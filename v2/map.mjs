// Map format v2: paper anchors (exact quote and occurrence), Lean anchors
// (declaration names, step positions or quoted Lean spans) and the kind of
// correspondence. Structural validation only; anchors are resolved in build.
import fs from 'node:fs';
import path from 'node:path';

export const SCHEMA = 'paper-lean-audit/map-2';
export const ENTRY_KINDS = ['formalizes', 'cites', 'lean-only', 'prose'];
export const SENTENCE_KINDS = ['formalizes', 'cites', 'lean-only', 'prose'];

export function loadMap(mapPath) {
  const map = JSON.parse(fs.readFileSync(mapPath, 'utf8'));
  map.__dir = path.dirname(path.resolve(mapPath));
  const errors = validateMap(map);
  if (errors.length) throw new Error('invalid map:\n' + errors.join('\n'));
  return map;
}

function checkQuote(where, anchor, errors) {
  if (!anchor || typeof anchor.quote !== 'string' || !anchor.quote.length) errors.push(`${where}: paper anchor needs a non-empty "quote"`);
  else if (anchor.occurrence !== undefined && !(Number.isInteger(anchor.occurrence) && anchor.occurrence >= 1)) errors.push(`${where}: "occurrence" must be a positive integer`);
}

export function checkStepAnchor(where, a, errors) {
  if (!a || typeof a !== 'object') { errors.push(`${where}: step anchor must be an object`); return; }
  const hasPos = Array.isArray(a.at) && a.at.length === 2 && a.at.every(Number.isInteger);
  const hasQuote = typeof a.quote === 'string' && a.quote.length > 0;
  // "decl" alone anchors the whole proof of that helper lemma.
  if (hasPos && hasQuote || !hasPos && !hasQuote && !a.decl) errors.push(`${where}: step anchor needs exactly one of "at": [line, column] or "quote", or only "decl"`);
  if (a.decl !== undefined && (typeof a.decl !== 'string' || !a.decl.length)) errors.push(`${where}: "decl" must be a declaration name`);
}

export function validateMap(map) {
  const errors = [];
  if (map.schema !== SCHEMA) errors.push(`schema must be "${SCHEMA}"`);
  if (!map.sources?.paper?.file) errors.push('sources.paper.file is required');
  if (!map.sources?.formal?.commit) errors.push('sources.formal.commit is required');
  if (!Array.isArray(map.entries)) errors.push('entries must be an array');
  const ids = new Set();
  for (const [i, e] of (map.entries ?? []).entries()) {
    const where = `entries[${i}]${e?.id ? ' (' + e.id + ')' : ''}`;
    if (!e.id || typeof e.id !== 'string') errors.push(`${where}: id is required`);
    else if (ids.has(e.id)) errors.push(`${where}: duplicate id`);
    ids.add(e.id);
    checkQuote(where, e.paper, errors);
    if (!ENTRY_KINDS.includes(e.kind)) errors.push(`${where}: kind must be one of ${ENTRY_KINDS.join(', ')}`);
    if (e.lean !== undefined && !(Array.isArray(e.lean) && e.lean.every((n) => typeof n === 'string'))) errors.push(`${where}: lean must be a list of declaration names`);
    if ((e.kind === 'formalizes' || e.kind === 'cites') && !(e.lean ?? []).length) errors.push(`${where}: kind ${e.kind} needs at least one Lean declaration`);
    if (e.kind === 'prose' && !e.note) errors.push(`${where}: kind prose needs a note`);
    if (e.proof) {
      if (e.kind === 'cites') errors.push(`${where}: a cited result has no printed proof to map`);
      if (e.proof.paper) checkQuote(`${where}.proof`, e.proof.paper, errors);
      if (e.proof.end) {
        if (!e.proof.paper) errors.push(`${where}.proof: "end" needs "paper", the start of the proof in the running text`);
        checkQuote(`${where}.proof.end`, e.proof.end, errors);
      }
      if (!Array.isArray(e.proof.sentences)) errors.push(`${where}.proof: sentences must be an array`);
      for (const [j, s] of (e.proof.sentences ?? []).entries()) {
        const sw = `${where}.proof.sentences[${j}]`;
        checkQuote(sw, s, errors);
        if (!SENTENCE_KINDS.includes(s.kind)) errors.push(`${sw}: kind must be one of ${SENTENCE_KINDS.join(', ')}`);
        if (s.kind === 'prose' && !s.note) errors.push(`${sw}: kind prose needs a note`);
        if (s.kind === 'formalizes' && !(s.steps ?? []).length) errors.push(`${sw}: kind formalizes needs at least one Lean step`);
        for (const [k, a] of (s.steps ?? []).entries()) checkStepAnchor(`${sw}.steps[${k}]`, a, errors);
      }
      for (const [j, a] of (e.proof.lean_adds ?? []).entries()) {
        checkStepAnchor(`${where}.proof.lean_adds[${j}]`, a.step, errors);
        if (!a.note) errors.push(`${where}.proof.lean_adds[${j}]: note is required`);
      }
    }
  }
  for (const [i, l] of (map.lean_only ?? []).entries()) {
    if (!!l.decl === !!l.prefix) errors.push(`lean_only[${i}]: give exactly one of "decl" or "prefix"`);
    if (!l.note) errors.push(`lean_only[${i}]: note is required`);
  }
  return errors;
}

// Declaration of the Lean proof that a proof entry follows.
export const proofDecl = (e) => e.proof?.lean ?? e.lean?.[0];

// Helper declarations whose proofs a proof entry follows step by step: a step
// anchor with "decl" names a lemma that the proof calls.
export function stepDecls(e) {
  const names = new Set();
  for (const s of e.proof?.sentences ?? []) for (const a of s.steps ?? []) if (a.decl) names.add(a.decl);
  for (const la of e.proof?.lean_adds ?? []) if (la.step?.decl) names.add(la.step.decl);
  names.delete(proofDecl(e));
  return [...names].sort();
}

// Declarations that are results of the map; uses are computed through every
// other project lemma, including the step declarations.
export function mapMapped(map) {
  const names = new Set();
  for (const e of map.entries) for (const n of e.lean ?? []) names.add(n);
  for (const l of map.lean_only ?? []) if (l.decl) names.add(l.decl);
  for (const e of map.entries) if (e.proof && proofDecl(e)) names.add(proofDecl(e));
  return [...names].sort();
}

export function mapDeclarations(map) {
  const names = new Set(mapMapped(map));
  for (const e of map.entries) if (e.proof) for (const n of stepDecls(e)) names.add(n);
  return [...names].sort();
}

export function mapTraces(map) {
  const names = new Set();
  for (const e of map.entries) if (e.proof && proofDecl(e)) { names.add(proofDecl(e)); for (const n of stepDecls(e)) names.add(n); }
  return [...names].sort();
}
