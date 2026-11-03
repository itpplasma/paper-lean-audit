#!/usr/bin/env node
// Side-by-side paper/Lean reader (map v2).
//
//   node v2/build.mjs --map MAP --out DIR [--paper FILE|REPO] [--extraction FILE]
//        [--previous REPORT] [--check] [--no-graph]
//
// Inputs: the paper source at a pinned commit (or a snapshot whose sha256 the
// map records), the extraction JSON written by v2/extract.mjs for the pinned
// Lean commit, and the map. Outputs DIR/<stem>.html and DIR/<stem>.report.json;
// equal inputs give byte-identical outputs. --check exits non-zero when a
// check fails.
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { TexRenderer } from '../texhtml.mjs';
import { highlightLean } from '../lean.mjs';
import { loadMap, proofDecl } from './map.mjs';
import { parsePaper, equationTags, resolveQuote, sentences, refsIn, lineAt } from './paper.mjs';
import { stableStringify, sha256, escapeHtml, slug } from './util.mjs';
import { buildGraphs } from './graph.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));

// Plain text of a TeX span for graph labels.
function texToPlain(s, refs) {
  return s.replace(/\\label\s*\{[^}]*\}/g, '').replace(/\\(?:begin|end)\s*\{[^}]*\}/g, ' ')
    .replace(/\\(?:ref|eqref)\s*\{([^}]*)\}/g, (_, l) => refs[l]?.text ?? l).replace(/~/g, ' ')
    .replace(/\\(?:emph|textit|textbf|mathrm|operatorname|text)\s*\{([^}]*)\}/g, '$1').replace(/\\([A-Za-z]+)/g, '$1')
    .replace(/[$\\{}]/g, '').replace(/\s+/g, ' ').trim();
}

const cmpPos = (a, b) => a[0] - b[0] || a[1] - b[1];
const shortName = (n) => n.split('.').slice(-1)[0];

function readPaper(map, paperArg) {
  const src = map.sources.paper;
  if (src.snapshot) {
    const file = path.resolve(map.__dir, src.snapshot);
    const raw = fs.readFileSync(file, 'utf8');
    if (src.sha256 && sha256(raw) !== src.sha256) throw new Error(`paper snapshot ${src.snapshot} does not match sources.paper.sha256`);
    return raw;
  }
  if (!paperArg) throw new Error('--paper REPO is required unless sources.paper.snapshot is given');
  const p = path.resolve(paperArg);
  if (fs.statSync(p).isFile()) {
    const raw = fs.readFileSync(p, 'utf8');
    if (src.sha256 && sha256(raw) !== src.sha256) throw new Error('paper file does not match sources.paper.sha256');
    return raw;
  }
  return execFileSync('git', ['-C', p, 'show', `${src.commit}:${src.file}`], { encoding: 'utf8', maxBuffer: 64 << 20 });
}

function bibCites(bib) {
  const cites = {};
  for (const m of (bib ?? '').matchAll(/@\w+\{([^,]+),[\s\S]*?\n\}/g)) {
    const entry = m[0];
    const author = /author\s*=\s*[{"]([^}"]+)/i.exec(entry)?.[1] ?? m[1];
    const year = /year\s*=\s*[{"]?(\d{4})/i.exec(entry)?.[1] ?? '';
    const surname = author.split(/\s+and\s+/)[0].split(',')[0].trim().split(/\s+/).pop().replace(/[{}\\'"`^]/g, '');
    cites[m[1].trim()] = `${surname}${year ? ' ' + year : ''}`;
  }
  return cites;
}

// Absolute [line, column] (column in code points) of offset k in a declaration
// source that starts at `start`.
function sourcePos(source, start, k) {
  const before = source.slice(0, k);
  const lines = before.split('\n');
  if (lines.length === 1) return [start[0], start[1] + Array.from(before).length];
  return [start[0] + lines.length - 1, Array.from(lines.at(-1)).length];
}

export function build({ mapPath, paperArg = null, extractionPath = null, previous = null, graph = true, bib = null }) {
  const map = loadMap(mapPath);
  const errors = [], warnings = [];
  const raw = readPaper(map, paperArg);
  if (bib === null && map.sources.paper.bib_snapshot) bib = fs.readFileSync(path.resolve(map.__dir, map.sources.paper.bib_snapshot), 'utf8');
  const doc = parsePaper(raw);
  const exPath = path.resolve(map.__dir, extractionPath ?? map.lean?.extraction ?? 'extraction.json');
  const ex = JSON.parse(fs.readFileSync(exPath, 'utf8'));
  const settings = { large_step: 5, ...(map.settings ?? {}) };
  // Environments whose citation is a use of a result (not of a definition).
  const resultEnvs = new Set(settings.result_environments ?? ['theorem', 'lemma', 'proposition', 'corollary']);
  const isResult = (card) => !!card?.env && resultEnvs.has(card.env.name);
  if (ex.environment?.commit && ex.environment.commit !== map.sources.formal.commit) {
    errors.push(`extraction is for Lean commit ${ex.environment.commit}, map pins ${map.sources.formal.commit}`);
  }
  if (ex.environment?.dirty) errors.push('extraction was made from a Lean checkout with uncommitted changes');

  // ------------------------------------------------------------ scope ----
  const topSections = doc.sections.filter((s) => s.level === 0);
  let scopeRanges = [[doc.docStart, doc.docEnd]];
  if (map.scope?.sections) {
    scopeRanges = map.scope.sections.map((num) => {
      const i = topSections.findIndex((s) => s.number === String(num));
      if (i < 0) { errors.push(`scope: section ${num} not found`); return null; }
      return [topSections[i].start, topSections[i + 1]?.start ?? doc.docEnd];
    }).filter(Boolean);
  }
  const inScope = (off) => scopeRanges.some(([a, b]) => off >= a && off < b);

  // --------------------------------------------------- resolve entries ----
  const entryByDecl = new Map();
  for (const e of map.entries) for (const n of e.lean ?? []) if (!entryByDecl.has(n)) entryByDecl.set(n, e);
  const labelEntry = new Map();
  const cards = [];
  for (const e of map.entries) {
    const r = resolveQuote(raw, e.paper, 0, raw.length, doc.text);
    const card = { id: e.id, entry: e, anchor: null, env: null, passage: null, decls: [], errors: [] };
    if (r.error) { errors.push(`${e.id}: paper ${r.error}: ${JSON.stringify(e.paper.quote)}`); continue; }
    card.anchor = { start: r.start, end: r.end, line: lineAt(raw, r.start) };
    const env = doc.envs.filter((x) => x.start <= r.start && r.end <= x.end).sort((a, b) => b.start - a.start)[0];
    if (env) card.env = env;
    else {
      // A passage outside environments: the paragraph that contains the quote.
      let a = raw.lastIndexOf('\n\n', r.start), b = raw.indexOf('\n\n', r.end);
      a = a < 0 ? doc.docStart : a + 2; b = b < 0 ? doc.docEnd : b;
      const inner = doc.envs.find((x) => x.start >= a && x.start < b);
      if (inner) b = Math.min(b, inner.start);
      const prev = [...doc.envs].reverse().find((x) => x.end > a && x.end <= r.start);
      if (prev) a = Math.max(a, prev.end);
      card.passage = { start: a, end: b };
    }
    card.start = card.env?.start ?? card.passage.start;
    card.end = card.env?.end ?? card.passage.end;
    for (const n of e.lean ?? []) {
      const d = ex.declarations[n];
      if (!d) errors.push(`${e.id}: Lean declaration ${n} not found in the extraction`);
      else card.decls.push({ name: n, d });
    }
    if (card.env) for (const l of card.env.labels) labelEntry.set(l, card);
    cards.push(card);
  }
  // One card per environment.
  const byEnv = new Map();
  for (const c of cards) if (c.env) {
    if (byEnv.has(c.env)) errors.push(`${c.id}: environment already mapped by ${byEnv.get(c.env).id}`);
    else byEnv.set(c.env, c);
  }
  for (const env of doc.envs) {
    if (!inScope(env.start)) continue;
    if (!byEnv.has(env)) errors.push(`paper ${env.title} ${env.number ?? ''} (line ${lineAt(raw, env.start)}) has no map entry`);
  }
  cards.sort((a, b) => a.start - b.start);

  // ------------------------------------------------------- proofs ----
  const proofOwner = new Map();
  for (const c of cards) {
    if (c.entry.proof?.end) {
      // A printed proof in the running text, from the start quote to the end quote.
      const a = resolveQuote(raw, c.entry.proof.paper, 0, raw.length, doc.text);
      const b = a.error ? null : resolveQuote(raw, c.entry.proof.end, a.start, raw.length, doc.text);
      if (a.error) { errors.push(`${c.id}: proof anchor ${a.error}`); continue; }
      if (b.error) { errors.push(`${c.id}: proof end anchor ${b.error} after the start`); continue; }
      const pf = { start: a.start, end: b.end, bodyStart: a.start, bodyEnd: b.end, text: true };
      if (doc.envs.some((x) => x.start < pf.end && pf.start < x.end) || doc.proofs.some((x) => x.start < pf.end && pf.start < x.end)) {
        errors.push(`${c.id}: the running-text proof overlaps an environment`); continue;
      }
      if (c.env) {
        if (doc.text.slice(c.env.end, pf.start).trim()) { errors.push(`${c.id}: text between the statement and its running-text proof`); continue; }
        c.end = Math.max(c.end, pf.end);
      } else {
        c.passage = { start: pf.start, end: pf.start };
        c.start = pf.start; c.end = pf.end;
      }
      c.proofEnv = pf;
      continue;
    }
    if (!c.env) continue;
    let pf = null;
    if (c.entry.proof?.paper) {
      const r = resolveQuote(raw, c.entry.proof.paper, 0, raw.length, doc.text);
      if (r.error) errors.push(`${c.id}: proof anchor ${r.error}`);
      else pf = doc.proofs.find((p) => p.start <= r.start && r.end <= p.end) ?? null;
      if (!r.error && !pf) errors.push(`${c.id}: proof anchor is not inside a proof environment`);
    } else {
      const next = doc.proofs.find((p) => p.start >= c.env.end);
      if (next) {
        const gap = doc.text.slice(c.env.end, next.start).replace(/\\AI(?:add|comment)\s*\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\}(?:\s*\{(?:[^{}]|\{(?:[^{}]|\{[^{}]*\})*\})*\})?/g, '');
        if (!gap.trim()) pf = next;
      }
    }
    if (pf) {
      if (proofOwner.has(pf)) errors.push(`${c.id}: proof already attached to ${proofOwner.get(pf).id}`);
      proofOwner.set(pf, c);
      c.proofEnv = pf;
      c.end = Math.max(c.end, pf.end);
      if (!c.entry.proof) {
        if (c.entry.kind === 'cites') errors.push(`${c.id}: kind cites, but the paper prints a proof (line ${lineAt(raw, pf.start)})`);
        else if (inScope(c.start)) errors.push(`${c.id}: the printed proof (line ${lineAt(raw, pf.start)}) has no sentence map`);
      }
    } else if (c.entry.proof) errors.push(`${c.id}: map has a proof, but no printed proof follows the statement; give proof.paper`);
  }
  for (const p of doc.proofs) if (inScope(p.start) && !proofOwner.has(p)) errors.push(`paper proof at line ${lineAt(raw, p.start)} belongs to no mapped statement`);

  // ------------------------------------------------- refs and render ----
  const { eqAuto, labels: eqLabels } = equationTags(doc);
  const refs = {};
  for (const s of doc.sections) for (const l of s.labels) refs[l] = { text: s.number ?? '' };
  for (const [l, t] of Object.entries(eqLabels)) refs[l] = { text: t };
  for (const env of doc.envs) for (const l of env.labels) if (!eqLabels[l]) refs[l] = { text: env.number ?? '' };
  for (const c of cards) {
    if (c.env) for (const l of c.env.labels) if (!eqLabels[l]) refs[l] = { text: c.env.number ?? '', href: `#c-${slug(c.id)}` };
  }
  for (const [l, info] of doc.labels) if (refs[l] && !refs[l].href) {
    const owner = cards.find((c) => info.at >= c.start && info.at < c.end);
    if (owner) refs[l].href = `#c-${slug(owner.id)}`;
  }
  const macros = { ...(map.macros ?? {}) };
  for (const m of doc.text.matchAll(/\\newcommand\s*\{(\\[A-Za-z]+)\}\s*\{((?:[^{}]|\{[^{}]*\})*)\}/g)) if (!m[2].includes('#')) macros[m[1]] = m[2];
  for (const m of doc.text.matchAll(/\\DeclareMathOperator\s*\{(\\[A-Za-z]+)\}\s*\{([^}]*)\}/g)) macros[m[1]] = `\\operatorname{${m[2]}}`;
  const tex = new TexRenderer({ macros, refs, cites: bibCites(bib), eqAuto });
  const renderTex = (a, b) => tex.block(doc.text.slice(a, b), a);
  const envHead = (env) => `<span class="env-head">${escapeHtml(env.title)}${env.number ? ' ' + escapeHtml(env.number) : ''}${env.optArg ? ' (' + tex.text(env.optArg, env.optStart) + ')' : ''}.</span>`;
  const cardTitle = (c) => c.env ? `${c.env.title}${c.env.number ? ' ' + c.env.number : ''}` : (c.entry.title ?? `Paragraph${c.entry.short ? ': ' + c.entry.short : ''}`);

  // ------------------------------------------------- Lean classification ----
  const leanOnly = (name) => (map.lean_only ?? []).find((l) => l.decl === name || (l.prefix && name.startsWith(l.prefix)));
  const counterpart = (name) => {
    const c = cards.find((x) => x.decls.some((d) => d.name === name));
    return c ?? null;
  };
  const ctxInfo = (name) => ex.context[name] ?? ex.declarations[name];
  const knownNames = new Set([...Object.keys(ex.context ?? {}), ...Object.keys(ex.declarations ?? {})]);
  const suffixIndex = new Map();
  for (const n of knownNames) {
    const parts = n.split('.');
    for (let i = 0; i < parts.length; i++) {
      const k = parts.slice(i).join('.');
      if (!suffixIndex.has(k)) suffixIndex.set(k, new Set());
      suffixIndex.get(k).add(n);
    }
  }
  const declAnchor = (n) => `d-${slug(n)}`;
  const linkFor = (ident) => {
    const s = suffixIndex.get(ident);
    if (!s || s.size !== 1) return null;
    return '#' + declAnchor([...s][0]);
  };
  const leanHtml = (src) => `<pre class="lean"><code>${highlightLean(src, linkFor)}</code></pre>`;

  // ------------------------------------------------------- cards ----
  const shown = new Map(); // Lean name -> card id where its definition is shown
  const envId = { toolchain: ex.environment?.toolchain ?? null, lean_githash: ex.environment?.lean_githash ?? null, manifest_sha256: ex.environment?.manifest_sha256 ?? null };
  const report = { schema: 'paper-lean-audit/report-2', anchors: {}, cards: [], errors, warnings };
  const routeKinds = new Set(['formalizes', 'cites']);

  const defBlock = (name, role, note = null) => {
    const info = ctxInfo(name);
    const cp = role;
    const badge = cp.kind === 'paper' ? `<span class="badge formalizes">formalizes <a href="#c-${slug(cp.card.id)}">${escapeHtml(cardTitle(cp.card))}</a></span>`
      : cp.kind === 'lean-only' ? '<span class="badge lean-only">Lean only</span>'
        : cp.kind === 'instance' ? '<span class="badge instance">instance</span>'
          : '<span class="badge missing">no paper counterpart</span>';
    const src = info?.source ?? info?.signature ?? name;
    return `<div class="def" id="${declAnchor(name)}" data-name="${escapeHtml(name)}"><div class="def-head"><code class="fqn">${escapeHtml(name)}</code> ${badge}` +
      `<span class="loc">${escapeHtml(info?.file ?? '')}${info?.range ? ':' + info.range.start[0] : ''}</span></div>` +
      (note ? `<p class="note">${escapeHtml(note)}</p>` : '') + leanHtml(src) + '</div>';
  };
  const backref = (name) => `<a class="backref" href="#${declAnchor(name)}" data-preview="${declAnchor(name)}"><code>${escapeHtml(shortName(name))}</code></a>`;

  // Breadth-first order from the statement through direct dependencies.
  const contextOrder = (d) => {
    const all = new Set(d.context ?? []);
    const out = [], seen = new Set();
    let frontier = (d.deps ?? []).filter((n) => all.has(n));
    while (frontier.length) {
      const next = [];
      for (const n of frontier) {
        if (seen.has(n)) continue;
        seen.add(n); out.push(n);
        for (const m of ctxInfo(n)?.deps ?? []) if (all.has(m) && !seen.has(m)) next.push(m);
      }
      frontier = next;
    }
    for (const n of [...all].sort()) if (!seen.has(n)) out.push(n);
    return out;
  };

  const renderGoalChange = (before, after) => {
    const b0 = before[0], a0 = after[0];
    const parts = [];
    if (b0 && a0) {
      const key = (h) => h.name + '\0' + h.type;
      const old = new Set(b0.hyps.map(key));
      const now = new Set(a0.hyps.map(key));
      const added = a0.hyps.filter((h) => !old.has(key(h)));
      const removed = b0.hyps.filter((h) => !now.has(key(h)) && !a0.hyps.some((x) => x.name === h.name));
      for (const h of added) parts.push(`<div class="hyp new"><span class="hn">${escapeHtml(h.name)}</span> : <code>${escapeHtml(h.type)}</code></div>`);
      if (removed.length) parts.push(`<div class="hyp gone">cleared: ${removed.map((h) => `<code>${escapeHtml(h.name)}</code>`).join(', ')}</div>`);
      if (a0.target !== b0.target || !added.length) parts.push(`<div class="goal">⊢ <code>${escapeHtml(a0.target)}</code></div>`);
    } else if (b0 && after.length < before.length) parts.push('<div class="goal closed">goal closed</div>');
    if (after.length > 1) parts.push(`<div class="more-goals">${after.length - 1} further goal${after.length > 2 ? 's' : ''}: ${after.slice(1).map((g) => `<code>${escapeHtml(g.target)}</code>`).join('; ')}</div>`);
    return parts.join('');
  };
  const cardLink = (n) => { const e = entryByDecl.get(n); const cc = cards.find((x) => x.id === e.id); return `<a href="#c-${slug(e.id)}">${escapeHtml(cc ? cardTitle(cc) : e.id)}</a>`; };
  const usesHtml = (steps, via = {}) => {
    const proj = [...new Set(steps.flatMap((s) => s.uses_project))].sort();
    const lib = [...new Set(steps.flatMap((s) => s.uses_library))].sort();
    let h = '';
    const one = (n) => entryByDecl.has(n) ? `${cardLink(n)} <code class="small">${escapeHtml(shortName(n))}</code>`
      : `<code title="${escapeHtml(n)}">${escapeHtml(shortName(n))}</code>` + ((via[n] ?? []).length ? ` (through it: ${via[n].filter((m) => entryByDecl.has(m)).map(cardLink).join(', ')})` : '');
    if (proj.length) h += `<div class="uses">uses ${proj.map(one).join(', ')}</div>`;
    if (lib.length) h += `<details class="uses-lib"><summary>${lib.length} library result${lib.length > 1 ? 's' : ''}</summary>${lib.map((n) => `<code>${escapeHtml(n)}</code>`).join(' ')}</details>`;
    return h;
  };
  const tacticHtml = (steps) => `<details class="tactic"><summary>tactic</summary>${leanHtml(steps.map((s) => s.text).join('\n'))}</details>`;

  const htmlCards = [];
  for (const c of cards) {
    if (!inScope(c.start)) continue;
    const e = c.entry;
    const flags = [];
    let right = '';
    for (const { name, d } of c.decls) {
      shown.set(name, c.id);
      const unused = (d.unused ?? []).filter((u) => u.prop || u.binder === 'instance' || !u.in_statement);
      if (unused.length) flags.push('unused hypotheses');
      right += `<div class="stmt" id="${declAnchor(name)}" data-name="${escapeHtml(name)}"><div class="def-head"><code class="fqn">${escapeHtml(name)}</code> <span class="kind">${escapeHtml(d.kind)}</span>` +
        `<span class="loc">${escapeHtml(d.file ?? '')}${d.range ? ':' + d.range.start[0] : ''}</span></div>` +
        leanHtml(d.kind === 'theorem' ? d.signature : (d.source ?? d.signature)) +
        (unused.length ? `<div class="flag unused">unused by the proof: ${unused.map((u) => `<code>${escapeHtml(u.name)} : ${escapeHtml(u.type)}</code>`).join(', ')}</div>` : '') +
        (d.unfolded ? `<details class="unfold"><summary>unfolded to the library boundary</summary>${leanHtml(d.unfolded)}</details>` : '') +
        (d.kind === 'theorem' && d.source ? `<details class="source"><summary>Lean source</summary>${leanHtml(d.source)}</details>` : '') + '</div>';
    }
    // Statement context, each definition once.
    const fresh = [], again = [], instances = [], groups = new Map();
    for (const { name, d } of c.decls) {
      for (const n of contextOrder(d)) {
        if (c.decls.some((x) => x.name === n)) continue;
        if (shown.has(n)) { if (shown.get(n) !== c.id && !again.includes(n)) again.push(n); continue; }
        const info = ctxInfo(n);
        if (info?.instance || info?.kind === 'instance') { if (!instances.includes(n)) instances.push(n); shown.set(n, c.id); continue; }
        const cp = counterpart(n);
        const lo = leanOnly(n);
        if (cp && cp.id !== c.id) { fresh.push({ n, role: { kind: 'paper', card: cp } }); shown.set(n, c.id); continue; }
        if (lo) {
          const key = lo.decl ?? lo.prefix;
          if (!groups.has(key)) groups.set(key, { lo, names: [] });
          groups.get(key).names.push(n); shown.set(n, c.id);
          continue;
        }
        fresh.push({ n, role: { kind: 'missing' } }); shown.set(n, c.id);
        if (routeKinds.has(e.kind)) errors.push(`${c.id}: statement context of ${name} contains ${n}, which has neither a paper counterpart nor a lean_only entry`);
      }
    }
    if (fresh.length || groups.size) {
      right += '<div class="context"><div class="ctx-head">Definitions used by the statement</div>';
      for (const f of fresh) right += defBlock(f.n, f.role);
      for (const [, g] of groups) {
        flags.push('Lean-only definitions');
        const body = g.names.map((n) => defBlock(n, { kind: 'lean-only' })).join('');
        right += g.names.length > 2
          ? `<details class="lean-only-group"><summary><span class="badge lean-only">Lean only</span> ${g.names.length} definitions${g.lo.prefix ? ' under <code>' + escapeHtml(g.lo.prefix) + '</code>' : ''}: ${escapeHtml(g.lo.note)}</summary>${body}</details>`
          : `<p class="note"><span class="badge lean-only">Lean only</span> ${escapeHtml(g.lo.note)}</p>${body}`;
      }
      right += '</div>';
    }
    if (again.length) right += `<div class="again">Already shown: ${again.map(backref).join(' ')}</div>`;
    if (instances.length) right += `<details class="instances"><summary>${instances.length} instance${instances.length > 1 ? 's' : ''} used by the statement</summary>${instances.map((n) => defBlock(n, { kind: 'instance' })).join('')}</details>`;

    // Paper side.
    let left;
    if (c.env) left = `<div class="env env-${escapeHtml(c.env.name)}">${envHead(c.env)} ${renderTex(c.env.bodyStart, c.env.bodyEnd)}</div>`;
    else if (c.proofEnv?.text && c.passage.start === c.passage.end) left = '<p class="muted">The proof is printed as running text; its sentences follow below.</p>';
    else left = renderTex(c.passage.start, c.passage.end);

    // Proof rows.
    let proofHtml = '', account = null;
    if (c.proofEnv && e.proof) {
      const pf = c.proofEnv;
      const decl = proofDecl(e);
      const trace = ex.traces?.[decl]?.steps;
      const dsrc = ex.declarations[decl];
      if (!trace) errors.push(`${c.id}: no proof-state trace for ${decl}`);
      const steps = trace ?? [];
      const children = new Map();
      for (const s of steps) if (s.parent !== null) { if (!children.has(s.parent)) children.set(s.parent, []); children.get(s.parent).push(s.index); }
      const descendants = (i) => { const out = []; const st = [...(children.get(i) ?? [])]; while (st.length) { const j = st.pop(); out.push(j); st.push(...(children.get(j) ?? [])); } return out; };
      const resolveStep = (a, where) => {
        if (a.decl && a.decl !== decl) return resolveOther(a, where);
        if (!dsrc?.source) { errors.push(`${where}: no source for ${decl}`); return null; }
        let pos, endPos = null;
        if (a.at) pos = a.at;
        else {
          const hits = [];
          for (let i = dsrc.source.indexOf(a.quote); i >= 0; i = dsrc.source.indexOf(a.quote, i + 1)) hits.push(i);
          if (!hits.length) { errors.push(`${where}: Lean quote not found in ${decl}: ${JSON.stringify(a.quote)}`); return null; }
          if (a.occurrence === undefined && hits.length > 1) { errors.push(`${where}: Lean quote occurs ${hits.length} times in ${decl}; give "occurrence"`); return null; }
          const k = hits[(a.occurrence ?? 1) - 1];
          if (k === undefined) { errors.push(`${where}: Lean quote occurrence ${a.occurrence} not found`); return null; }
          pos = sourcePos(dsrc.source, dsrc.range.start, k);
          endPos = sourcePos(dsrc.source, dsrc.range.start, k + a.quote.length);
        }
        let s = steps.find((x) => cmpPos(x.range.start, pos) === 0);
        if (!s && endPos) {
          const containing = steps.filter((x) => cmpPos(x.range.start, pos) <= 0 && cmpPos(endPos, x.range.end) <= 0);
          s = containing.sort((x, y) => y.depth - x.depth)[0];
        }
        if (!s) { errors.push(`${where}: no tactic step of ${decl} at ${JSON.stringify(a.at ?? a.quote)}`); return null; }
        return s;
      };
      // A step of another (helper) declaration, or that declaration as a whole.
      const resolveOther = (a, where) => {
        const od = ex.declarations[a.decl];
        if (!od) { errors.push(`${where}: Lean declaration ${a.decl} not found in the extraction`); return null; }
        const otrace = ex.traces?.[a.decl]?.steps ?? [];
        const ochildren = new Map();
        for (const s of otrace) if (s.parent !== null) { if (!ochildren.has(s.parent)) ochildren.set(s.parent, []); ochildren.get(s.parent).push(s.index); }
        const odesc = (i) => { const out = []; const st = [...(ochildren.get(i) ?? [])]; while (st.length) { const j = st.pop(); out.push(j); st.push(...(ochildren.get(j) ?? [])); } return out; };
        if (!a.at && !a.quote) return { other: a.decl, whole: true, d: od, size: Math.max(1, otrace.length), index: null };
        let pos, endPos = null;
        if (a.at) pos = a.at;
        else {
          const hits = [];
          for (let i = (od.source ?? '').indexOf(a.quote); i >= 0; i = od.source.indexOf(a.quote, i + 1)) hits.push(i);
          if (!hits.length) { errors.push(`${where}: Lean quote not found in ${a.decl}: ${JSON.stringify(a.quote)}`); return null; }
          if (a.occurrence === undefined && hits.length > 1) { errors.push(`${where}: Lean quote occurs ${hits.length} times in ${a.decl}; give "occurrence"`); return null; }
          const k = hits[(a.occurrence ?? 1) - 1];
          if (k === undefined) { errors.push(`${where}: Lean quote occurrence ${a.occurrence} not found`); return null; }
          pos = sourcePos(od.source, od.range.start, k);
          endPos = sourcePos(od.source, od.range.start, k + a.quote.length);
        }
        let s = otrace.find((x) => cmpPos(x.range.start, pos) === 0);
        if (!s && endPos) s = otrace.filter((x) => cmpPos(x.range.start, pos) <= 0 && cmpPos(endPos, x.range.end) <= 0).sort((x, y) => y.depth - x.depth)[0];
        if (!s) { errors.push(`${where}: no tactic step of ${a.decl} at ${JSON.stringify(a.at ?? a.quote)}`); return null; }
        return { ...s, other: a.decl, whole: false, size: 1 + odesc(s.index).length, index: null, otherIndex: s.index };
      };
      const sents = sentences(doc.text, pf.bodyStart, pf.bodyEnd);
      const mapped = [];
      for (const [j, s] of (e.proof.sentences ?? []).entries()) {
        const where = `${c.id}.proof.sentences[${j}]`;
        const r = resolveQuote(raw, s, pf.bodyStart, pf.bodyEnd, doc.text);
        if (r.error) { errors.push(`${where}: paper ${r.error}: ${JSON.stringify(s.quote)}`); continue; }
        const resolved = (s.steps ?? []).map((a, k) => resolveStep(a, `${where}.steps[${k}]`)).filter(Boolean);
        mapped.push({ s, r, steps: resolved, sentence: sents.find((x) => x.start <= r.start && r.start < x.end) ?? null });
        report.anchors[where] = { paper: { start: r.start, line: lineAt(raw, r.start) }, steps: resolved.map((x) => x.other
          ? { decl: x.other, ...(x.whole ? { range: x.d.range ?? null, type: x.d.type_hash ?? null } : { index: x.otherIndex, start: x.range.start }) }
          : { index: x.index, start: x.range.start }) };
      }
      for (const sn of sents) {
        if (!mapped.some((m) => m.sentence === sn)) errors.push(`${c.id}: proof sentence at line ${lineAt(raw, sn.start)} has no map entry: ${JSON.stringify(raw.slice(sn.start, Math.min(sn.end, sn.start + 90)))}`);
      }
      const claimed = new Set();
      for (const m of mapped) for (const s of m.steps) if (!s.other) { claimed.add(s.index); for (const d of descendants(s.index)) claimed.add(d); }
      const hasClaimedDesc = (i) => descendants(i).some((d) => claimed.has(d));
      const adds = steps.filter((s) => !claimed.has(s.index) && !hasClaimedDesc(s.index) && (s.parent === null || hasClaimedDesc(s.parent)));
      const addNotes = new Map();
      for (const [j, la] of (e.proof.lean_adds ?? []).entries()) {
        const s = resolveStep(la.step, `${c.id}.proof.lean_adds[${j}]`);
        if (!s) continue;
        if (s.other) { errors.push(`${c.id}.proof.lean_adds[${j}]: a Lean-added step must be a step of ${decl}`); continue; }
        if (!adds.includes(s)) errors.push(`${c.id}.proof.lean_adds[${j}]: step ${s.index} is not a Lean-added step`);
        addNotes.set(s.index, la.note);
      }
      // Group sentences by paper sentence, in paper order.
      const groupsBySentence = [];
      for (const m of [...mapped].sort((a, b) => a.r.start - b.r.start)) {
        const g = groupsBySentence.find((x) => x.sentence && x.sentence === m.sentence);
        if (g) g.items.push(m); else groupsBySentence.push({ sentence: m.sentence, items: [m] });
      }
      const proofRows = [];
      const rowId = () => `r-${slug(c.id)}-${proofRows.length}`;
      // A step's mapped results, directly or through unmapped helper lemmas.
      const via = ex.declarations[decl]?.uses?.via ?? {};
      const stepMapped = (ss) => [...new Set(ss.flatMap((x) => x.whole ? (x.d.uses?.mapped ?? [])
        : x.uses_project.flatMap((n) => entryByDecl.has(n) ? [n] : ((x.other ? ex.declarations[x.other]?.uses?.via : via)?.[n] ?? []))))];
      const usesCards = (ss) => [...new Set(stepMapped(ss).map((n) => entryByDecl.get(n)?.id).filter((x) => x && x !== c.id))].sort();
      const addRow = (s) => {
        const note = addNotes.get(s.index);
        const id = rowId();
        proofRows.push({ kind: 'lean-adds', label: 'Lean adds: ' + s.text.split('\n')[0].slice(0, 60), refs: [], uses: usesCards([s]), anchor: id });
        return `<div class="row lean-adds" id="${id}"><div class="paper-col"><span class="badge lean-adds">Lean adds</span>${note ? ` <span class="note">${escapeHtml(note)}</span>` : ''}</div>` +
          `<div class="lean-col">${renderGoalChange(s.goals_before, s.goals_after)}${usesHtml([s], via)}${tacticHtml([s])}</div></div>`;
      };
      // A helper declaration as a whole: its statement, uses and source; a step
      // inside it: its state change.
      const otherHtml = (s) => {
        const od = ex.declarations[s.other];
        const head = `<div class="def-head in-decl">${s.whole ? '' : 'step of '}<code class="fqn">${escapeHtml(s.other)}</code> <span class="kind">${escapeHtml(od.kind)}</span>` +
          `<span class="loc">${escapeHtml(od.file ?? '')}${od.range ? ':' + od.range.start[0] : ''}</span></div>`;
        if (s.whole) {
          const lib = [...(od.uses?.library ?? [])].sort();
          // Mapped results in the line; the (transitive) unmapped helpers folded away.
          const helpers = [...(od.uses?.helpers ?? [])].sort();
          const fake = [{ uses_project: [...(od.uses?.mapped ?? [])], uses_library: lib }];
          const id = shown.has(s.other) ? '' : ` id="${declAnchor(s.other)}"`;
          shown.set(s.other, c.id);
          return `<div class="helper"${id}>${head}${leanHtml(od.kind === 'theorem' ? od.signature : (od.source ?? od.signature))}${usesHtml(fake, {})}` +
            (helpers.length ? `<details class="uses-lib"><summary>${helpers.length} project lemma${helpers.length > 1 ? 's' : ''} without a card</summary>${helpers.map((n) => `<code>${escapeHtml(n)}</code>`).join(' ')}</details>` : '') +
            (od.kind === 'theorem' && od.source ? `<details class="tactic"><summary>Lean source</summary>${leanHtml(od.source)}</details>` : '') + '</div>';
        }
        return `<div class="helper">${head}${renderGoalChange(s.goals_before, s.goals_after)}${usesHtml([s], od.uses?.via ?? {})}${tacticHtml([s])}</div>`;
      };
      let rows = '';
      const placed = new Set();
      let large = 0, prose = 0, matched = 0;
      for (const [gi, g] of groupsBySentence.entries()) {
        const upto = Math.min(...g.items.flatMap((m) => m.steps.filter((s) => !s.other).map((s) => s.index)), Infinity);
        for (const s of adds) if (!placed.has(s.index) && s.index < upto) { rows += addRow(s); placed.add(s.index); }
        const span = g.sentence ?? { start: g.items[0].r.start, end: g.items[0].r.end };
        let leanCol = '';
        for (const m of g.items) {
          if (m.s.kind === 'prose') { prose++; leanCol += `<div class="prose"><span class="badge prose">prose</span> ${escapeHtml(m.s.note)}</div>`; continue; }
          matched++;
          const top = m.steps.filter((s) => !s.other).sort((a, b) => a.index - b.index);
          const others = m.steps.filter((s) => s.other);
          const count = new Set(top.flatMap((s) => [s.index, ...descendants(s.index)])).size + others.reduce((n, s) => n + s.size, 0);
          const isLarge = count > settings.large_step;
          if (isLarge) large++;
          const first = top[0], last = top.at(-1);
          leanCol += `<div class="state ${escapeHtml(m.s.kind)}">` + (m.s.kind !== 'formalizes' ? `<span class="badge ${escapeHtml(m.s.kind)}">${escapeHtml(m.s.kind)}</span> ` : '') +
            (isLarge ? `<span class="badge large">large step: ${count} Lean steps</span>` : '') +
            (m.s.note ? `<p class="note">${escapeHtml(m.s.note)}</p>` : '') +
            (first ? renderGoalChange(first.goals_before, last.goals_after) + usesHtml(top, via) + tacticHtml(top) : '') +
            others.map(otherHtml).join('') + '</div>';
        }
        const id = rowId();
        const refsHere = [...new Set(refsIn(doc.text, span.start, span.end).map((r) => labelEntry.get(r.label)?.id).filter(Boolean))].sort();
        const kinds = g.items.map((m) => m.s.kind);
        proofRows.push({ kind: kinds.every((k) => k === 'prose') ? 'prose' : 'formalizes', label: texToPlain(raw.slice(span.start, span.end), refs).slice(0, 90),
          refs: refsHere, uses: usesCards(g.items.flatMap((m) => m.steps)), anchor: id });
        rows += `<div class="row" id="${id}"><div class="paper-col">${renderTex(span.start, span.end)}</div><div class="lean-col">${leanCol}</div></div>`;
      }
      for (const s of adds) if (!placed.has(s.index)) { rows += addRow(s); placed.add(s.index); }
      // Citations against Lean uses.
      const cited = new Map();
      for (const r of refsIn(doc.text, pf.bodyStart, pf.bodyEnd)) {
        const owner = labelEntry.get(r.label);
        if (owner && owner !== c && isResult(owner)) cited.set(owner.id, owner);
      }
      const used = new Map();
      for (const n of ex.declarations[decl]?.uses?.mapped ?? []) {
        const owner = entryByDecl.get(n);
        if (owner && owner.id !== e.id) { const oc = cards.find((x) => x.id === owner.id); if (oc) used.set(owner.id, oc); }
      }
      const onlyPaper = [...cited.keys()].filter((k) => !used.has(k)).sort();
      const onlyLean = [...used.keys()].filter((k) => !cited.has(k)).sort();
      const notes = e.citations ?? {};
      for (const k of [...onlyPaper, ...onlyLean]) if (!notes[k]) errors.push(`${c.id}: ${onlyPaper.includes(k) ? 'the paper cites' : 'the Lean proof uses'} ${k} but ${onlyPaper.includes(k) ? 'the Lean proof does not use it' : 'the paper does not cite it'}; record the difference in citations`);
      const both = [...cited.keys()].filter((k) => used.has(k)).sort();
      account = { sentences: sents.length, matched, prose, lean_adds: adds.length, large, cited: [...cited.keys()].sort(), used: [...used.keys()].sort(), only_paper: onlyPaper, only_lean: onlyLean };
      const link = (k) => { const x = cards.find((y) => y.id === k); return `<a href="#c-${slug(k)}">${escapeHtml(x ? cardTitle(x) : k)}</a>`; };
      const diff = (k) => `${link(k)}${notes[k] ? ` <span class="note">${escapeHtml(notes[k])}</span>` : ' <span class="badge missing">unexplained</span>'}`;
      proofHtml = `<div class="proof"><div class="proof-head"><span class="env-head">Proof.</span> Lean: <code>${escapeHtml(decl)}</code></div>${rows}` +
        `<div class="account"><b>Account.</b> ${sents.length} sentences: ${matched} matched, ${prose} prose; ${adds.length} Lean-added step${adds.length === 1 ? '' : 's'}; ${large} large step${large === 1 ? '' : 's'}.` +
        ` Cited and used: ${both.length ? both.map(link).join(', ') : 'none'}.` +
        (onlyPaper.length ? ` <span class="one-sided">Cited, not used by Lean: ${onlyPaper.map(diff).join('; ')}.</span>` : '') +
        (onlyLean.length ? ` <span class="one-sided">Used by Lean, not cited: ${onlyLean.map(diff).join('; ')}.</span>` : '') + '</div></div>';
      c.proofRows = proofRows;
      if (adds.length) flags.push('Lean adds');
      if (large) flags.push('large step');
      if (prose) flags.push('prose');
    } else if (c.decls.some((x) => x.d.kind === 'theorem')) {
      const usedCards = [...new Set(c.decls.flatMap((x) => x.d.uses?.mapped ?? []).map((n) => entryByDecl.get(n)).filter((x) => x && x.id !== e.id).map((x) => x.id))].sort();
      if (usedCards.length) right += `<div class="uses-mapped">The Lean proof uses ${usedCards.map((k) => { const x = cards.find((y) => y.id === k); return `<a href="#c-${slug(k)}">${escapeHtml(x ? cardTitle(x) : k)}</a>`; }).join(', ')}${c.proofEnv ? '' : ' (no printed proof here)'}.</div>`;
      c.usedCards = usedCards;
    }
    const fp = sha256(stableStringify({
      paper: raw.slice(c.start, c.end), kind: e.kind, note: e.note ?? null, proof: e.proof ?? null,
      lean: c.decls.map(({ name, d }) => ({ name, type: d.type_hash, closure: d.closure_hash, body: c.proofEnv ? d.body_hash : null })),
      env: envId,
    })).slice(0, 16);
    c.fp = fp; c.flags = [...new Set(flags)]; c.account = account;
    report.cards.push({ id: c.id, kind: e.kind, title: cardTitle(c), paper_line: c.anchor.line, lean: c.decls.map((x) => x.name), fingerprint: fp, flags: c.flags, account });
    report.anchors[c.id] = { paper: { start: c.anchor.start, line: c.anchor.line }, lean: c.decls.map(({ name, d }) => ({ name, range: d.range ?? null })) };
    const badges = `<span class="badge ${escapeHtml(e.kind)}">${escapeHtml(e.kind)}</span>` + c.flags.map((f) => `<span class="badge flag">${escapeHtml(f)}</span>`).join('');
    htmlCards.push({ start: c.start, end: c.end, html: `<section class="card" id="c-${slug(c.id)}" data-card="${escapeHtml(c.id)}" data-fp="${fp}">` +
      `<header><h3>${escapeHtml(cardTitle(c))}</h3>${badges}<a class="graph-link" href="#g-${slug(c.id)}" title="show in the graph">graph</a>` +
      `<label class="mark"><input type="checkbox" data-mark="${escapeHtml(c.id)}"> reviewed</label><span class="mark-state" data-mark-state="${escapeHtml(c.id)}"></span><span class="fp" title="fingerprint of the paper text and the Lean statement, context and toolchain">${fp}</span></header>` +
      (e.note ? `<p class="note entry-note">${escapeHtml(e.note)}</p>` : '') +
      `<div class="pair"><div class="paper-col">${left}</div><div class="lean-col">${right || '<p class="muted">No Lean counterpart.</p>'}</div></div>${proofHtml}</section>` });
  }

  // ---------------------------------------------- paper order with text ----
  const blocks = [];
  for (const [a, b] of scopeRanges) {
    let pos = a;
    const inRange = htmlCards.filter((h) => h.start >= a && h.start < b).sort((x, y) => x.start - y.start);
    const textBlock = (x, y) => {
      if (x >= y) return;
      // Section headings inside a text block are rendered as headings.
      let p = x;
      for (const s of doc.sections.filter((s) => s.start >= x && s.start < y)) {
        if (doc.text.slice(p, s.start).trim()) blocks.push(`<div class="paper-text">${renderTex(p, s.start)}</div>`);
        const h = s.level === 0 ? 'h2' : 'h3';
        blocks.push(`<${h} class="sec" id="sec-${slug(s.number ?? s.title)}">${escapeHtml(s.number ?? '')} ${tex.text(s.title, s.titleStart)}</${h}>`);
        p = s.end;
        const lab = /^\s*\\label\s*\{[^}]*\}/.exec(doc.text.slice(p, y));
        if (lab) p += lab[0].length;
      }
      if (doc.text.slice(p, y).trim()) blocks.push(`<div class="paper-text">${renderTex(p, y)}</div>`);
    };
    for (const h of inRange) {
      textBlock(pos, h.start);
      blocks.push(h.html);
      pos = Math.max(pos, h.end);
    }
    textBlock(pos, b);
  }
  for (const w of tex.warnings) warnings.push(w);

  // ----------------------------------------------------------- graph ----
  let graphHtml = '';
  if (graph) {
    const g = buildGraphs({ cards: cards.filter((c) => inScope(c.start)), cardTitle, isResult, labelEntry, doc, refsIn, entryByDecl, ex, errors });
    graphHtml = g.html;
    report.graph = g.edges;
  }

  // ----------------------------------------------------------- sync ----
  if (previous) {
    const old = JSON.parse(fs.readFileSync(previous, 'utf8'));
    const sync = { moved: [], new: [], broken: [] };
    for (const [k, v] of Object.entries(report.anchors)) {
      const o = old.anchors?.[k];
      if (!o) sync.new.push(k);
      else if (stableStringify(o) !== stableStringify(v)) sync.moved.push(k);
    }
    for (const k of Object.keys(old.anchors ?? {})) if (!report.anchors[k]) sync.broken.push(k);
    report.sync = sync;
  }
  report.errors = [...new Set(errors)];
  report.warnings = [...new Set(warnings)];

  // ----------------------------------------------------------- page ----
  const css = fs.readFileSync(path.join(here, 'reader.css'), 'utf8');
  const js = fs.readFileSync(path.join(here, 'reader.js'), 'utf8');
  const katexDir = path.join(here, '../node_modules/katex/dist');
  const katexCss = fs.readFileSync(path.join(katexDir, 'katex.min.css'), 'utf8')
    .replace(/src:url\(fonts\/(KaTeX_[^)]+\.woff2)\) format\("woff2"\),url\([^)]+\) format\("woff"\),url\([^)]+\) format\("truetype"\)/g,
      (_, font) => `src:url(data:font/woff2;base64,${fs.readFileSync(path.join(katexDir, 'fonts', font)).toString('base64')}) format("woff2")`);
  const stem = map.output_stem ?? 'paper-lean-reader';
  const meta = { stem, schema: 'paper-lean-audit/reader-2', paper: map.sources.paper.commit ?? null, formal: map.sources.formal.commit, cards: report.cards.map((c) => ({ id: c.id, fp: c.fingerprint })) };
  const src = map.sources;
  const errorBanner = report.errors.length ? `<div class="build-errors"><b>${report.errors.length} check${report.errors.length > 1 ? 's' : ''} failed.</b><ul>${report.errors.map((x) => `<li>${escapeHtml(x)}</li>`).join('')}</ul></div>` : '';
  const html = `<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>${escapeHtml(map.title ?? 'Paper and Lean')}</title>
<style>${katexCss}</style><style>${css}</style></head>
<body><header class="top"><h1>${escapeHtml(map.title ?? 'Paper and Lean')}</h1>
<p class="sources">Paper <code>${escapeHtml(src.paper.repo ?? '')}</code> at <code>${escapeHtml((src.paper.commit ?? '').slice(0, 12))}</code> · Lean <code>${escapeHtml(src.formal.repo ?? '')}</code> at <code>${escapeHtml(src.formal.commit.slice(0, 12))}</code> · <code>${escapeHtml(envId.toolchain ?? '')}</code></p>
<p class="legend"><span class="badge formalizes">formalizes</span> Lean states the paper's claim · <span class="badge cites">cites</span> known result, proved in Lean by any route · <span class="badge lean-only">Lean only</span> no paper counterpart · <span class="badge prose">prose</span> no Lean counterpart · <span class="badge lean-adds">Lean adds</span> step the text leaves out · <span class="badge large">large step</span> sentence covering many Lean steps</p>
<div class="tools"><span id="progress"></span> <button id="export">Export marks</button> <label class="import">Import marks <input id="import" type="file" accept="application/json"></label> <a href="#graph">Graph</a></div>
${errorBanner}</header>
<main>${blocks.join('\n')}
${graphHtml}</main>
<div id="preview" class="preview" hidden></div>
<script>window.READER_META = ${JSON.stringify(meta).replace(/</g, '\\u003c')};</script>
<script>${js}</script>
</body></html>
`;
  return { html, report, stem };
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const argv = process.argv.slice(2);
  const opt = (name, fallback = null) => { const i = argv.indexOf(name); return i >= 0 ? argv[i + 1] : fallback; };
  const mapPath = opt('--map');
  const out = path.resolve(opt('--out', 'build'));
  if (!mapPath) { console.error('usage: node v2/build.mjs --map MAP --out DIR [--paper FILE|REPO] [--extraction FILE] [--bib FILE] [--previous REPORT] [--check] [--no-graph]'); process.exit(2); }
  const bibPath = opt('--bib');
  const args = { mapPath, paperArg: opt('--paper'), extractionPath: opt('--extraction'), previous: opt('--previous'), graph: !argv.includes('--no-graph'), bib: bibPath ? fs.readFileSync(bibPath, 'utf8') : null };
  const first = build(args);
  if (argv.includes('--check')) {
    const second = build(args);
    if (second.html !== first.html || stableStringify(second.report) !== stableStringify(first.report)) first.report.errors.push('nondeterminism: two builds from the same inputs differ');
  }
  fs.mkdirSync(out, { recursive: true });
  fs.writeFileSync(path.join(out, first.stem + '.html'), first.html);
  fs.writeFileSync(path.join(out, first.stem + '.report.json'), stableStringify(first.report) + '\n');
  for (const e of first.report.errors) console.error('error: ' + e);
  console.error(`wrote ${path.join(out, first.stem + '.html')} (${first.report.cards.length} cards, ${first.report.errors.length} errors, ${first.report.warnings.length} warnings)`);
  if (argv.includes('--check') && first.report.errors.length) process.exit(1);
}
