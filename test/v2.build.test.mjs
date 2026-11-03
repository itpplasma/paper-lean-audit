// Side-by-side reader (map v2) on the synthetic fixture in test/fixtures/v2:
// a definition, a lemma with a one-line proof, a lemma whose proof has a
// Lean-added step, a prose sentence, an unused hypothesis and a Lean-only
// helper. Each negative test breaks one input and expects the named check.
import test from 'node:test';
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { build } from '../v2/build.mjs';
import { sentences, parsePaper, resolveQuote, maskComments } from '../v2/paper.mjs';
import { stableStringify } from '../v2/util.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const fixture = path.join(here, 'fixtures/v2');
const hasDot = spawnSync('dot', ['-V']).status === 0;

function copy(t, edit = {}) {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pla-v2-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  const map = JSON.parse(fs.readFileSync(path.join(fixture, 'map.json'), 'utf8'));
  const ex = JSON.parse(fs.readFileSync(path.join(fixture, 'extraction.json'), 'utf8'));
  let paper = fs.readFileSync(path.join(fixture, 'paper.tex'), 'utf8');
  if (edit.map) edit.map(map);
  if (edit.ex) edit.ex(ex);
  if (edit.paper) paper = edit.paper(paper);
  fs.writeFileSync(path.join(dir, 'map.json'), JSON.stringify(map));
  fs.writeFileSync(path.join(dir, 'extraction.json'), JSON.stringify(ex));
  fs.writeFileSync(path.join(dir, 'paper.tex'), paper);
  return path.join(dir, 'map.json');
}
const run = (mapPath, opts = {}) => build({ mapPath, graph: hasDot, ...opts });
const entry = (map, id) => map.entries.find((e) => e.id === id);
const hasError = (r, re) => r.report.errors.some((e) => re.test(e));

test('fixture builds without failed checks and shows every element of the view', (t) => {
  const r = run(copy(t));
  assert.deepEqual(r.report.errors, []);
  const h = r.html;
  // Statement in project notation, context definition once, back-references.
  assert.match(h, /id="d-AuditFixture.double"/);
  assert.equal((h.match(/id="d-AuditFixture.IsEven"/g) ?? []).length, 1);
  assert.match(h, /class="backref" href="#d-AuditFixture.IsEven"/);
  assert.match(h, /𝔡\(k\)/);
  // Unused hypothesis, Lean-only helper with its note, unfold toggle.
  assert.match(h, /unused by the proof: <code>hc : 0 &lt; c<\/code>/);
  assert.match(h, /id="d-AuditFixture.IsDoubled"[^]*?Lean only/);
  assert.match(h, /Lean phrases/);
  assert.match(h, /unfolded to the library boundary/);
  // Proof column: state change, Lean adds with note, prose with note.
  assert.match(h, /<span class="hn">a<\/span> : <code>Nat<\/code>/);
  assert.match(h, /Lean adds<\/span> <span class="note">Lean names the witness/);
  assert.match(h, /prose<\/span> A remark on the argument/);
  assert.match(h, /through it: <a href="#c-lem:double">Lemma 1.2<\/a>/);
  const sum = r.report.cards.find((c) => c.id === 'lem:sum');
  assert.deepEqual(sum.account, { sentences: 4, matched: 3, prose: 1, lean_adds: 2, large: 0, cited: ['lem:double'], used: ['lem:double'], only_paper: [], only_lean: [] });
  assert.deepEqual(sum.flags.sort(), ['Lean adds', 'Lean-only definitions', 'prose', 'unused hypotheses']);
});

test('two builds from the same inputs are byte-identical', (t) => {
  const m = copy(t);
  const a = run(m), b = run(m);
  assert.equal(a.html, b.html);
  assert.equal(stableStringify(a.report), stableStringify(b.report));
});

test('a paper environment without a map entry fails', (t) => {
  const r = run(copy(t, { map: (m) => { m.entries = m.entries.filter((e) => e.id !== 'lem:double'); } }));
  assert.ok(hasError(r, /Lemma 1\.2 \(line \d+\) has no map entry/), r.report.errors.join('\n'));
});

test('a quote that is not verbatim in the paper fails', (t) => {
  const r = run(copy(t, { map: (m) => { entry(m, 'lem:sum').proof.sentences[0].quote = 'Write $m = 2a$.'; } }));
  assert.ok(hasError(r, /paper quote not found/));
});

test('an occurrence beyond the quote count fails, and an ambiguous quote needs one', (t) => {
  const r = run(copy(t, { map: (m) => { entry(m, 'def:even').paper = { quote: '\\label{def:even}', occurrence: 2 }; } }));
  assert.ok(hasError(r, /occurrence 2 requested/));
  const r2 = run(copy(t, { map: (m) => { entry(m, 'def:even').paper = { quote: 'is even' }; } }));
  assert.ok(hasError(r2, /occurs \d times; give "occurrence"/));
});

test('a quote inside a TeX comment does not count', () => {
  const raw = 'A % hidden \\label{x}\n\\label{x}\n';
  const r = resolveQuote(raw, { quote: '\\label{x}' }, 0, raw.length, maskComments(raw));
  assert.equal(r.start, raw.lastIndexOf('\\label{x}'));
});

test('a Lean declaration or step anchor that does not exist fails', (t) => {
  const r = run(copy(t, { map: (m) => { entry(m, 'def:even').lean.push('AuditFixture.missing'); } }));
  assert.ok(hasError(r, /AuditFixture.missing not found in the extraction/));
  const r2 = run(copy(t, { map: (m) => { entry(m, 'lem:sum').proof.sentences[0].steps = [{ quote: 'simp' }]; } }));
  assert.ok(hasError(r2, /Lean quote not found in AuditFixture.even_add/));
  const r3 = run(copy(t, { map: (m) => { entry(m, 'lem:sum').proof.sentences[0].steps = [{ at: [99, 0] }]; } }));
  assert.ok(hasError(r3, /no tactic step of AuditFixture.even_add at \[99,0\]/));
});

test('a statement-context definition without counterpart or lean_only entry fails', (t) => {
  const r = run(copy(t, { map: (m) => { m.lean_only = []; } }));
  assert.ok(hasError(r, /statement context of AuditFixture.even_add contains AuditFixture.IsDoubled/));
});

test('a proof sentence without a Lean step or prose entry fails', (t) => {
  const r = run(copy(t, { map: (m) => { entry(m, 'lem:sum').proof.sentences.pop(); } }));
  assert.ok(hasError(r, /proof sentence at line \d+ has no map entry: "This is the familiar argument\."/));
});

test('a printed proof without a sentence map fails', (t) => {
  const r = run(copy(t, { map: (m) => { delete entry(m, 'lem:double').proof; } }));
  assert.ok(hasError(r, /lem:double: the printed proof .* has no sentence map/));
});

test('cited and used results must agree unless the map records the difference', (t) => {
  const drop = (ex) => {
    const u = ex.declarations['AuditFixture.even_add'].uses;
    u.mapped = []; u.via = {};
  };
  const r = run(copy(t, { ex: drop }));
  assert.ok(hasError(r, /lem:sum: the paper cites lem:double but the Lean proof does not use it/));
  const r2 = run(copy(t, { ex: drop, map: (m) => { entry(m, 'lem:sum').citations = { 'lem:double': 'Lean proves this directly.' }; } }));
  assert.deepEqual(r2.report.errors, []);
  assert.match(r2.html, /Cited, not used by Lean: <a href="#c-lem:double">Lemma 1.2<\/a> <span class="note">Lean proves this directly\./);
});

test('a sentence covering more Lean steps than the threshold is a large step', (t) => {
  const r = run(copy(t, { map: (m) => { m.settings = { large_step: 1 }; } }));
  assert.match(r.html, /large step: 3 Lean steps/);
});

test('a sentence may name steps of a step lemma that the proof calls', (t) => {
  const r = run(copy(t, { map: (m) => { entry(m, 'lem:sum').proof.lean_adds.push({ step: { decl: 'AuditFixture.isEven_of_isDoubled', quote: 'obtain ⟨k, rfl⟩ := h' }, note: 'The helper unpacks n = 2k.' }); } }));
  assert.deepEqual(r.report.errors, []);
  // The state change of the callee is shown under its name, its unclaimed step as Lean adds.
  assert.match(r.html, /<div class="in-decl">in <code title="AuditFixture.isEven_of_isDoubled">isEven_of_isDoubled<\/code><\/div><div class="goal closed">goal closed<\/div>/);
  assert.match(r.html, /Lean adds<\/span> <span class="note">The helper unpacks n = 2k\.<\/span><\/div><div class="lean-col"><div class="in-decl">in <code title="AuditFixture.isEven_of_isDoubled">/);
  assert.match(r.html, /Lean: <code>AuditFixture.even_add<\/code>, with steps in <code title="AuditFixture.isEven_of_isDoubled">/);
  assert.deepEqual(r.report.anchors['lem:sum.proof.sentences[1]'].steps.map((x) => x.decl ?? null), [null, 'AuditFixture.isEven_of_isDoubled', null]);
  // A step lemma is not a mapped result: the result it uses still counts as used by the proof.
  assert.deepEqual(r.report.cards.find((c) => c.id === 'lem:sum').account.used, ['lem:double']);
  const r2 = run(copy(t, { map: (m) => { entry(m, 'lem:sum').proof.sentences[0].steps.push({ decl: 'AuditFixture.IsDoubled', quote: 'IsDoubled' }); } }));
  assert.ok(hasError(r2, /no proof-state trace for AuditFixture.IsDoubled/), r2.report.errors.join('\n'));
});

// The proof of the sum lemma stands apart from its statement (after a remark) and
// states and proves Lemma 1.2 where it is used.
const nested = (p) => p
  .replace(/\\begin\{lemma\}\\label\{lem:double\}[^]*?\\end\{proof\}\n/, '')
  .replace('\\begin{proof}\nWrite $m=2a$.', 'Lemma~\\ref{lem:sum} is used below.\n\\begin{proof}\nWrite $m=2a$.\n' +
    '\\begin{lemma}\\label{lem:double}\nFor every $k$, the number $\\dbl(k)$ is even.\n\\end{lemma}\n' +
    '\\begin{proof}\nBy definition, $\\dbl(k)=2k$ is of the required form.\n\\end{proof}\n');

test('a proof apart from its statement, with a lemma stated and proved inside it', (t) => {
  const r = run(copy(t, { paper: nested, map: (m) => { entry(m, 'lem:sum').proof.paper = { quote: 'Write $m=2a$.' }; } }));
  assert.deepEqual(r.report.errors, []);
  const sum = r.report.cards.find((c) => c.id === 'lem:sum');
  assert.equal(sum.account.sentences, 4);
  assert.deepEqual(sum.account.cited, ['lem:double']);
  // Paper order: statement, the text between, proof part, nested lemma, proof part.
  const at = (re) => r.html.search(re);
  const order = [at(/id="c-lem:sum"/), at(/is used below/), at(/id="p-lem:sum-0"/), at(/id="c-lem:double"/), at(/id="p-lem:sum-1"/)];
  assert.ok(order.every((x, i) => x > 0 && (i === 0 || x > order[i - 1])), JSON.stringify(order));
  assert.match(r.html, /id="p-lem:sum-0"[^]*?<h3>Proof of Lemma 1\.2<\/h3>/);
  assert.match(r.html, /id="p-lem:sum-1"[^]*?<h3>Proof of Lemma 1\.2 \(continued\)<\/h3>/);
  assert.match(r.html, /id="p-lem:sum-1"[^]*?Account\./);
  assert.doesNotMatch(r.html.slice(at(/id="p-lem:sum-0"/), at(/id="c-lem:double"/)), /Account\./);
  // A sentence quote inside the nested lemma is not a sentence of the outer proof.
  const r2 = run(copy(t, { paper: nested, map: (m) => {
    entry(m, 'lem:sum').proof.paper = { quote: 'Write $m=2a$.' };
    entry(m, 'lem:sum').proof.sentences.push({ quote: 'is of the required form', kind: 'prose', note: 'x' });
  } }));
  assert.ok(hasError(r2, /lies in an environment nested in the proof/), r2.report.errors.join('\n'));
});

test('sync against a previous report lists moved, new and broken anchors', (t) => {
  const first = run(copy(t));
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pla-v2-prev-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  const prev = path.join(dir, 'report.json');
  fs.writeFileSync(prev, stableStringify(first.report));
  const r = run(copy(t, {
    paper: (p) => p.replace('Throughout,', 'Throughout this note,\n'),
    map: (m) => { m.entries = m.entries.filter((e) => e.id !== 'lem:double'); m.entries[0].id = 'def:even-renamed'; },
  }), { previous: prev });
  assert.ok(r.report.sync.moved.includes('lem:sum'));
  assert.ok(r.report.sync.new.includes('def:even-renamed'));
  assert.ok(r.report.sync.broken.includes('lem:double'));
});

test('extraction from another Lean commit or a dirty checkout fails', (t) => {
  const r = run(copy(t, { ex: (ex) => { ex.environment.commit = 'f'.repeat(40); ex.environment.dirty = true; } }));
  assert.ok(hasError(r, /extraction is for Lean commit f{40}/));
  assert.ok(hasError(r, /uncommitted changes/));
});

test('graph: nodes link to cards, one-sided edges are highlighted', { skip: !hasDot && 'Graphviz not installed' }, (t) => {
  const ok = run(copy(t));
  assert.match(ok.html, /<g id="g-lem:sum" class="node card-node kind-formalizes/);
  assert.match(ok.html, /xlink:href="#c-lem:sum"/);
  assert.deepEqual(ok.report.graph.overall.map((e) => [e.from, e.to, e.kind]),
    [['def:even', 'lem:double', 'def'], ['def:even', 'lem:sum', 'def'], ['lem:double', 'lem:sum', 'both']]);
  const r = run(copy(t, { ex: (ex) => { const u = ex.declarations['AuditFixture.even_add'].uses; u.mapped = []; u.via = {}; },
    map: (m) => { entry(m, 'lem:sum').citations = { 'lem:double': 'noted' }; } }));
  assert.deepEqual(r.report.graph.overall.find((e) => e.to === 'lem:sum' && e.from === 'lem:double').kind, 'paper-only');
  assert.match(r.html, /class="edge edge-paper-only"/);
  assert.match(ok.html, /id="gp-lem:sum"/);
});

test('sentences: abbreviations, displays and inline mathematics', () => {
  const text = 'Write $m=2a$. By Lemma~1, $n$ is even, i.e.\\ $n=2b$. Then\n\\begin{equation}\nx=y.\n\\end{equation}\nThis is it. See Prop. 3 for more.';
  const s = sentences(text, 0, text.length).map((x) => text.slice(x.start, x.end));
  assert.deepEqual(s, ['Write $m=2a$.', 'By Lemma~1, $n$ is even, i.e.\\ $n=2b$.', 'Then\n\\begin{equation}\nx=y.\n\\end{equation}', 'This is it.', 'See Prop. 3 for more.']);
});

test('environment numbers follow shared counters and section resets', () => {
  const doc = parsePaper(fs.readFileSync(path.join(fixture, 'paper.tex'), 'utf8'));
  assert.deepEqual(doc.envs.map((e) => `${e.title} ${e.number}`), ['Definition 1.1', 'Lemma 1.2', 'Lemma 1.3']);
});
