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
import { loadMap, mapDeclarations, mapMapped, mapTraces } from '../v2/map.mjs';
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
  assert.deepEqual(sum.account, { sentences: 4, matched: 3, prose: 1, lean_adds: 1, large: 0, cited: ['lem:double'], used: ['lem:double'], only_paper: [], only_lean: [] });
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

test('a sentence can follow the proof into a helper lemma the proof calls', (t) => {
  // The helper isEven_of_isDoubled (Main.lean lines 10-12) with its trace.
  const helper = 'AuditFixture.isEven_of_isDoubled';
  const goal = (hyps, target) => [{ hyps, tag: '', target }];
  const addHelper = (ex) => {
    ex.declarations[helper] = { kind: 'theorem', module: 'AuditFixture.Main', file: 'AuditFixture/Main.lean',
      range: { start: [10, 0], end: [12, 23] }, signature: 'AuditFixture.isEven_of_isDoubled {n : Nat} (h : IsDoubled n) : IsEven n',
      source: 'theorem isEven_of_isDoubled {n : Nat} (h : IsDoubled n) : IsEven n := by\n  obtain ⟨k, rfl⟩ := h\n  exact double_isEven k',
      context: [], deps: [], type_hash: '0', body_hash: '1', closure_hash: '0', unused: [],
      uses: { mapped: ['AuditFixture.double_isEven'], helpers: [], library: [], via: {} } };
    ex.traces[helper] = { steps: [
      { index: 0, depth: 0, parent: null, kind: 'Lean.Parser.Tactic.obtain', range: { start: [11, 2], end: [11, 22] }, text: 'obtain ⟨k, rfl⟩ := h',
        goals_before: goal([{ name: 'n', type: 'Nat' }, { name: 'h', type: 'IsDoubled n' }], 'IsEven n'),
        goals_after: goal([{ name: 'k', type: 'Nat' }], 'IsEven 𝔡(k)'), uses_library: [], uses_project: [] },
      { index: 1, depth: 0, parent: null, kind: 'Lean.Parser.Tactic.exact', range: { start: [12, 2], end: [12, 23] }, text: 'exact double_isEven k',
        goals_before: goal([{ name: 'k', type: 'Nat' }], 'IsEven 𝔡(k)'), goals_after: [], uses_library: [], uses_project: ['AuditFixture.double_isEven'] }] };
  };
  const follow = (m) => { entry(m, 'lem:sum').proof.sentences[1].steps.splice(1, 0, { decl: helper, quote: 'exact double_isEven k' }); };
  const r = run(copy(t, { ex: addHelper, map: follow }));
  assert.deepEqual(r.report.errors, []);
  // The sentence shows the helper's state change, labelled with the helper.
  assert.match(r.html, /<div class="in-decl">in <code title="AuditFixture.isEven_of_isDoubled">isEven_of_isDoubled<\/code><\/div><div class="goal closed">goal closed: <code>IsEven 𝔡\(k\)<\/code><\/div>/);
  // The helper step no sentence claims is a Lean-added step, before the sentence.
  assert.match(r.html, /Lean adds<\/span><\/div><div class="lean-col"><div class="in-decl">in <code[^>]*>isEven_of_isDoubled<\/code><\/div>[^]*?obtain ⟨k, rfl⟩ := h[^]*?By Lemma/);
  const sum = r.report.cards.find((c) => c.id === 'lem:sum');
  assert.equal(sum.account.lean_adds, 2);
  assert.deepEqual(r.report.anchors['lem:sum.proof.sentences[1]'].steps.map((s) => s.decl ?? null), [null, helper, null]);
  // A changed helper proof invalidates the card's fingerprint.
  const r2 = run(copy(t, { ex: (ex) => { addHelper(ex); ex.declarations[helper].body_hash = '2'; }, map: follow }));
  assert.notEqual(r2.report.cards.find((c) => c.id === 'lem:sum').fingerprint, sum.fingerprint);
  // The extractor traces the helper but keeps computing uses through it.
  const m = loadMap(copy(t, { map: follow }));
  assert.ok(mapTraces(m).includes(helper) && mapDeclarations(m).includes(helper));
  assert.ok(!mapMapped(m).includes(helper));
  // "decl" alone claims the helper's whole proof, so nothing of it is added.
  const whole = run(copy(t, { ex: addHelper, map: (m) => { entry(m, 'lem:sum').proof.sentences[1].steps.splice(1, 0, { decl: helper }); } }));
  assert.deepEqual(whole.report.errors, []);
  assert.equal(whole.report.cards.find((c) => c.id === 'lem:sum').account.lean_adds, 1);
  assert.deepEqual(whole.report.anchors['lem:sum.proof.sentences[1]'].steps.map((s) => s.decl ?? null), [null, helper, helper, null]);
  // A helper without a trace fails.
  const r3 = run(copy(t, { ex: (ex) => { addHelper(ex); delete ex.traces[helper]; }, map: follow }));
  assert.ok(hasError(r3, /no proof-state trace for AuditFixture.isEven_of_isDoubled/));
});

test('a sentence covering more Lean steps than the threshold is a large step', (t) => {
  const r = run(copy(t, { map: (m) => { m.settings = { large_step: 1 }; } }));
  assert.match(r.html, /large step: 2 Lean steps/);
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

test('sentences: a display that ends with a period and a long label ends the sentence', () => {
  const text = 'We show\n\\begin{equation} a=b.\n \\label{eq:a-rather-long-label}\\end{equation}\nThe inclusion holds.';
  const s = sentences(text, 0, text.length).map((x) => text.slice(x.start, x.end));
  assert.deepEqual(s, ['We show\n\\begin{equation} a=b.\n \\label{eq:a-rather-long-label}\\end{equation}', 'The inclusion holds.']);
});

test('sentences: list markup joins the first and the last item', () => {
  const text = 'Two facts:\n\\begin{itemize}\n\\item $a=b$.\n\\item $c=d$.\n\\end{itemize}\n\nHence the claim.';
  const s = sentences(text, 0, text.length).map((x) => text.slice(x.start, x.end));
  assert.deepEqual(s, ['Two facts:', '\\begin{itemize}\n\\item $a=b$.', '\\item $c=d$.\n\\end{itemize}', 'Hence the claim.']);
});

test('a proof row holding a list item renders without an unclosed list', (t) => {
  const r = run(copy(t, {
    paper: (p) => p.replace('This is the familiar argument.', 'Two remarks:\n\\begin{itemize}\n\\item This is the familiar argument.\n\\item It is short.\n\\end{itemize}'),
    map: (m) => { entry(m, 'lem:sum').proof.sentences.push({ quote: 'It is short.', kind: 'prose', note: 'A remark.' }, { quote: 'Two remarks:', kind: 'prose', note: 'A remark.' }); },
  }));
  assert.deepEqual(r.report.errors, []);
  assert.ok(!r.report.warnings.some((w) => /unclosed environment/.test(w)), r.report.warnings.join('; '));
});

test('environment numbers follow shared counters and section resets', () => {
  const doc = parsePaper(fs.readFileSync(path.join(fixture, 'paper.tex'), 'utf8'));
  assert.deepEqual(doc.envs.map((e) => `${e.title} ${e.number}`), ['Definition 1.1', 'Lemma 1.2', 'Lemma 1.3']);
});
