// The Lean extractor on the fixture project reproduces the committed
// extraction byte for byte (statement, context, fingerprints, unused binders,
// uses through helpers and proof-state traces). Needs elan with the fixture's
// toolchain; skipped otherwise.
import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { extract } from '../v2/extract.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const fixture = path.join(here, 'fixtures/v2');
const toolchain = fs.readFileSync(path.join(fixture, 'lean/lean-toolchain'), 'utf8').trim();
const lake = spawnSync('lake', ['--version'], { cwd: path.join(fixture, 'lean'), encoding: 'utf8' });
const skip = lake.status !== 0 && `lake for ${toolchain} not available`;

test('extractor output equals the committed fixture extraction', { skip, timeout: 600000 }, async (t) => {
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pla-lean-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  const project = path.join(dir, 'lean');
  fs.cpSync(path.join(fixture, 'lean'), project, { recursive: true, filter: (p) => !p.includes(`${path.sep}.lake`) });
  execFileSync('lake', ['build'], { cwd: project, stdio: 'ignore' });
  const out = path.join(dir, 'extraction.json');
  await extract({ mapPath: path.join(fixture, 'map.json'), project, out });
  const got = JSON.parse(fs.readFileSync(out, 'utf8'));
  const want = JSON.parse(fs.readFileSync(path.join(fixture, 'extraction.json'), 'utf8'));
  assert.deepEqual(got, want);
  assert.equal(fs.readFileSync(out, 'utf8'), fs.readFileSync(path.join(fixture, 'extraction.json'), 'utf8'));
  // Spot checks of the features the reader relies on.
  const d = got.declarations['AuditFixture.even_add'];
  assert.deepEqual(d.unused.map((u) => u.name), ['hc']);
  assert.deepEqual(d.uses.mapped, ['AuditFixture.double_isEven']);
  assert.deepEqual(d.uses.helpers, ['AuditFixture.isEven_of_isDoubled']);
  assert.deepEqual(d.context, ['AuditFixture.IsDoubled', 'AuditFixture.IsEven', 'AuditFixture.double']);
  assert.match(got.declarations['AuditFixture.double_isEven'].signature, /IsEven 𝔡\(k\)/);
  const steps = got.traces['AuditFixture.even_add'].steps;
  assert.deepEqual(steps.map((s) => s.text.split(' ')[0]), ['obtain', 'have', 'obtain', 'refine', 'rw']);
  assert.ok(steps[1].goals_after[0].hyps.some((h) => h.name === 'hb' && h.type === 'IsEven n'));
  assert.deepEqual(steps[1].uses_project, ['AuditFixture.isEven_of_isDoubled']);
});

test('two traced declarations of one module both get their proof states', { skip, timeout: 600000 }, async (t) => {
  // Lean resets info trees per command, so the extractor must keep them for
  // every traced command, not only for the last one of the module.
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pla-lean-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  const project = path.join(dir, 'lean');
  fs.cpSync(path.join(fixture, 'lean'), project, { recursive: true, filter: (p) => !p.includes(`${path.sep}.lake`) });
  execFileSync('lake', ['build'], { cwd: project, stdio: 'ignore' });
  const map = JSON.parse(fs.readFileSync(path.join(fixture, 'map.json'), 'utf8'));
  const sum = map.entries.find((e) => e.id === 'lem:sum');
  sum.proof.sentences[1].steps.push({ decl: 'AuditFixture.isEven_of_isDoubled', quote: 'exact double_isEven k' });
  const mapPath = path.join(dir, 'map.json');
  fs.writeFileSync(mapPath, JSON.stringify(map));
  const out = path.join(dir, 'extraction.json');
  await extract({ mapPath, project, out });
  const got = JSON.parse(fs.readFileSync(out, 'utf8'));
  assert.deepEqual(got.traces['AuditFixture.isEven_of_isDoubled'].steps.map((s) => s.text), ['obtain ⟨k, rfl⟩ := h', 'exact double_isEven k']);
  assert.deepEqual(got.traces['AuditFixture.even_add'].steps.map((s) => s.text.split(' ')[0]), ['obtain', 'have', 'obtain', 'refine', 'rw']);
  // The helper is traced but stays a helper: uses still pass through it.
  assert.deepEqual(got.declarations['AuditFixture.even_add'].uses.mapped, ['AuditFixture.double_isEven']);
});
