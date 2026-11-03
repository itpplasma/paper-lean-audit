// The v2 reader in Chromium: review marks keyed by fingerprints survive a
// reload, become invalid when the fingerprint changes, colour the graph node,
// export and import; back-references show a preview on hover.
import test from 'node:test';
import assert from 'node:assert/strict';
import { createServer } from 'node:http';
import { existsSync, readFileSync } from 'node:fs';
import { spawnSync } from 'node:child_process';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { chromium } from 'playwright-core';
import { build } from '../v2/build.mjs';

const here = path.dirname(fileURLToPath(import.meta.url));
const executablePath = process.env.CHROMIUM_PATH ??
  ['/usr/bin/chromium', '/opt/pw-browsers/chromium-1194/chrome-linux/chrome', '/opt/pw-browsers/chromium'].find((p) => existsSync(p));
const hasDot = spawnSync('dot', ['-V']).status === 0;

test('v2 reader: marks, invalidation, graph colours, export/import and previews', { skip: !executablePath && 'Chromium not found' }, async (t) => {
  const { html } = build({ mapPath: path.join(here, 'fixtures/v2/map.json'), graph: hasDot });
  const server = createServer((req, res) => { res.setHeader('content-type', 'text/html; charset=utf-8'); res.end(html); });
  await new Promise((r) => server.listen(0, '127.0.0.1', r));
  const url = `http://127.0.0.1:${server.address().port}/`;
  const browser = await chromium.launch({ executablePath });
  t.after(async () => { await browser.close(); server.close(); });
  const context = await browser.newContext({ acceptDownloads: true });
  const page = await context.newPage();
  const errors = [];
  page.on('pageerror', (e) => errors.push(e.message));
  await page.goto(url);
  const box = 'input[data-mark="lem:sum"]';
  assert.equal(await page.isChecked(box), false);
  await page.check(box);
  await page.reload();
  assert.equal(await page.isChecked(box), true);
  assert.match(await page.textContent('#progress'), /^1 of 3 cards reviewed/);
  if (hasDot) assert.equal(await page.evaluate(() => document.getElementById('g-lem:sum').classList.contains('reviewed')), true);

  // Export, then change the stored fingerprint as a changed Lean statement would.
  const [download] = await Promise.all([page.waitForEvent('download'), page.click('#export')]);
  const exported = JSON.parse(readFileSync(await download.path(), 'utf8'));
  assert.equal(exported.schema, 'paper-lean-audit/marks-2');
  assert.equal(exported.marks['lem:sum'].reviewed, true);
  await page.evaluate(() => {
    const k = 'paper-lean-audit:marks:fixture-reader';
    const m = JSON.parse(localStorage.getItem(k));
    m['lem:sum'].fp = '0000000000000000';
    localStorage.setItem(k, JSON.stringify(m));
  });
  await page.reload();
  assert.equal(await page.isChecked(box), false);
  assert.match(await page.textContent('[data-mark-state="lem:sum"]'), /invalidated/);
  if (hasDot) assert.equal(await page.evaluate(() => document.getElementById('g-lem:sum').classList.contains('stale')), true);

  // Importing the export restores the valid mark.
  await page.setInputFiles('#import', await download.path());
  assert.equal(await page.isChecked(box), true);

  // Hover over a back-reference previews the definition shown earlier.
  await page.hover('#c-lem\\:sum a.backref[href="#d-AuditFixture.IsEven"]');
  assert.equal(await page.isVisible('#preview'), true);
  assert.match(await page.textContent('#preview'), /natural number is even/);
  assert.deepEqual(errors, []);
});

test('v2 reader: a long source path does not widen the page on a phone', { skip: !executablePath && 'Chromium not found' }, async (t) => {
  const fs = await import('node:fs');
  const os = await import('node:os');
  const fixture = path.join(here, 'fixtures/v2');
  const dir = fs.mkdtempSync(path.join(os.tmpdir(), 'pla-v2-narrow-'));
  t.after(() => fs.rmSync(dir, { recursive: true, force: true }));
  for (const f of ['map.json', 'paper.tex']) fs.copyFileSync(path.join(fixture, f), path.join(dir, f));
  const ex = JSON.parse(readFileSync(path.join(fixture, 'extraction.json'), 'utf8'));
  for (const d of [...Object.values(ex.declarations), ...Object.values(ex.context)]) d.file = 'AuditFixture/AVeryLongDirectoryName/AnotherQuiteLongModuleNameWithoutBreaks.lean';
  fs.writeFileSync(path.join(dir, 'extraction.json'), JSON.stringify(ex));
  const { html } = build({ mapPath: path.join(dir, 'map.json'), graph: false });
  const browser = await chromium.launch({ executablePath });
  t.after(() => browser.close());
  const page = await browser.newPage({ viewport: { width: 390, height: 800 } });
  await page.setContent(html);
  assert.equal(await page.evaluate(() => document.documentElement.scrollWidth <= window.innerWidth), true);
});
