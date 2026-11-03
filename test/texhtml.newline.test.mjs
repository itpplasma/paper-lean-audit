import test from 'node:test';
import assert from 'node:assert/strict';
import { TexRenderer } from '../texhtml.mjs';

test('AI addition newline renders as a line break without exposing the TeX command', () => {
  const renderer = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map() });
  const html = renderer.block('before\\AIadd{\\newline}after', 0);
  assert.match(html, /<span class="ai-add"><br><\/span>/);
  assert.doesNotMatch(html, /\\newline|code/);
  assert.deepEqual(renderer.warnings, []);
});

test('a backslash before a line break is a control space', () => {
  const renderer = new TexRenderer({ macros: {}, refs: {}, cites: {}, eqAuto: new Map() });
  const html = renderer.block('i.e.\\\nthe next word', 0);
  assert.doesNotMatch(html, /\\/);
  assert.match(html, /i\.e\. +the next word/);
});
