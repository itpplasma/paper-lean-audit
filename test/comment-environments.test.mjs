import test from 'node:test';
import assert from 'node:assert/strict';
import {stripComments, TexRenderer} from '../texhtml.mjs';

test('excluded proofs cannot override active labels or equation numbering', () => {
  const source = 'before\n\\begin{comment}\n\\label{same}\\begin{equation}old\\end{equation}\n\\end{comment}\n\\label{same}after';
  const clean = stripComments(source);
  assert.equal(clean.split('\n').length, source.split('\n').length);
  assert.equal(clean.length, source.length);
  assert.deepEqual([...clean.matchAll(/\\label\{([^}]+)\}/g)].map(m => m[1]), ['same']);
  assert.ok(!clean.includes('old'));
  assert.ok(clean.endsWith('\\label{same}after'));
  const renderer = new TexRenderer({macros: {}, refs: {}, cites: {}, eqAuto: new Map()});
  assert.ok(!renderer.block(clean).includes('old'));
});
