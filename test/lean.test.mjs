// Behavioural tests for full Lean declaration extraction.
import test from 'node:test';
import assert from 'node:assert/strict';
import { extractDeclaration, extractStatement } from '../lean.mjs';

test('full theorem extraction keeps a long tactic proof and nested local claims', () => {
  const body = [
    '/-- Reviewed theorem. -/',
    '@[simp]',
    'theorem reviewed (n : Nat) : n = n := by',
    '  have localFact : n = n := by',
    '    rfl',
    '  exact localFact',
    ...Array.from({ length: 180 }, (_, i) => `  -- proof step ${i + 1}`),
    '  exact localFact',
    '',
    'theorem next : True := by trivial',
    '',
  ].join('\n').split('\n');
  const result = extractDeclaration(body, 3);
  assert.equal(result.startLine, 1);
  assert.equal(result.endLine, 187);
  assert.equal(result.truncated, false);
  assert.match(result.text, /@\[simp\]\ntheorem reviewed[\s\S]*have localFact/);
  assert.match(result.text, /proof step 180\n  exact localFact$/);
  assert.doesNotMatch(result.text, /theorem next/);
  // Existing statement extraction remains signature-only.
  assert.doesNotMatch(extractStatement(body, 3).text, /have localFact/);
});

test('full extraction retains where helpers and stops at namespace end', () => {
  const lines = [
    'namespace Demo',
    'def nested : Nat := by',
    '  exact helper',
    'where',
    '  helper : Nat := 1',
    'end Demo',
    'theorem outside : True := by trivial',
  ];
  const result = extractDeclaration(lines, 2);
  assert.equal(result.text, lines.slice(1, 5).join('\n'));
  assert.equal(result.startLine, 2);
  assert.equal(result.endLine, 5);
});

test('declaration-shaped text in comments and strings does not end extraction', () => {
  const lines = [
    'theorem quoted : True := by',
    '  let s := "theorem fake : False := by"',
    '  /- theorem alsoFake : False := by -/',
    '  trivial',
    '  -- still in proof',
    'theorem next : True := by trivial',
  ];
  assert.equal(extractDeclaration(lines, 1).text, lines.slice(0, 5).join('\n'));
});

test('the next command’s docstring and attributes stay with that command', () => {
  const lines = [
    'theorem first : True := by',
    '  trivial',
    '',
    '/-- Documentation for the next theorem. -/',
    '@[simp]',
    'theorem next : True := by trivial',
    'set_option pp.universes true',
  ];
  const first = extractDeclaration(lines, 1);
  assert.equal(first.text, lines.slice(0, 2).join('\n'));
  assert.equal(first.endLine, 2);
  const next = extractDeclaration(lines, 6);
  assert.equal(next.text, lines.slice(3, 6).join('\n'));
  assert.equal(next.startLine, 4);
  assert.equal(next.endLine, 6);
});
