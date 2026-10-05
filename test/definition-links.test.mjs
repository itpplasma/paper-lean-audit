import test from 'node:test';
import assert from 'node:assert/strict';
import { resolveDefinitionRef } from '../definition-links.mjs';

const weyl = { repo: 'formal', file: 'Definitions.lean', name: 'Canonical.WeylAlg' };
const degree = { repo: 'mathlib', file: 'WeightedHomogeneous.lean', name: 'MvPolynomial.weightedTotalDegree' };
const info = { repo: 'formal', file: 'Proof.lean', name: 'Proof.theorem', bindings: [] };

test('canonical definitions resolve through plain and selected open namespaces', () => {
  for (const text of ['open Canonical', 'open Canonical (WeylAlg)']) {
    assert.equal(resolveDefinitionRef({ ...info, context: [{ text }] }, 'WeylAlg', [weyl]), weyl);
  }
  assert.equal(resolveDefinitionRef(info, degree.name, [degree]), degree);
  assert.equal(resolveDefinitionRef(info, '_root_.' + degree.name, [degree]), degree);
});

test('local bindings and declarations shadow opened definitions', () => {
  const context = [{ text: 'open Canonical (WeylAlg)' }];
  assert.equal(resolveDefinitionRef({ ...info, context, bindings: ['WeylAlg'] }, 'WeylAlg', [weyl]), null);
  const local = { ...weyl, file: 'Proof.lean', name: 'Proof.WeylAlg' };
  assert.equal(resolveDefinitionRef({ ...info, context }, 'WeylAlg', [weyl, local]), local);
});

test('ambiguous and unsupported opens do not create misleading definition links', () => {
  const other = { ...weyl, name: 'Other.WeylAlg' };
  assert.equal(resolveDefinitionRef({ ...info, context: [{ text: 'open Canonical Other' }] }, 'WeylAlg', [weyl, other]), null);
  for (const text of ['open Canonical (OtherName)', 'open Canonical hiding WeylAlg', 'open scoped Canonical']) {
    assert.equal(resolveDefinitionRef({ ...info, context: [{ text }] }, 'WeylAlg', [weyl]), null);
  }
  assert.equal(resolveDefinitionRef(info, 'WeylAlg', [weyl]), null);
});
