// Plain-node tests for Pan's real schemes (STOC 1978, Theorems 8 and 10).
// Coverage is explicit: degree 8, odd degrees 9, 11, 13, and 15, an even
// lift, non-monic inputs, and both input and internal radix shifts.

import { compilePan1978Real } from '../js/methods/pan1978real.js';
import { verifyLines } from '../js/methods/motzkin.js';
import { buildGraphFromLines } from '../js/graph.js';
import { buildComparisons } from '../js/compare.js';
import { Q } from '../js/field.js';
import { Rat } from '../js/rat.js';

let failures = 0;
const check = (ok, msg) => { if (!ok) { failures++; console.log(`FAIL: ${msg}`); } };

const alternatingLog = n => Array.from({ length: n + 1 }, (_, i) =>
  i === 0 ? 0 : (i % 2 ? 1 : -1) / i);

const targets = [
  ['degree 9 alternating log', alternatingLog(9)],
  ['degree 9 exp with conditioned leading coefficient',
    [1, 1, 1 / 2, 1 / 6, 1 / 24, 1 / 120, 1 / 720, 1 / 5040, 1 / 40320, 1 / 362880]],
  ['degree 9 nontrivial radix shift', [55, 98, -70, -27, 16, 59, 102, -66, -230, -1.2]],
  ['degree 11 deterministic non-monic', Array.from({ length: 12 }, (_, i) =>
    i === 11 ? 1.7 : ((i * 7 + 11) % 17 - 8) / (i % 4 + 1))],
  ['degree 13 alternating log', alternatingLog(13)],
  ['degree 15 deterministic non-monic', Array.from({ length: 16 }, (_, i) =>
    i === 15 ? 1.7 : ((i * 7 + 15) % 17 - 8) / (i % 4 + 1))],
];

for (const [label, coeffs] of targets) {
  const started = performance.now();
  let r;
  try { r = compilePan1978Real(coeffs); }
  catch (e) { check(false, `${label}: ${e.message}`); continue; }
  const n = coeffs.length - 1, err = verifyLines(r.lines, coeffs);
  check(r.mults === (n + 1) / 2, `${label}: ${r.mults}M, expected ${(n + 1) / 2}M`);
  check(r.adds <= n + 4, `${label}: ${r.adds}A exceeds Pan's ${n + 4}A bound`);
  check(r.lines.filter(line => line.mul).length === r.mults, `${label}: multiplication flags disagree`);
  check(buildGraphFromLines(r.lines).nodes.filter(node => node.kind === 'mul').length === r.mults,
    `${label}: graph counted the radix shift as a multiplication`);
  check(r.lines.at(-1)?.lhs === 'P', `${label}: final wire is not P`);
  check(!r.lines.some(line => /\bi\b|[0-9]i\)/.test(line.rhs)), `${label}: a non-real constant was emitted`);
  check(!r.lines.some(line => line.lhs === 'P\u0303'), `${label}: non-monic input acquired a cleanup multiply`);
  check(err <= 1e-6 && r.maxRelError <= 1e-6, `${label}: emitted-chain relative error ${err}`);
  check(r.preprocessing === 'real' && r.exact === false, `${label}: preprocessing label is not real/numeric`);
  const inputShifts = r.lines.filter(line => line.lhs === 'z' && line.radixShift !== undefined).length;
  check(r.radixShifts === inputShifts + (r.radixExponent > 0 ? 1 : 0),
    `${label}: radix-shift metadata disagrees`);
  console.log(`${label}: ${r.mults}M ${r.adds}A, shift 2^${r.radixExponent}, ` +
    `error ${err.toExponential(2)}, ${(performance.now() - started).toFixed(0)} ms`);
}

for (const coeffs of [[1], [1, ...Array(6).fill(0), 1]]) {
  let message = '';
  try { compilePan1978Real(coeffs); } catch (e) { message = e.message; }
  check(message.length > 0, `unsupported degree ${coeffs.length - 1} did not throw`);
}

for (const [label, coeffs, wantM] of [
  ['degree 8 monic', [1, 0, 0, 0, 0, 0, 0, 0, 1], 4],
  ['degree 8 non-monic', [1, 2, -3, 4, -5, 6, -7, 8, 2.3], 5],
  ['degree 10 even lift', [1, -2, 3, -4, 5, -6, 7, -8, 9, -10, 1.2], 6],
]) {
  let r;
  try { r = compilePan1978Real(coeffs); }
  catch (e) { check(false, `${label}: ${e.message}`); continue; }
  check(r.mults === wantM, `${label}: ${r.mults}M, expected ${wantM}M`);
  check(verifyLines(r.lines, coeffs) <= 1e-6, `${label}: chain did not verify`);
}

{
  const coeffs = [Rat.ZERO, ...Array.from({ length: 13 }, (_, j) =>
    new Rat(BigInt((j + 1) % 2 ? 1 : -1), BigInt(j + 1)))];
  const row = buildComparisons(coeffs, Q, 'Q').find(r => r.name === 'Pan');
  check(row?.ok && row.mults === 7 && row.adds === 17,
    `comparison row is not the expected 7M/17A real scheme: ${row?.note ?? 'missing'}`);
  check(row?.preprocessing === 'real algebraic system (numeric)',
    'comparison row does not distinguish real from complex preprocessing');
  check(row.mathText.split('\n').slice(0, -1).every(line => line.includes(' * ')),
    'Pan factored form contains a non-product intermediate line');
}

if (failures) process.exit(1);
console.log(`PAN 1978 REAL PASSES: ${targets.length} stated targets verified`);
