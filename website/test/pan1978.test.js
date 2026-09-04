// Plain-node tests for Pan's 1978 odd-degree schemes.
//
// Coverage is deliberately explicit: one non-monic target in each tested
// degree 11, 13, 15, 19 and 23.  The degree-13 target is the alternating
// logarithm polynomial from the motivating report.  Each literal emitted
// chain is reparsed by verifyLines and checked at its 69 real sample points.

import { compilePan1978 } from '../js/methods/pan1978.js';
import { verifyLines } from '../js/methods/motzkin.js';

let failures = 0;
const check = (ok, msg) => { if (!ok) { failures++; console.log(`FAIL: ${msg}`); } };

const targets = [
  ['degree 11 deterministic', Array.from({ length: 12 }, (_, i) =>
    i === 11 ? 2.5 : (i % 2 ? -1 : 1) * (i + 2) / 7)],
  ['degree 13 alternating log', [
    0, 1, -1 / 2, 1 / 3, -1 / 4, 1 / 5, -1 / 6,
    1 / 7, -1 / 8, 1 / 9, -1 / 10, 1 / 11, -1 / 12, 1 / 13,
  ]],
  ...[15, 19, 23].map(n => [`degree ${n} deterministic`,
    Array.from({ length: n + 1 }, (_, i) =>
      i === n ? (n % 4 === 1 ? -0.625 : 1.375) : ((i * 11 + n) % 29 - 14) / (1 + i % 5))]),
];

for (const [label, coeffs] of targets) {
  let r;
  const started = performance.now();
  try { r = compilePan1978(coeffs); }
  catch (e) { check(false, `${label}: ${e.message}`); continue; }
  const n = coeffs.length - 1, err = verifyLines(r.lines, coeffs);
  check(r.mults === (n + 1) / 2, `${label}: ${r.mults} multiplications, expected ${(n + 1) / 2}`);
  check(r.adds <= n + 2, `${label}: ${r.adds} additions, expected at most ${n + 2}`);
  check(r.lines.filter(line => line.mul).length === r.mults, `${label}: line multiplication flags disagree`);
  check(r.lines.at(-1)?.lhs === 'P', `${label}: final wire is not P`);
  check(!r.lines.some(line => line.lhs === 'P\u0303' || /leading-coefficient scale/.test(line.rhs)),
    `${label}: non-monic target acquired a cleanup multiplication`);
  check(err <= 1e-6 && r.maxRelError <= 1e-6, `${label}: emitted-chain relative error ${err}`);
  check(r.exact === false && /algebraic system \(numeric\)/.test(r.preprocessingLabel),
    `${label}: numeric algebraic preprocessing is not labelled`);
  console.log(`${label}: ${r.mults}M ${r.adds}A, error ${err.toExponential(2)}, ` +
    `${(performance.now() - started).toFixed(0)} ms`);
}

for (const coeffs of [[1, ...Array(8).fill(0), 1], [1, ...Array(11).fill(0), 1]]) {
  let message = '';
  try { compilePan1978(coeffs); } catch (e) { message = e.message; }
  check(message.length > 0, `unsupported degree ${coeffs.length - 1} did not throw`);
}

if (failures) process.exit(1);
console.log(`PAN 1978 PASSES: ${targets.length} stated targets verified`);
