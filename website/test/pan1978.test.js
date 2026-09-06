// Plain-node tests for Pan's 1978 odd-degree schemes.
//
// Coverage is deliberately explicit: one non-monic target in each tested
// degree 11, 13, 15, 19 and 23.  The degree-13 target is the alternating
// logarithm polynomial from the motivating report.  Each literal emitted
// chain is reparsed by verifyLines and checked at its 69 real sample points.
// Complex-coefficient targets ({re, im} arrays) in degrees 11, 13, 15 and 19
// are checked by verifyLinesComplex at real and non-real sample points.

import { compilePan1978 } from '../js/methods/pan1978.js';
import { verifyLines, verifyLinesComplex } from '../js/methods/motzkin.js';
import { COMPLEX_SRC } from '../js/tokens.js';

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

// degrees below 11 are refused with the one-sentence pointer to Knuth–Eve
for (const coeffs of [[1, ...Array(8).fill(0), 1], [1, ...Array(9).fill(0), 1], [1, 2], []]) {
  let message = '';
  try { compilePan1978(coeffs); } catch (e) { message = e.message; }
  const n = coeffs.length - 1;
  check(/complex schemes start at degree 11 \(scheme \(4\); family \(3\) from 13\); Knuth–Eve and Belaga give ⌊n\/2⌋\+1 multiplications for a monic polynomial here/.test(message),
    `degree ${n}: low-degree message is not the stated sentence (${message})`);
  check((message.match(/[.!?](\s|$)/g) ?? []).length === 1, `degree ${n}: low-degree message is not one sentence (${message})`);
}

// ---- complex coefficients: {re, im} arrays, verified by verifyLinesComplex ----
// The only complex constant token in the chain text is fmtC's "(re+imi)";
// a real constant stays a plain number and no bare "i" appears anywhere.
const COMPLEX_TOKEN = new RegExp(COMPLEX_SRC, 'g');   // the canonical token of js/tokens.js
const complexTargets = [
  ['degree 11 complex', Array.from({ length: 12 }, (_, i) =>
    ({ re: (i % 2 ? -1 : 1) * (i + 2) / 7, im: i === 11 ? 1.5 : ((i * 5) % 7 - 3) / 4 }))],
  // ln(1 + ix)/i: the alternating logarithm series with the coefficient of x^k
  // multiplied by i^(k-1), so half the coefficients are purely imaginary
  ['degree 13 twisted alternating log', Array.from({ length: 14 }, (_, k) => {
    if (k === 0) return { re: 0, im: 0 };
    const ik = [[1, 0], [0, 1], [-1, 0], [0, -1]][(k - 1) % 4], s = (k % 2 ? 1 : -1) / k;
    return { re: ik[0] * s, im: ik[1] * s };
  })],
  ...[15, 19].map(n => [`degree ${n} complex`, Array.from({ length: n + 1 }, (_, i) =>
    ({ re: ((i * 11 + n) % 29 - 14) / (1 + i % 5), im: ((i * 7 + 3) % 11 - 5) / (2 + i % 3) }))]),
];
for (const [label, coeffs] of complexTargets) {
  let r;
  const started = performance.now();
  try { r = compilePan1978(coeffs); }
  catch (e) { check(false, `${label}: ${e.message}`); continue; }
  const n = coeffs.length - 1, err = verifyLinesComplex(r.lines, coeffs);
  check(r.mults === (n + 1) / 2, `${label}: ${r.mults} multiplications, expected ${(n + 1) / 2}`);
  check(r.adds <= n + 2, `${label}: ${r.adds} additions, expected at most ${n + 2}`);
  check(r.lines.filter(line => line.mul).length === r.mults, `${label}: line multiplication flags disagree`);
  check(r.lines.at(-1)?.lhs === 'P', `${label}: final wire is not P`);
  check(err <= 1e-6 && r.maxRelError <= 1e-6, `${label}: emitted-chain relative error ${err} (reported ${r.maxRelError})`);
  check(r.preprocessing === 'complex' && r.preprocessingLabel === 'complex algebraic system (numeric)',
    `${label}: complex preprocessing is not labelled (${r.preprocessing}, ${r.preprocessingLabel})`);
  check(/complex coefficients/.test(r.note), `${label}: note does not mention the complex coefficients`);
  const text = r.lines.map(line => line.rhs).join('\n');
  check(COMPLEX_TOKEN.test(text), `${label}: no canonical complex constant token in the chain`);
  check(!/i/.test(text.replace(COMPLEX_TOKEN, '')), `${label}: a bare i outside the canonical token`);
  console.log(`${label}: ${r.mults}M ${r.adds}A, error ${err.toExponential(2)}, ` +
    `${(performance.now() - started).toFixed(0)} ms`);
}

// ---- even degrees >= 12: P = x·Q_{n-1} + a_0 on top of the odd scheme ----
const evenReal = [12, 14, 16].map(n => [`degree ${n} even real`,
  Array.from({ length: n + 1 }, (_, i) =>
    i === n ? (n % 4 === 0 ? 1.75 : -0.875) : ((i * 13 + n) % 31 - 15) / (1 + i % 4))]);
const evenComplex = [12, 14, 16].map(n => [`degree ${n} even complex`,
  Array.from({ length: n + 1 }, (_, i) =>
    ({ re: ((i * 13 + n) % 31 - 15) / (1 + i % 4), im: ((i * 5 + 1) % 13 - 6) / (2 + i % 3) }))]);
for (const [label, coeffs] of [...evenReal, ...evenComplex]) {
  let r;
  const started = performance.now();
  try { r = compilePan1978(coeffs); }
  catch (e) { check(false, `${label}: ${e.message}`); continue; }
  const n = coeffs.length - 1, complex = typeof coeffs[0] === 'object';
  const err = complex ? verifyLinesComplex(r.lines, coeffs) : verifyLines(r.lines, coeffs);
  check(r.mults === n / 2 + 1, `${label}: ${r.mults} multiplications, expected ${n / 2 + 1}`);
  check(r.adds <= n + 2, `${label}: ${r.adds} additions, expected at most ${n + 2}`);
  check(r.lines.filter(line => line.mul).length === r.mults, `${label}: line multiplication flags disagree`);
  const last = r.lines.at(-1), lower = r.lines.at(-2);
  check(last?.lhs === 'P' && last.mul && /^x \* Q [+-] /.test(last.rhs), `${label}: final line is not P = x * Q + a_0 (${last?.rhs})`);
  check(lower?.lhs === 'Q' && lower.mul, `${label}: the odd scheme's output was not renamed Q`);
  check(r.lines.filter(line => line.lhs === 'P').length === 1, `${label}: more than one P line`);
  check(err <= 1e-6 && r.maxRelError <= 1e-6, `${label}: emitted-chain relative error ${err} (reported ${r.maxRelError})`);
  check(/^Pan even-degree reduction P\(x\) = x·Q_\d+\(x\) \+ a_0, followed by Pan 1978 scheme/.test(r.note) &&
    new RegExp(`Q_${n - 1}\\(x\\)`).test(r.note), `${label}: note (${r.note.slice(0, 80)})`);
  check(r.exact === false && /algebraic system \(numeric\)/.test(r.preprocessingLabel), `${label}: numeric preprocessing is not labelled`);
  if (complex) {
    check(r.preprocessing === 'complex' && r.preprocessingLabel === 'complex algebraic system (numeric)',
      `${label}: complex preprocessing is not labelled (${r.preprocessing}, ${r.preprocessingLabel})`);
    const text = r.lines.map(line => line.rhs).join('\n');
    check(COMPLEX_TOKEN.test(last.rhs), `${label}: a_0 is not printed as the canonical complex token (${last.rhs})`);
    check(!/i/.test(text.replace(COMPLEX_TOKEN, '')), `${label}: a bare i outside the canonical token`);
  }
  console.log(`${label}: ${r.mults}M ${r.adds}A height ${r.height}, error ${err.toExponential(2)}, ` +
    `${(performance.now() - started).toFixed(0)} ms`);
}
// a_0 = 0: the lift is the bare product x * Q, one multiplication and no addition more
{
  const [, odd] = targets[0];
  const lower = compilePan1978(odd), r = compilePan1978([0, ...odd]);
  check(r.lines.at(-1)?.rhs === 'x * Q' && r.mults === lower.mults + 1 && r.adds === lower.adds &&
    r.height === lower.height + 1, `zero constant lift: ${r.lines.at(-1)?.rhs}, ${r.mults}M ${r.adds}A height ${r.height}`);
  check(JSON.stringify(r.lines.slice(0, -1).map(l => l.rhs)) === JSON.stringify(lower.lines.map(l => l.rhs)),
    'zero constant lift: the odd chain underneath is not the odd compile');
  check(verifyLines(r.lines, [0, ...odd]) <= 1e-6, 'zero constant lift: chain does not verify');
}

// {re, im: 0} coefficients take the real path: byte-identical to plain numbers
{
  const [, coeffs] = targets[0];
  const a = compilePan1978(coeffs), b = compilePan1978(coeffs.map(re => ({ re, im: 0 })));
  check(JSON.stringify(a) === JSON.stringify(b), 'real {re, im: 0} input differs from the plain-number input');
}
for (const [nm, badInput] of [
  ['complex zero leading coefficient', [...Array(11).fill({ re: 1, im: 1 }), { re: 0, im: 0 }]],
  ['non-finite imaginary part', [{ re: 1, im: NaN }, ...Array(11).fill(1)]],
]) {
  let message = '';
  try { compilePan1978(badInput); } catch (e) { message = e.message; }
  check(message.length > 0, `${nm} did not throw`);
}

if (failures) process.exit(1);
console.log(`PAN 1978 PASSES: ${targets.length} real and ${complexTargets.length} complex odd targets, ` +
  `${evenReal.length + evenComplex.length} even lifts verified`);
