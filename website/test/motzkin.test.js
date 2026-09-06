// Plain-node test for the Motzkin/Eve adaptation compiler (no framework).
// Run: node website/test/motzkin.test.js   -> exit 0 on success, 1 on failure.
//
// Knuth's Theorem E promises a REAL parameterisation for every real
// polynomial, so the compiler must never emit complex constants and must
// succeed on EVERY polynomial: the e^x, ln(1+x), sqrt(1+x) Taylor polynomials
// at every degree 3..20 the site offers, random polynomials up to degree 24
// (the site's maximum) and a few sparse ones.  The chain is evaluated in
// doubles, and the rounding error of an adapted chain grows like
// (|x| + 2|c|)^n with the degree (its intermediate values are as large as
// u(-x - 2c) for the shift c even where u(x) is small), so the tolerance on
// the compiler's own measured error is 1e-6 up to degree 20 and 1e-5 for
// degrees 21..24, where the best achievable chains for random coefficients in
// [-10, 10] reach a few 1e-6 (the compiler picks the smallest admissible
// shift, decided exactly by Sturm sequences, and searches the peel order).
import { compileMotzkin, verifyLines, verifyLinesComplex, SAMPLE_ZS } from '../js/methods/motzkin.js';
import { examplesFor } from '../js/uistate.js';
import { parsePoly } from '../js/polyparse.js';
import { hasComplexToken } from '../js/tokens.js';

let hardFails = 0;
const bad = msg => { console.log('FAIL: ' + msg); hardFails++; };

// deterministic RNG (mulberry32)
let state = 0xC0FFEE;
function rnd() {
  state |= 0; state = (state + 0x6D2B79F5) | 0;
  let t = Math.imul(state ^ (state >>> 15), 1 | state);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
}

function hornerReal(p, x) {
  let v = 0;
  for (let i = p.length - 1; i >= 0; i--) v = v * x + p[i];
  return v;
}

// independent real-arithmetic evaluator for the emitted lines
function evalChainReal(lines, x) {
  const env = Object.create(null);
  env.x = x;
  for (const ln of lines) env[ln.lhs] = evalRhs(ln.rhs, env);
  return env.P;
}
function evalRhs(src, env) {
  let i = 0;
  const ws = () => { while (i < src.length && src[i] === ' ') i++; };
  function expr() {
    let v = term();
    for (;;) {
      ws();
      const c = src[i];
      if (c === '+' || c === '-') { i++; const t = term(); v = c === '+' ? v + t : v - t; }
      else return v;
    }
  }
  function term() {
    let v = factor();
    for (;;) { ws(); if (src[i] === '*') { i++; v = v * factor(); } else return v; }
  }
  function factor() {
    ws();
    let neg = false;
    if (src[i] === '-') { neg = true; i++; ws(); }
    let v;
    if (src[i] === '(') {
      i++; v = expr(); ws();
      if (src[i] !== ')') throw new Error('missing ) in: ' + src);
      i++;
    } else {
      const rest = src.slice(i);
      const num = /^\d+(?:\.\d+)?(?:[eE][+-]?\d+)?/.exec(rest);
      if (num && !rest.slice(num[0].length).startsWith('i')) {
        i += num[0].length; v = parseFloat(num[0]);
      } else {
        const id = /^[A-Za-z_]\w*/.exec(rest);
        if (!id) throw new Error('bad atom in: ' + src);
        if (!(id[0] in env)) throw new Error('undefined wire ' + id[0] + ' in: ' + src);
        i += id[0].length; v = env[id[0]];
      }
    }
    return neg ? -v : v;
  }
  const v = expr();
  ws();
  if (i !== src.length) throw new Error('trailing input in: ' + src);
  return v;
}

// Tolerance on the compiler's reported max relative error (see the header).
const tol = n => (n <= 20 ? 1e-6 : 1e-5);

function checkWellFormed(r, n, label) {
  if (!Array.isArray(r.lines) || r.lines.length === 0) return bad(label + ': lines not a nonempty array');
  const seen = new Set(['x']);
  let mulLines = 0;
  for (const ln of r.lines) {
    if (typeof ln.lhs !== 'string' || !/^[A-Za-z_]\w*$/.test(ln.lhs))
      return bad(label + ': bad lhs ' + JSON.stringify(ln.lhs));
    if (typeof ln.rhs !== 'string' || ln.rhs.length === 0)
      return bad(label + ': bad rhs on ' + ln.lhs);
    if (typeof ln.mul !== 'boolean') return bad(label + ': mul not boolean on ' + ln.lhs);
    if (seen.has(ln.lhs)) return bad(label + ': duplicate lhs ' + ln.lhs);
    seen.add(ln.lhs);
    if (ln.mul) mulLines++;
    const stars = (ln.rhs.match(/\*/g) || []).length;
    if (ln.mul !== (stars > 0) || stars > 1)
      return bad(label + ': mul flag/star mismatch on ' + ln.lhs + ': ' + ln.rhs);
    if (hasComplexToken(ln.rhs)) return bad(label + ': complex constant in a Motzkin-Eve chain: ' + ln.rhs);
  }
  if (r.lines[r.lines.length - 1].lhs !== 'P') return bad(label + ': last lhs is not P');
  if (mulLines !== r.mults) return bad(label + ': mults field != number of mul lines');
  if (r.exact !== false) return bad(label + ': exact should be false');
  if (r.preprocessing !== 'real') return bad(label + ': preprocessing must be real, got ' + r.preprocessing);
  if (!(r.maxRelError <= tol(n))) return bad(label + ': maxRelError ' + r.maxRelError + ' > ' + tol(n));
  if (r.adds > n + 1) return bad(label + `: adds ${r.adds} > n+1`);
  return true;
}

// The chain evaluates the polynomial: at every sample point the error is
// below 10 tol(n) |p(x)| away from the roots of p and below 1e-2 tol(n) S(x)
// near them, S(x) = sum |p_i| max(1,|x|)^i being the coefficient scale (an
// adapted chain has an absolute rounding error set by its constants, so a
// purely relative test at a root is meaningless).
function checkNumeric(r, coeffs, label, xs) {
  const n = coeffs.length - 1;
  for (const x of xs) {
    let got;
    try { got = evalChainReal(r.lines, x); }
    catch (e) { return bad(label + ': chain evaluation error: ' + e.message); }
    const want = hornerReal(coeffs, x);
    let scale = 0, xp = 1;
    const ax = Math.max(1, Math.abs(x));
    for (let i = 0; i < coeffs.length; i++) { scale += Math.abs(coeffs[i]) * xp; xp *= ax; }
    const denom = Math.max(Math.abs(want), 1e-3 * scale, 1e-300);
    if (!(Math.abs(got - want) / denom <= 10 * tol(n)))
      return bad(label + ` at x=${x}: got ${got} want ${want}`);
  }
  return true;
}
const FIXED_XS = [-1.7, -0.3, 0.9, 1.6, 2.5];
const randomXs = k => Array.from({ length: k }, () => rnd() * 6 - 3).concat([rnd() * 4 + 3, -(rnd() * 4 + 3)]);

// ---- the site's example polynomials, degrees 3..20: every one must compile ----
// (same float scaling as compare.js: coefficients as doubles, divided by the
// leading coefficient)
let exampleFails = 0, exampleCount = 0;
for (const key of ['exp', 'ln', 'sqrt']) {
  for (let n = 3; n <= 20; n++) {
    const ex = examplesFor('Q', n).find(e => e.key === key);
    const { coeffs } = parsePoly(ex.src);
    let fl = coeffs.map(c => Number(c.n) / Number(c.d));
    const lc = fl[fl.length - 1];
    fl = fl.map(v => v / lc);
    const label = `${key} n=${n}`;
    exampleCount++;
    let r;
    try { r = compileMotzkin(fl); }
    catch (e) { exampleFails++; bad(label + ': ' + e.message.slice(0, 100)); continue; }
    if (r.mults !== Math.floor(n / 2) + 1)
      bad(label + `: mults ${r.mults} != floor(n/2)+1 = ${Math.floor(n / 2) + 1}`);
    checkWellFormed(r, n, label);
    checkNumeric(r, fl, label, FIXED_XS.concat(randomXs(8)));
  }
}
console.log(`site examples (e^x, ln(1+x), sqrt(1+x); n = 3..20): ${exampleCount - exampleFails}/${exampleCount} compiled`);

// ---- random monic polynomials, n = 3..24 ----
const PER_DEGREE = 6;
let attempts = 0, failures = 0;
const bandStats = {};   // band -> [ok, total]
const bandOf = n => n <= 8 ? '3-8' : n <= 16 ? '9-16' : '17-24';
const failMsgs = new Map();

for (let n = 3; n <= 24; n++) {
  for (let t = 0; t < PER_DEGREE; t++) {
    const coeffs = Array.from({ length: n }, () => (rnd() * 20 - 10));
    coeffs.push(1);
    attempts++;
    const band = bandOf(n);
    bandStats[band] = bandStats[band] || [0, 0];
    bandStats[band][1]++;
    const label = `random n=${n} #${t}`;
    let r;
    try { r = compileMotzkin(coeffs); }
    catch (e) {
      failures++;
      const k = `n=${n}: ${e.message.slice(0, 60)}`;
      failMsgs.set(k, (failMsgs.get(k) || 0) + 1);
      continue;
    }
    bandStats[band][0]++;
    if (r.mults !== Math.floor(n / 2) + 1)
      bad(label + `: mults ${r.mults} != floor(n/2)+1 = ${Math.floor(n / 2) + 1}`);
    checkWellFormed(r, n, label);
    checkNumeric(r, coeffs, label, FIXED_XS.concat(randomXs(4)));
  }
}

// ---- near-sparse inputs ----
const sparse = [
  ['x^7+x+1', [1, 1, 0, 0, 0, 0, 0, 1]],
  ['x^5-2x+1', [1, -2, 0, 0, 0, 1]],
  ['x^11+x^2+1', [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
  ['x^16+x^3+x+1', [1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]],
  ['x^24+x+1', [1, 1].concat(Array(22).fill(0)).concat([1])],
];
let sparseOk = 0;
for (const [nm, coeffs] of sparse) {
  const n = coeffs.length - 1;
  attempts++;
  let r;
  try { r = compileMotzkin(coeffs); }
  catch (e) {
    failures++;
    failMsgs.set(nm + ': ' + e.message.slice(0, 60), 1);
    continue;
  }
  sparseOk++;
  if (r.mults > Math.floor(n / 2) + 1)
    bad(nm + `: mults ${r.mults} > floor(n/2)+1`);
  checkWellFormed(r, n, nm);
  checkNumeric(r, coeffs, nm, FIXED_XS.concat(randomXs(4)));
}

// ---- polynomials without constant term (x = 0 is a root; the verification
// scale must not vanish there) and with all roots already in the left
// half-plane (no shift needed) ----
for (const [nm, coeffs] of [
  ['x^6 - x^5 + x^2 - x', [0, -1, 1, 0, 0, -1, 1]],
  ['(x+1)^5 + x^2', [1, 5, 11, 10, 5, 1]],
]) {
  const n = coeffs.length - 1;
  let r;
  try { r = compileMotzkin(coeffs); }
  catch (e) { bad(nm + ': ' + e.message.slice(0, 80)); continue; }
  checkWellFormed(r, n, nm);
  checkNumeric(r, coeffs, nm, FIXED_XS.concat([0, 1e-3, -1e-3]));
}

// ---- error cases must throw cleanly ----
for (const [nm, badInput] of [
  ['non-monic', [1, 2, 3, 2]],
  ['too small', [1, 1, 1]],
  ['non-finite', [NaN, 0, 0, 1]],
]) {
  let threw = false;
  try { compileMotzkin(badInput); } catch (e) { threw = e instanceof Error && e.message.length > 5; }
  if (!threw) bad('expected a clear Error for ' + nm + ' input');
}

// ---- verifyLinesComplex: the verifier the complex-coefficient rows use ----
// Sample points off the real axis, complex Horner reference, |.|-relative
// error with the same 1e-3 S(z) floor as verifyLines.
{
  if (!SAMPLE_ZS.some(z => z.im !== 0)) bad('SAMPLE_ZS has no point with Im != 0');
  if (!SAMPLE_ZS.some(z => z.im === 0)) bad('SAMPLE_ZS has no real point');
  // x^2 + 1 = (x + i)(x - i): exact over C, and the roots +-i are sample points
  const good = [{ lhs: 'y', rhs: 'x + (0+1i)', mul: false }, { lhs: 'P', rhs: 'y * (x + (0-1i))', mul: true }];
  const e1 = verifyLinesComplex(good, [1, 0, 1]);
  if (!(e1 <= 1e-15)) bad(`verifyLinesComplex: (x+i)(x-i) vs x^2+1 gave ${e1}`);
  const e1r = verifyLines(good, [1, 0, 1]);
  if (!(e1r <= 1e-15)) bad(`verifyLines still accepts the complex chain for x^2+1: ${e1r}`);
  // the same chain is not x^2 - 1
  if (!(verifyLinesComplex(good, [-1, 0, 1]) > 0.1)) bad('verifyLinesComplex accepted a wrong chain');
  // complex coefficients: x^2 + (1+2i) x + i, coefficient arrays of {re, im}
  const cc = [{ re: 0, im: 1 }, { re: 1, im: 2 }, { re: 1, im: 0 }];
  const chain = [{ lhs: 'P', rhs: '(x + (1+2i)) * x + (0+1i)', mul: true }];
  const e2 = verifyLinesComplex(chain, cc);
  if (!(e2 <= 1e-15)) bad(`verifyLinesComplex: complex-coefficient chain gave ${e2}`);
  const wrong = [{ lhs: 'P', rhs: '(x + (1-2i)) * x + (0+1i)', mul: true }];
  if (!(verifyLinesComplex(wrong, cc) > 0.1)) bad('verifyLinesComplex accepted a conjugated constant');
  // plain numbers and {re, im: 0} are the same coefficients
  const e3 = verifyLinesComplex(good, [{ re: 1, im: 0 }, 0, { re: 1 }]);
  if (e3 !== e1) bad('verifyLinesComplex: {re, im} and plain-number coefficients disagree');
}

// ---- report ----
console.log('--- Motzkin/Eve adaptation test ---');
for (const band of ['3-8', '9-16', '17-24']) {
  const [ok, total] = bandStats[band];
  console.log(`degrees ${band}: ${ok}/${total} compiled (${(100 * ok / total).toFixed(1)}%)`);
}
console.log(`near-sparse: ${sparseOk}/${sparse.length} compiled`);
console.log(`total: ${attempts - failures}/${attempts} compiled, ${failures} non-convergent/inaccurate`);
if (failMsgs.size) {
  console.log('failure summary:');
  for (const [k, v] of failMsgs) console.log(`  ${v}x ${k}`);
}
if (failures) bad(`${failures} polynomial(s) failed to compile - the real parameterisation exists for every polynomial (Theorem E)`);
if (hardFails) { console.log(`${hardFails} hard failure(s)`); process.exit(1); }
console.log('MOTZKIN/EVE PASS');
