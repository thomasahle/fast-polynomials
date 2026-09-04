// Plain-node test for the Belaga scheme compiler (no framework).
// Run: node website/test/belaga.test.js   -> exit 0 on success, 1 on failure.
//
// Belaga's scheme (0.5) has exactly n parameters for the n coefficients of a
// monic polynomial: a_1 is rational and the other a's are the roots of a
// degree-(l-1) polynomial B fixed by the input, so (Pan 1966) the parameters
// are in general COMPLEX.  The compiler must therefore succeed on every
// polynomial (the site's e^x, ln(1+x), sqrt(1+x) examples at every degree
// 3..20, and random polynomials up to degree 24), report complex parameters
// precisely, and its chains - complex or not - must evaluate the polynomial.
// Costs: ceil(n/2) multiplications and n + 1 additions for a monic input.
import { compileBelaga } from '../js/methods/belaga.js';
import { examplesFor } from '../js/uistate.js';
import { parsePoly } from '../js/polyparse.js';

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

// independent complex-arithmetic evaluator for the emitted lines
// (constants are real literals or "(a+bi)" / "(a-bi)" literals)
const Cx = (re, im = 0) => ({ re, im });
const add = (a, b) => Cx(a.re + b.re, a.im + b.im);
const sub = (a, b) => Cx(a.re - b.re, a.im - b.im);
const mul = (a, b) => Cx(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
function evalChain(lines, x) {
  const env = Object.create(null);
  env.x = Cx(x);
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
      if (c === '+' || c === '-') { i++; const t = term(); v = c === '+' ? add(v, t) : sub(v, t); }
      else return v;
    }
  }
  function term() {
    let v = factor();
    for (;;) { ws(); if (src[i] === '*') { i++; v = mul(v, factor()); } else return v; }
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
      const num = /^\d+(?:\.\d+)?(?:[eE][+-]?\d+)?i?/.exec(rest);
      if (num) {
        i += num[0].length;
        v = num[0].endsWith('i') ? Cx(0, parseFloat(num[0].slice(0, -1))) : Cx(parseFloat(num[0]));
      } else {
        const id = /^[A-Za-z_]\w*/.exec(rest);
        if (!id) throw new Error('bad atom in: ' + src);
        if (!(id[0] in env)) throw new Error('undefined wire ' + id[0] + ' in: ' + src);
        i += id[0].length; v = env[id[0]];
      }
    }
    return neg ? Cx(-v.re, -v.im) : v;
  }
  const v = expr();
  ws();
  if (i !== src.length) throw new Error('trailing input in: ' + src);
  return v;
}

function checkWellFormed(r, n, label) {
  if (!Array.isArray(r.lines) || r.lines.length === 0) return bad(label + ': lines not a nonempty array');
  const seen = new Set(['x']);
  let mulLines = 0, complex = false;
  for (const ln of r.lines) {
    if (typeof ln.lhs !== 'string' || !/^[A-Za-z_]\w*$/.test(ln.lhs))
      return bad(label + ': bad lhs ' + JSON.stringify(ln.lhs));
    if (typeof ln.rhs !== 'string' || ln.rhs.length === 0)
      return bad(label + ': bad rhs on ' + ln.lhs);
    if (typeof ln.mul !== 'boolean') return bad(label + ': mul not boolean on ' + ln.lhs);
    if (seen.has(ln.lhs)) return bad(label + ': duplicate lhs ' + ln.lhs);
    seen.add(ln.lhs);
    if (ln.mul) mulLines++;
    if (/\di\)/.test(ln.rhs)) complex = true;
    const stars = (ln.rhs.match(/\*/g) || []).length;
    if (ln.mul !== (stars > 0) || stars > 1)
      return bad(label + ': mul flag/star mismatch on ' + ln.lhs + ': ' + ln.rhs);
  }
  if (r.lines[r.lines.length - 1].lhs !== 'P') return bad(label + ': last lhs is not P');
  if (mulLines !== r.mults) return bad(label + ': mults field != number of mul lines');
  if (r.exact !== false) return bad(label + ': exact should be false');
  if (r.preprocessing !== 'real' && r.preprocessing !== 'complex')
    return bad(label + ': bad preprocessing ' + r.preprocessing);
  if (complex !== (r.preprocessing === 'complex'))
    return bad(label + `: preprocessing '${r.preprocessing}' but complex constants ${complex ? 'present' : 'absent'}`);
  if (r.preprocessing === 'complex' && !/needs complex parameters for this polynomial/.test(r.note))
    return bad(label + ': complex parameters must be explained in the note');
  if (n <= 5 && r.preprocessing !== 'real') return bad(label + ': preprocessing is rational for n <= 5');
  if (!(r.maxRelError <= 1e-6)) return bad(label + ': maxRelError ' + r.maxRelError + ' > 1e-6');
  // Belaga's scheme (0.5) uses n + 1 additions (1 for y = x(x + a_1), 4 for
  // s_2, 2 per further s_k, 1 for a_n when n is odd): Pan 1966 states that it
  // attains the lower bound of n additions "to within one addition".
  if (r.adds > n + 1) return bad(label + `: adds ${r.adds} > n+1`);
  return true;
}

// The chain evaluates the polynomial (over C when its constants are complex):
// error below 1e-5 |p(x)| away from the roots of p and below 1e-8 S(x) near
// them, S(x) = sum |p_i| max(1,|x|)^i.
function checkNumeric(r, coeffs, label, xs) {
  for (const x of xs) {
    let got;
    try { got = evalChain(r.lines, x); }
    catch (e) { return bad(label + ': chain evaluation error: ' + e.message); }
    const want = hornerReal(coeffs, x);
    let scale = 0, xp = 1;
    const ax = Math.max(1, Math.abs(x));
    for (let i = 0; i < coeffs.length; i++) { scale += Math.abs(coeffs[i]) * xp; xp *= ax; }
    const denom = Math.max(Math.abs(want), 1e-3 * scale, 1e-300);
    if (!(Math.hypot(got.re - want, got.im) / denom <= 1e-5))
      return bad(label + ` at x=${x}: got ${got.re}${got.im ? '+' + got.im + 'i' : ''} want ${want}`);
  }
  return true;
}
const FIXED_XS = [-1.7, -0.3, 0.9, 1.6, 2.5];
const randomXs = k => Array.from({ length: k }, () => rnd() * 6 - 3).concat([rnd() * 4 + 3, -(rnd() * 4 + 3)]);

// ---- the site's example polynomials, degrees 3..20: every one must compile ----
let exampleFails = 0, exampleCount = 0, exampleComplex = 0;
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
    try { r = compileBelaga(fl); }
    catch (e) { exampleFails++; bad(label + ': ' + e.message.slice(0, 100)); continue; }
    if (r.preprocessing === 'complex') exampleComplex++;
    if (r.mults !== Math.ceil(n / 2))
      bad(label + `: mults ${r.mults} != ceil(n/2) = ${Math.ceil(n / 2)}`);
    checkWellFormed(r, n, label);
    checkNumeric(r, fl, label, FIXED_XS.concat(randomXs(8)));
  }
}
console.log(`site examples (e^x, ln(1+x), sqrt(1+x); n = 3..20): ${exampleCount - exampleFails}/${exampleCount} compiled, ${exampleComplex} with complex parameters`);

// ---- random monic polynomials, n = 3..24 ----
const PER_DEGREE = 6;
let attempts = 0, failures = 0, complexCount = 0;
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
    try { r = compileBelaga(coeffs); }
    catch (e) {
      failures++;
      const k = `n=${n}: ${e.message.slice(0, 60)}`;
      failMsgs.set(k, (failMsgs.get(k) || 0) + 1);
      continue;
    }
    bandStats[band][0]++;
    if (r.preprocessing === 'complex') complexCount++;
    if (r.mults !== Math.ceil(n / 2))
      bad(label + `: mults ${r.mults} != ceil(n/2) = ${Math.ceil(n / 2)}`);
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
  ['x^6 - x^5 + x^2 - x', [0, -1, 1, 0, 0, -1, 1]],
];
let sparseOk = 0;
for (const [nm, coeffs] of sparse) {
  const n = coeffs.length - 1;
  attempts++;
  let r;
  try { r = compileBelaga(coeffs); }
  catch (e) {
    failures++;
    failMsgs.set(nm + ': ' + e.message.slice(0, 60), 1);
    continue;
  }
  sparseOk++;
  if (r.mults > Math.ceil(n / 2))
    bad(nm + `: mults ${r.mults} > ceil(n/2)`);
  checkWellFormed(r, n, nm);
  checkNumeric(r, coeffs, nm, FIXED_XS.concat([0, 1e-3], randomXs(4)));
}

// ---- error cases must throw cleanly ----
for (const [nm, badInput] of [
  ['non-monic', [1, 2, 3, 2]],
  ['too small', [1, 1, 1]],
  ['non-finite', [NaN, 0, 0, 1]],
]) {
  let threw = false;
  try { compileBelaga(badInput); } catch (e) { threw = e instanceof Error && e.message.length > 5; }
  if (!threw) bad('expected a clear Error for ' + nm + ' input');
}

// ---- report ----
console.log('--- Belaga scheme test ---');
for (const band of ['3-8', '9-16', '17-24']) {
  const [ok, total] = bandStats[band];
  console.log(`degrees ${band}: ${ok}/${total} compiled (${(100 * ok / total).toFixed(1)}%)`);
}
console.log(`near-sparse: ${sparseOk}/${sparse.length} compiled`);
console.log(`total: ${attempts - failures}/${attempts} compiled (${complexCount} random ones with complex parameters), ${failures} non-convergent/inaccurate`);
if (failMsgs.size) {
  console.log('failure summary:');
  for (const [k, v] of failMsgs) console.log(`  ${v}x ${k}`);
}
if (failures) bad(`${failures} polynomial(s) failed to compile - Belaga's scheme exists for every polynomial`);
if (hardFails) { console.log(`${hardFails} hard failure(s)`); process.exit(1); }
console.log('BELAGA PASS');
