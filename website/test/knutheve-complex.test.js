// Plain-node test for the complex Knuth-Eve adaptation compiler (no framework).
// Run: node website/test/knutheve-complex.test.js   -> exit 0 on success, 1 on failure.
//
// Over C the scheme needs no real-rootedness shift, so the compiler must
// succeed on EVERY polynomial of degree 2..24: random real coefficients,
// random Gaussian coefficients, the e^x and e^{ix} Taylor chips, x^n - 1
// (an even polynomial at even n: no odd part, so no shift and one
// multiplication fewer), non-monic inputs (which get the scale line inside
// the compiler) and the raw, non-monic Taylor coefficients 1/k! and i^k/k!
// as the page's numeric row passes them.  The chain is re-evaluated here by
// an independent complex evaluator at points with Im != 0, every complex
// constant must be the canonical token "(re+imi)" of js/tokens.js, and the
// multiplication count is floor(n/2) + 1 (+1 when non-monic; -1 for an even
// polynomial).  A real polynomial whose nodes are distinct reals must yield
// a chain without any complex token.
import { compileKnuthEveComplex, verifyLinesComplex, polyRootsC } from '../js/methods/knutheve-complex.js';
import { COMPLEX_TOKEN, COMPLEX_SRC, hasComplexToken } from '../js/tokens.js';

const COMPLEX_TOKEN_RE = COMPLEX_TOKEN;
const COMPLEX_TOKEN_G = new RegExp(COMPLEX_SRC, 'g');

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

// ---- independent complex arithmetic and evaluator ----
const Z = (re, im = 0) => ({ re, im });
const zAdd = (a, b) => Z(a.re + b.re, a.im + b.im);
const zSub = (a, b) => Z(a.re - b.re, a.im - b.im);
const zMul = (a, b) => Z(a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re);
const zAbs = a => Math.hypot(a.re, a.im);
const asZ = v => (typeof v === 'number' ? Z(v) : Z(v.re, v.im));

function hornerZ(p, z) {
  let v = Z(0);
  for (let i = p.length - 1; i >= 0; i--) v = zAdd(zMul(v, z), asZ(p[i]));
  return v;
}

function evalChain(lines, z) {
  const env = Object.create(null);
  env.x = z;
  for (const ln of lines) env[ln.lhs] = evalRhs(ln.rhs, env);
  return env.P;
}
// token-based recursive descent: numbers (optionally suffixed i), wires, + - * ( )
function evalRhs(src, env) {
  const toks = src.match(/\d+(?:\.\d+)?(?:[eE][+-]?\d+)?i?|[A-Za-z_][\w\u0300-\u036f]*|[-+*()]/g) || [];
  if (toks.join('') !== src.replace(/ /g, '')) throw new Error('unlexable rhs: ' + src);
  let i = 0;
  function expr() {
    let v = term();
    while (toks[i] === '+' || toks[i] === '-') { const op = toks[i++]; const t = term(); v = op === '+' ? zAdd(v, t) : zSub(v, t); }
    return v;
  }
  function term() {
    let v = factor();
    while (toks[i] === '*') { i++; v = zMul(v, factor()); }
    return v;
  }
  function factor() {
    let neg = false;
    if (toks[i] === '-') { neg = true; i++; }
    let v;
    const t = toks[i++];
    if (t === '(') { v = expr(); if (toks[i++] !== ')') throw new Error('missing ) in: ' + src); }
    else if (/^\d/.test(t)) v = t.endsWith('i') ? Z(0, parseFloat(t.slice(0, -1))) : Z(parseFloat(t));
    else if (t in env) v = env[t];
    else throw new Error('undefined wire ' + t + ' in: ' + src);
    return neg ? Z(-v.re, -v.im) : v;
  }
  const v = expr();
  if (i !== toks.length) throw new Error('trailing input in: ' + src);
  return v;
}

const TOL = 1e-6;
const XS = [];
for (let k = 0; k < 24; k++) {
  const r = 0.3 + 0.35 * k, ang = 0.37 * k + 0.2;
  XS.push(Z(r * Math.cos(ang), r * Math.sin(ang)));
}
XS.push(Z(0), Z(1), Z(-1), Z(2.5), Z(-3), Z(0, 1), Z(0, -2), Z(3, 4), Z(-5, 0.5), Z(1, 10));

// ---- checks ----
const isZeroCoeff = v => (typeof v === 'number' ? v === 0 : v.re === 0 && v.im === 0);
/** An even polynomial (every odd-index coefficient zero) needs no b*y line. */
const evenPoly = coeffs => coeffs.length % 2 === 1 && coeffs.every((c, k) => k % 2 === 0 || isZeroCoeff(c));

function checkWellFormed(r, n, label, monic, coeffs) {
  if (!Array.isArray(r.lines) || r.lines.length === 0) return bad(label + ': lines not a nonempty array');
  const seen = new Set(['x']);
  let mulLines = 0;
  for (const ln of r.lines) {
    if (typeof ln.lhs !== 'string' || !/^[A-Za-z_][\w\u0303]*$/.test(ln.lhs))
      return bad(label + ': bad lhs ' + JSON.stringify(ln.lhs));
    if (typeof ln.rhs !== 'string' || ln.rhs.length === 0) return bad(label + ': bad rhs on ' + ln.lhs);
    if (typeof ln.mul !== 'boolean') return bad(label + ': mul not boolean on ' + ln.lhs);
    if (seen.has(ln.lhs)) return bad(label + ': duplicate lhs ' + ln.lhs);
    seen.add(ln.lhs);
    if (ln.mul) mulLines++;
    const stars = (ln.rhs.match(/\*/g) || []).length;
    if (ln.mul !== (stars > 0) || stars > 1)
      return bad(label + ': mul flag/star mismatch on ' + ln.lhs + ': ' + ln.rhs);
    // every complex constant is the canonical token, and nothing else mentions i
    const toks = ln.rhs.match(COMPLEX_TOKEN_G) || [];
    for (const t of toks) if (!COMPLEX_TOKEN_RE.test(t) || / /.test(t)) return bad(label + ': non-canonical token ' + t);
    const rest = ln.rhs.replace(COMPLEX_TOKEN_G, '#');
    if (/i/.test(rest)) return bad(label + ': stray i outside a canonical token: ' + ln.rhs);
    if (/\(#\)/.test(rest))
      return bad(label + ': doubly parenthesised token: ' + ln.rhs);
  }
  if (r.lines[r.lines.length - 1].lhs !== 'P') return bad(label + ': last lhs is not P');
  if (mulLines !== r.mults) return bad(label + ': mults field != number of mul lines');
  const want = Math.floor(n / 2) + 1 + (monic ? 0 : 1) - (evenPoly(coeffs) ? 1 : 0);
  if (r.mults !== want) return bad(label + `: mults ${r.mults} != ${want}`);
  if (r.exact !== false) return bad(label + ': exact should be false');
  if (r.preprocessing !== 'complex') return bad(label + ': preprocessing must be complex, got ' + r.preprocessing);
  if (r.preprocessingLabel !== 'complex roots (numeric)') return bad(label + ': preprocessingLabel ' + r.preprocessingLabel);
  if (typeof r.note !== 'string' || !r.note) return bad(label + ': missing note');
  if (!(r.maxRelError <= TOL)) return bad(label + ': maxRelError ' + r.maxRelError + ' > ' + TOL);
  if (r.adds > n + 1) return bad(label + `: adds ${r.adds} > n+1`);
  if (!(Number.isInteger(r.height) && r.height >= 1 && r.height <= r.mults))
    return bad(label + `: height ${r.height} not in 1..mults`);
  return true;
}

function checkNumeric(r, coeffs, label) {
  for (const z of XS) {
    let got;
    try { got = evalChain(r.lines, z); }
    catch (e) { return bad(label + ': chain evaluation error: ' + e.message); }
    const want = hornerZ(coeffs, z);
    let scale = 0, zp = 1;
    const az = Math.max(1, zAbs(z));
    for (let i = 0; i < coeffs.length; i++) { scale += zAbs(asZ(coeffs[i])) * zp; zp *= az; }
    const denom = Math.max(zAbs(want), 1e-3 * scale, 1e-300);
    if (!(zAbs(zSub(got, want)) / denom <= 10 * TOL))
      return bad(label + ` at z=(${z.re},${z.im}): got (${got.re},${got.im}) want (${want.re},${want.im})`);
  }
  // the module's own verifier agrees with its report
  const v = verifyLinesComplex(r.lines, coeffs);
  if (!(v <= TOL)) return bad(label + ': verifyLinesComplex ' + v + ' > ' + TOL);
  return true;
}

function runCase(coeffs, label, monic) {
  const n = coeffs.length - 1;
  let r;
  try { r = compileKnuthEveComplex(coeffs); }
  catch (e) { return bad(label + ': threw ' + e.message); }
  if (!checkWellFormed(r, n, label, monic, coeffs)) return false;
  return checkNumeric(r, coeffs, label);
}

// ---- families ----
const gauss = () => ({ re: Math.round((rnd() * 20 - 10) * 100) / 100, im: Math.round((rnd() * 20 - 10) * 100) / 100 });
const real = () => Math.round((rnd() * 20 - 10) * 100) / 100;
const fact = k => { let f = 1; for (let i = 2; i <= k; i++) f *= i; return f; };
const ipow = k => [Z(1), Z(0, 1), Z(-1), Z(0, -1)][k % 4];

let cases = 0;
for (let n = 2; n <= 24; n++) {
  // (a) random real coefficients, monic
  const pr = Array.from({ length: n }, real).concat([1]);
  runCase(pr, `real random n=${n}`, true); cases++;
  // (b) random Gaussian coefficients, monic
  const pg = Array.from({ length: n }, gauss).concat([{ re: 1, im: 0 }]);
  runCase(pg, `gaussian random n=${n}`, true); cases++;
  // (c) e^x Taylor: degree n-1 series plus x^n
  const ex = Array.from({ length: n }, (_, k) => 1 / fact(k)).concat([1]);
  runCase(ex, `exp Taylor n=${n}`, true); cases++;
  // (d) e^{ix} Taylor: i^k / k!, plus x^n
  const eix = Array.from({ length: n }, (_, k) => { const w = ipow(k); return { re: w.re / fact(k), im: w.im / fact(k) }; }).concat([{ re: 1, im: 0 }]);
  runCase(eix, `exp(ix) Taylor n=${n}`, true); cases++;
  // (e) x^n - 1: degenerate odd part for even n
  const cyc = Array.from({ length: n + 1 }, (_, k) => (k === 0 ? -1 : k === n ? 1 : 0));
  runCase(cyc, `x^n-1 n=${n}`, true); cases++;
  // (f) non-monic: Gaussian leading coefficient, and a real one
  const nmg = Array.from({ length: n }, gauss).concat([{ re: 2, im: -1 }]);
  runCase(nmg, `non-monic gaussian n=${n}`, false); cases++;
  const nmr = Array.from({ length: n }, real).concat([3]);
  runCase(nmr, `non-monic real n=${n}`, false); cases++;
}
// (g) the raw Taylor coefficients 1/k! and i^k/k! (non-monic, as compare.js's
// numericRow passes the e^x / e^{ix} chips): normalised to monic inside the
// compiler, the lower coefficients grow like n!/k!, which the degenerate-odd-part
// test must not mistake for a vanishing leading odd coefficient
for (let n = 2; n <= 19; n++) {
  const ex = Array.from({ length: n + 1 }, (_, k) => 1 / fact(k));
  runCase(ex, `raw exp Taylor n=${n}`, false); cases++;
  const eix = Array.from({ length: n + 1 }, (_, k) => { const w = ipow(k); return { re: w.re / fact(k), im: w.im / fact(k) }; });
  runCase(eix, `raw exp(ix) Taylor n=${n}`, false); cases++;
}

// sparse / special shapes
runCase([1, 0, 0, 0, 1], 'x^4+1', true); cases++;
runCase([{ re: 0, im: 1 }, 0, 0, 0, 0, 0, 1], 'x^6+i', true); cases++;
runCase([0, 0, 0, 0, 0, 0, 0, 1], 'x^7', true); cases++;
runCase([0, 1, 0, 0, 0, 0, 0, 0, 1], 'x^8+x', true); cases++;
runCase([1, { re: 0, im: 2 }, 1], 'x^2+2ix+1 (double root -i)', true); cases++;

// base cases keep the row usable at every degree
{
  const r0 = compileKnuthEveComplex([{ re: 2, im: -3 }]);
  if (r0.mults !== 0 || r0.lines[0].rhs !== '(2-3i)') bad('degree 0: ' + JSON.stringify(r0.lines));
  const r1 = compileKnuthEveComplex([{ re: 0, im: 1 }, 1]);
  if (r1.mults !== 0 || r1.lines[0].rhs !== 'x + (0+1i)') bad('degree 1 monic: ' + JSON.stringify(r1.lines));
  const r1s = compileKnuthEveComplex([1, { re: 0, im: 2 }]);
  if (r1s.mults !== 1 || r1s.lines[1].rhs !== '(0+2i) * P̃') bad('degree 1 non-monic: ' + JSON.stringify(r1s.lines));
  if (!(r1s.maxRelError <= 1e-12)) bad('degree 1 non-monic error ' + r1s.maxRelError);
}

// token shape and sign conventions of an actual complex chain
{
  const r = compileKnuthEveComplex([{ re: 1, im: 1 }, { re: 0, im: 1 }, { re: 1, im: 0 }, 1]);
  const text = r.lines.map(l => l.rhs).join('\n');
  if (!COMPLEX_TOKEN_G.test(text)) bad('cubic with Gaussian coefficients has no complex token: ' + text);
  if (/\bi\b/.test(text) || /\di[^)]/.test(text)) bad('bad token shape: ' + text);
  if (r.shift === undefined || r.shift.re !== 0 || r.shift.im !== 0) bad('non-degenerate cubic should not be shifted');
}

// a real polynomial whose nodes (the roots of its odd part) are distinct reals
// yields a real chain: no shift and no complex token anywhere
{
  const realRooted = (coeffs, label) => {
    let r;
    try { r = compileKnuthEveComplex(coeffs); } catch (e) { return bad(label + ': threw ' + e.message); }
    if (!r.shift || r.shift.re !== 0 || r.shift.im !== 0) bad(label + ': a real-rooted real input was shifted');
    const cx = r.lines.find(l => hasComplexToken(l.rhs));
    if (cx) bad(label + ': complex token in a real-rooted real chain: ' + cx.rhs);
    checkNumeric(r, coeffs, label);
  };
  realRooted([0, 4, 0, -5, 0, 1], 'x^5-5x^3+4x (nodes 1, 4)');
  realRooted([2, -36, -1, 49, 3, -14, 0, 1], 'odd part (w-1)(w-4)(w-9)');
  // p(x) = x prod_k (x^2 - s_k) + E(x^2) with distinct real s_k spread in [-3, 3]
  // and a random real even part (monic x^n for even n)
  for (let n = 3; n <= 24; n++) {
    const K = Math.ceil(n / 2) - 1;
    const nodes = Array.from({ length: K }, (_, k) => (K === 1 ? 1.5 : -3 + 6 * k / (K - 1)) + 0.05 * (k % 3));
    let odd = [1];                                   // prod (w - s_k) in w
    for (const s of nodes) { const q = new Array(odd.length + 1).fill(0); for (let j = 0; j < odd.length; j++) { q[j + 1] += odd[j]; q[j] -= s * odd[j]; } odd = q; }
    const p = new Array(n + 1).fill(0);
    for (let j = 0; j < odd.length; j++) p[2 * j + 1] = odd[j];
    for (let j = 0; 2 * j <= n; j++) p[2 * j] = Math.round((rnd() * 6 - 3) * 100) / 100;
    if (n % 2 === 0) p[n] = 1;
    realRooted(p, `real-rooted family n=${n}`);
  }
}

// the root finder: all roots, no real snap, multiple roots accepted
{
  const roots = polyRootsC([{ re: 0, im: -1 }, 0, 1]);                   // z^2 - i
  if (!roots || roots.length !== 2) bad('polyRootsC: z^2 - i');
  else for (const z of roots) if (Math.abs(z.re * z.re - z.im * z.im) > 1e-12 || Math.abs(2 * z.re * z.im - 1) > 1e-12) bad('polyRootsC: bad root of z^2 - i');
  const dbl = polyRootsC([1, 2, 1]);                                      // (z+1)^2
  if (!dbl || dbl.length !== 2 || dbl.some(z => Math.hypot(z.re + 1, z.im) > 1e-6)) bad('polyRootsC: (z+1)^2');
  if (!polyRootsC([1]) || polyRootsC([1]).length !== 0) bad('polyRootsC: constant');
}

// error inputs
for (const inp of [[], [0, 0], [1, NaN], [1, { re: 1, im: Infinity }]]) {
  let threw = false;
  try { compileKnuthEveComplex(inp); } catch (e) { threw = true; }
  if (!threw) bad('should throw on ' + JSON.stringify(inp));
}

console.log(`knutheve-complex: ${cases} compile cases, ${hardFails} failures`);
process.exit(hardFails ? 1 : 0);
