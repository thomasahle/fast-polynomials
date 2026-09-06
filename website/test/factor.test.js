import { GF2k, Q } from '../js/field.js';
import { Rat } from '../js/rat.js';
import * as P from '../js/poly.js';
import { compileHorner } from '../js/methods/horner.js';
import { compileEstrin } from '../js/methods/estrin.js';
import { compileRW } from '../js/methods/rw.js';
import { compileMotzkin, compileKnuthEve } from '../js/methods/motzkin.js';
import { compilePan1978Real } from '../js/methods/pan1978real.js';
import { factorize } from '../js/chain.js';
import { parseRhs } from '../js/cgen.js';
import { REAL_TOKEN, COMPLEX_TOKEN, numTokenValue } from '../js/tokens.js';
// exact evaluator over a field for line chains (handles the ' − ' minus and negated atoms);
// constants are the real tokens and the atomic complex literal (re±imi) of js/tokens.js, both handed to `lit`
function evalLines(lines, F, x, lit) {
  const env = { x };
  const ev = n => {
    if (n.tok !== undefined) {
      const neg = n.tok.startsWith('-'); const b = neg ? n.tok.slice(1) : n.tok;
      const kw = /^(\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)·(\w+)$/.exec(b);          // k·w integer multiple / radix scale
      if (kw) { const w = env[kw[2]]; if (w === undefined) throw new Error('undefined wire ' + kw[2]); return F.mul(lit(kw[1]), w); }
      const v = REAL_TOKEN.test(b) || COMPLEX_TOKEN.test(b) ? lit(b) : env[b];
      if (v === undefined) throw new Error('undefined wire ' + b);
      return neg ? F.neg(v) : v;
    }
    let acc = null;
    for (const { neg, t } of n.sum) { let v = null; for (const f of t) { const fv = ev(f); v = v === null ? fv : F.mul(v, fv); }
      acc = acc === null ? (neg ? F.neg(v) : v) : (neg ? F.sub(acc, v) : F.add(acc, v)); }
    return acc;
  };
  for (const l of lines) env[l.lhs] = ev(parseRhs(l.rhs));
  return env[lines[lines.length - 1].lhs];
}
const PURE = /^\w+ = \([^()]*\) \* \([^()]*\)$/;   // pure product, NO nested brackets inside factors
const FLAT_FINAL = /^[^()]*$/;                          // final affine row: no parentheses at all
let fails = 0, checked = 0;
const litQ = s => { const [a, b] = s.split('/'); return new Rat(BigInt(a), b ? BigInt(b) : 1n); };
const coeffsQ = [new Rat(3n,2n), new Rat(-2n), new Rat(7n), new Rat(1n,4n), new Rat(-1n), new Rat(3n), new Rat(2n), new Rat(-1n,2n), new Rat(4n), Rat.ONE];
for (const [nm, fn] of [['horner', compileHorner], ['estrin', compileEstrin], ['rw', compileRW]]) {
  const r = fn(coeffsQ, Q); const fl = factorize(r.lines);
  const nprod = fl.filter(l => l.mul).length;
  if (nprod !== r.mults) { console.log(`FAIL ${nm}: ${nprod} product rows vs ${r.mults} mults`); fails++; }
  for (const l of fl.slice(0, -1)) if (!PURE.test(`${l.lhs} = ${l.rhs}`)) { console.log(`FAIL ${nm}: not pure product: ${l.lhs} = ${l.rhs}`); fails++; }
  if (fl[fl.length - 1].mul) { console.log(`FAIL ${nm}: last row must be affine`); fails++; }
  for (const t of [1, 2, 3]) { const x = new Rat(BigInt(2 * t - 3), 2n);
    const a = evalLines(r.lines, Q, x, litQ), b = evalLines(fl, Q, x, litQ);
    checked++; if (!a.eq(b)) { console.log(`FAIL ${nm}: value mismatch at x=${x}`); fails++; } }
  console.log(`${nm}: ${fl.length} rows, ${nprod} products (= ${r.mults}) ok`);
}
{ // Knuth–Eve and Pan: the factored form the site displays evaluates like the plain chain
  // (the factoring pass inlines affine wires and folds their constants; both are numeric methods)
  // complex doubles {re, im}: Knuth–Eve/Pan rows may carry (re±imi) constants
  const Fd = { add: (a, b) => ({ re: a.re + b.re, im: a.im + b.im }), sub: (a, b) => ({ re: a.re - b.re, im: a.im - b.im }),
               mul: (a, b) => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re }), neg: a => ({ re: -a.re, im: -a.im }) };
  const cAbs = z => Math.hypot(z.re, z.im);
  const hermite = n => {                              // He_n: monic, integer coefficients, real roots (fast for Pan)
    let prev = [1], cur = [0, 1];
    for (let k = 1; k < n; k++) { const next = Array(k + 2).fill(0); cur.forEach((c, i) => { next[i + 1] += c; }); prev.forEach((c, i) => { next[i] -= k * c; }); [prev, cur] = [cur, next]; }
    return cur;
  };
  const scale = (cs, x) => cs.reduce((s, c, i) => s + Math.abs(c) * Math.pow(Math.max(1, Math.abs(x)), i), 0);
  const cases = [
    ['knuth-eve deg 9', compileKnuthEve, coeffsQ.map(c => Number(c.n) / Number(c.d))],
    ['knuth-eve He_11', compileKnuthEve, hermite(11)],
    ['pan He_9', compilePan1978Real, hermite(9)],
    ['pan He_11', compilePan1978Real, hermite(11)],
  ];
  for (const [nm, fn, cs] of cases) {
    let r;
    try { r = fn(cs); } catch (e) { console.log(`FAIL ${nm}: ${e.message}`); fails++; continue; }
    const fl = factorize(r.lines);
    const products = fl.filter(l => l.mul).length;
    for (const l of fl.slice(0, -1)) if (l.mul && !PURE.test(`${l.lhs} = ${l.rhs}`)) { console.log(`FAIL ${nm}: not pure product: ${l.lhs} = ${l.rhs}`); fails++; }
    for (const x of [0.5, 1.5, -1.25, 2.75]) {
      const a = evalLines(r.lines, Fd, { re: x, im: 0 }, numTokenValue), b = evalLines(fl, Fd, { re: x, im: 0 }, numTokenValue);
      checked++;
      if (!(cAbs(Fd.sub(a, b)) <= 1e-8 * (1 + cAbs(a) + scale(cs, x)))) { console.log(`FAIL ${nm} at ${x}: plain ${a.re} vs factored ${b.re}`); fails++; }
    }
    console.log(`${nm}: ${fl.length} rows, ${products} products ok`);
  }
}
{ // Motzkin: doubles
  const r = compileMotzkin(coeffsQ.map(c => Number(c.n) / Number(c.d))); const fl = factorize(r.lines);
  const Fd = { add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b, neg: a => -a };
  const litD = s => { const v = numTokenValue(s); if (v.im !== 0) throw new Error('complex constant in a Motzkin chain: ' + s); return v.re; };
  for (const l of fl.slice(0, -1)) if (!PURE.test(`${l.lhs} = ${l.rhs}`)) { console.log(`FAIL motzkin: ${l.lhs} = ${l.rhs}`); fails++; }
  for (const x of [0.5, 1.5, -1.25]) { const a = evalLines(r.lines, Fd, x, litD), b = evalLines(fl, Fd, x, litD);
    checked++; if (Math.abs(a - b) > 1e-9 * (1 + Math.abs(a))) { console.log(`FAIL motzkin at ${x}: ${a} vs ${b}`); fails++; } }
  console.log(`motzkin: ${fl.length} rows, ${fl.filter(l => l.mul).length} products (= ${r.mults}) ok`);
}
{ // a chain with complex constants: the atomic (re±imi) token survives factorize and both forms agree
  const Fc = { add: (a, b) => ({ re: a.re + b.re, im: a.im + b.im }), sub: (a, b) => ({ re: a.re - b.re, im: a.im - b.im }),
               mul: (a, b) => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re }), neg: a => ({ re: -a.re, im: -a.im }) };
  const lines = [
    { lhs: 'y', rhs: 'x + (0.5+1.25i)', mul: false },
    { lhs: 'z', rhs: '(y − (1+0.25i)) * (x + 2)', mul: true },
    { lhs: 'P', rhs: 'z + (0-1i) + 3', mul: false },
  ];
  const fl = factorize(lines);
  if (!(fl[0].rhs === '(x + (-0.5+1i)) * (x + 2)' && fl[1].rhs === 'z + (3-1i)')) { console.log(`FAIL complex factorize: ${fl.map(l => l.rhs).join(' | ')}`); fails++; }
  for (const x of [0.5, -1.25]) {
    const a = evalLines(lines, Fc, { re: x, im: 0 }, numTokenValue), b = evalLines(fl, Fc, { re: x, im: 0 }, numTokenValue);
    checked++; if (Math.hypot(a.re - b.re, a.im - b.im) > 1e-12) { console.log(`FAIL complex factorize at ${x}`); fails++; }
  }
  console.log(`complex constants: ${fl.length} rows ok`);
}
if (fails) process.exit(1);
console.log(`FACTOR PASSES (${checked} evaluations)`);
