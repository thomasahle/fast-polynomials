// Numerical-stability experiment for Pan's rational sextic scheme (Knuth TAOCP 2, 4.6.4, eq. (16)),
// in the model and with the metrics of tools/numstab.mjs (rounding depth rho, schedule amplification
// A = M(|x|) / sum |a_i||x|^i with the majorant M evaluated exactly, observed double-precision error in
// units of u * sum |a_i||x|^i, reference in exact rational arithmetic).  The line-chain helpers below are
// copied from tools/numstab.mjs (which does not export them); the corpus generator is the same LCG with
// the same seed, so the degree-6 corpus here is what numstab.mjs would draw for DEGREES=[6].
//
// Three experiments, selected by argv[2] (default: all):
//   corpus  : degree-6 corpus, prescribed coefficients (12 monic sextics, integer coefficients in [-5,5],
//             3 dyadic points in [-2,2]) for Horner, Estrin, Rabin-Winograd, Motzkin-Eve (numeric,
//             website compiler), Belaga (numeric, website compiler, skipped when its constants are
//             complex), Knuth (12) (Knuth's own 3-multiplication sextic scheme; needs a real root of
//             a cubic, found here by exact-rational bisection to 2^-128 so that the single rounding of
//             the model is the only rounding of its constants; among the real roots the one with the
//             smallest majorant at |x| = 2 is kept), this paper (even lift P_6 = a0 + x P_5), and
//             Pan (16) (exact rational preprocessing, this file).
//   hyper   : approach to Pan's exceptional hypersurface H = {D = 0}, D = u3 - 2 a0 u4 + 5 a0^3
//             (a0 = u5/3): u5 in {0, 3, -3}, u4, u2, u1, u0 random integers, u3 = 2 a0 u4 - 5 a0^3 + 2^-k,
//             k = 0, 4, ..., 40; reports log10 A, log10 |alpha1|, log10 |alpha5| and the observed error.
//             Prediction (tools/pan_sextic_check.py, V5): alpha5 ~ -N^3 / D^3, so log10 A grows like 3 k log10 2.
//   pankeys : prescribed keys for Pan: alpha_j = k/16, |k| <= 16, the induced sextic evaluated by (16).
//   validate: exact identity checks of the emitted chains (Pan (16) and Pan (0.7) at n = 6): the line chain
//             is re-parsed and evaluated in exact rational arithmetic at 7 distinct points (a degree-6
//             identity), and the chain is expanded to its coefficient vector; on the 12 corpus sextics and on
//             200 random monic sextics with rational coefficients (numerator in [-50,50], denominator in [1,12]).
//   rho     : generic rounding depth of every line-chain scheme, measured on a monic polynomial with
//             coefficients (2i+3)/7 (none of which, and none of whose preprocessed constants, vanishes):
//             the harness's rhoLines drops a '+0' when a constant happens to be 0, so rho measured on one
//             corpus polynomial is input-dependent (Horner 2n-1 minus the number of zero coefficients;
//             Rabin-Winograd 10-12 at n = 7).  The corpus/odd blocks report the maximum over the trials
//             (which equals the generic value) and keep the per-trial values in rhoTrials.
//   scale   : sweep towards H by SCALING u3: u3 = (1 + 2^-k) u3_H with u3_H = 2 a0 u4 - 5 a0^3 (so that
//             D = 2^-k u3_H), for the corpus sextics with u5 in {3, -3} (u3_H an integer, the scaled u3 dyadic),
//             k = 0, 2, ..., 40 and k = infinity (on H: no parameters); records log10 |alpha_1..5|, log10 A,
//             the observed error of Pan (16), and Horner / this paper on the same polynomial and points.
// Corpus mode also includes 'Pan (0.7)' at n = 6: the even-n case of Pan's general real scheme (0.7),
//   P = x p5 + u0, p5 = (x + l1) ((x^2 + x + l2)(x^2 + l3) + l4) + l5, which is RATIONAL and everywhere
//   defined at n <= 6 (stage 1 of the decoder: l1 = u5 - 1, l5 = p5(-l1), Todd's quartic); 4 multiplications.
// Writes <scratch>/numstab_pan.json when argv[3] is a directory.
import { Q } from '../website/js/field.js';
import { Rat } from '../website/js/rat.js';
import * as P from '../website/js/poly.js';
import * as core from '../website/js/char0/core.js';
import { parseRhs } from '../website/js/cgen.js';
import { compileHorner } from '../website/js/methods/horner.js';
import { compileEstrin } from '../website/js/methods/estrin.js';
import { compileRW } from '../website/js/methods/rw.js';
import { compileMotzkin } from '../website/js/methods/motzkin.js';
import { compileBelaga } from '../website/js/methods/belaga.js';
import { writeFileSync, existsSync } from 'fs';
import { pathToFileURL } from 'url';

const U = 2 ** -53;
let seed = 12345n;
const rnd = () => { seed = (seed * 6364136223846793005n + 1442695040888963407n) & ((1n << 64n) - 1n); return seed; };
const rint = (lo, hi) => lo + Number(rnd() % BigInt(hi - lo + 1));

// ---- line-chain evaluation (copied from tools/numstab.mjs) ----
function evalAst(node, ops) {
  if (node.tok !== undefined) {
    if (/^-?(0x[0-9a-fA-F]+|\d+(\.\d+)?([eE][+-]?\d+)?(\/\d+)?)$/.test(node.tok)) return ops.lit(node.tok);
    if (node.tok.startsWith('-')) return ops.sub(ops.zero, ops.wire(node.tok.slice(1)));
    return ops.wire(node.tok);
  }
  let acc = null;
  for (const { neg, t } of node.sum) {
    let v = null;
    for (const f of t) { const fv = evalAst(f, ops); v = v === null ? fv : ops.mul(v, fv); }
    acc = acc === null ? (neg ? ops.sub(ops.zero, v) : v) : (neg ? ops.sub(acc, v) : ops.add(acc, v));
  }
  return acc;
}
function evalLines(lines, x, mk) {
  const env = { x };
  const ops = mk(name => env[name]);
  for (const l of lines) env[l.lhs] = evalAst(parseRhs(l.rhs), ops);
  return env[lines[lines.length - 1].lhs];
}
function rhoLines(lines, constRho) {
  const env = { x: 0 };
  const opsR = w => env[w];
  const rho = node => {
    if (node.tok !== undefined) {
      if (/^-?(0x|\d)/.test(node.tok)) return constRho;
      return node.tok.startsWith('-') ? opsR(node.tok.slice(1)) : opsR(node.tok);
    }
    let best = 0;
    const m = node.sum.length;
    for (const { t } of node.sum) {
      let r = 0;
      for (const f of t) r += rho(f);
      r += t.length - 1;
      best = Math.max(best, r);
    }
    return best + (m - 1);
  };
  for (const l of lines) env[l.lhs] = rho(parseRhs(l.rhs));
  return env[lines[lines.length - 1].lhs];
}
const litRat = t => {
  const neg = t.startsWith('-'); if (neg) t = t.slice(1);
  let r;
  if (t.includes('/')) { const [a, b] = t.split('/'); r = new Rat(BigInt(a), BigInt(b)); }
  else if (t.includes('.') || /e/i.test(t)) { r = doubleToRat(Number(t)); }
  else r = new Rat(BigInt(t));
  return neg ? r.neg() : r;
};
function ratToDouble(r) {                          // correctly rounded (half-to-even)
  if (r.isZero()) return 0;
  const neg = r.n < 0n; let n = neg ? -r.n : r.n, d = r.d;
  const bl = v => v.toString(2).length;
  let k = 55 - (bl(n) - bl(d));
  const qr = () => k >= 0 ? [(n << BigInt(k)) / d, (n << BigInt(k)) % d] : [n / (d << BigInt(-k)), n % (d << BigInt(-k))];
  let [q, rem] = qr();
  while (bl(q) > 55) { k -= 1; [q, rem] = qr(); }
  while (bl(q) < 54) { k += 1; [q, rem] = qr(); }
  const extra = bl(q) - 53;
  const drop = q & ((1n << BigInt(extra)) - 1n);
  let m = q >> BigInt(extra);
  const half = 1n << BigInt(extra - 1);
  const sticky = rem !== 0n;
  if (drop > half || (drop === half && (sticky || (m & 1n) === 1n))) m += 1n;
  const e = extra - k;
  let v = Number(m) * 2 ** e;
  if (!Number.isFinite(v)) v = Number(m) * 2 ** (e - 60) * 2 ** 60;
  return neg ? -v : v;
}
function doubleToRat(v) {
  if (!Number.isFinite(v)) throw new Error('nonfinite');
  if (v === 0) return Rat.ZERO;
  let m = v, e = 0;
  while (!Number.isInteger(m)) { m *= 2; e++; }
  return new Rat(BigInt(m), 1n << BigInt(e));
}
const ratLog10 = r => {
  if (r.isZero()) return -Infinity;
  const n = (r.n < 0n ? -r.n : r.n).toString(), d = r.d.toString();
  const lead = s => Number(s.slice(0, 15)) / 10 ** (Math.min(s.length, 15) - 1);
  return (n.length - 1 + Math.log10(lead(n))) - (d.length - 1 + Math.log10(lead(d)));
};
const ratAbs = r => (r.isNeg() ? r.neg() : r);
const mkDouble = wire => ({ zero: 0, lit: t => ratToDouble(litRat(t)), wire, add: (a, b) => a + b, sub: (a, b) => a - b, mul: (a, b) => a * b });
// double arithmetic with an exact shadow: records every operation whose double result is not the exact
// value of its (double) operands, with the magnitude of the result -- the first entry is the first rounding
// of the evaluation (the constants are rounded before, see exactConsts below)
const mkTraceDouble = trace => wire => {
  const chk = (op, d, ex) => { if (Number.isFinite(d) && !doubleToRat(d).eq(ex)) trace.push({ op, size: Math.abs(d) }); return d; };
  return { zero: 0, lit: t => ratToDouble(litRat(t)), wire,
    add: (a, b) => chk('+', a + b, doubleToRat(a).add(doubleToRat(b))),
    sub: (a, b) => chk('-', a - b, doubleToRat(a).sub(doubleToRat(b))),
    mul: (a, b) => chk('*', a * b, doubleToRat(a).mul(doubleToRat(b))) };
};
const exactConst = r => doubleToRat(ratToDouble(r)).eq(r);       // is the rational exactly representable as a double?
const mkMajorant = wire => ({ zero: Rat.ZERO, lit: t => ratAbs(litRat(t)), wire, add: (a, b) => a.add(b), sub: (a, b) => a.add(b), mul: (a, b) => a.mul(b) });
const cst = c => Rat.of(typeof c === 'number' ? BigInt(c) : c);
function evalOurs(chain, x, mode) {
  const wires = { 0: mode === 'double' ? 1 : Rat.ONE, 1: x };
  const form = f => {
    let acc = mode === 'double' ? ratToDouble(cst(f.const)) : (mode === 'maj' ? ratAbs(cst(f.const)) : cst(f.const));
    for (const [w, k] of f.terms) {
      if (k === 0) continue;
      const kk = mode === 'maj' ? Math.abs(k) : k;
      if (mode === 'double') acc = acc + kk * wires[w];
      else acc = acc.add(Rat.of(BigInt(kk)).mul(wires[w]));
    }
    return acc;
  };
  for (const g of chain.gates) {
    const l = form(g.left), r = form(g.right);
    wires[g.out_wire] = mode === 'double' ? l * r : l.mul(r);
  }
  return form(chain.output);
}
function rhoOurs(chain) {
  const rho = { 0: 1, 1: 0 };
  const formRho = f => {
    let terms = 0, best = 0;
    if (!cst(f.const).isZero()) { terms++; best = Math.max(best, 1); }
    for (const [w, k] of f.terms) {
      if (k === 0) continue;
      terms++;
      best = Math.max(best, rho[w] + (Math.abs(k) === 1 ? 0 : 1));
    }
    return best + Math.max(0, terms - 1);
  };
  for (const g of chain.gates) rho[g.out_wire] = 1 + formRho(g.left) + formRho(g.right);
  return formRho(chain.output);
}

// ---- Pan's scheme (16): exact rational preprocessing, decoder = the pivot sequence of
//      tools/pan_sextic_check.py (alpha0 slope 3; synthetic division by z; alpha1 = N/D; alpha3 slope 2;
//      alpha2, alpha4, alpha5 unit pivots).  Input: monic sextic as Rat[7], ascending. ----
export function decodePan16(u) {
  if (u.length !== 7 || !u[6].isOne()) throw new Error('Pan (16): monic sextic required');
  const [u0, u1, u2, u3, u4, u5] = u;
  const a0 = u5.div(Rat.of(3n));
  const D = u3.sub(a0.mul(u4).mul(Rat.of(2n))).add(a0.mul(a0).mul(a0).mul(Rat.of(5n)));
  const N = u1.sub(a0.mul(u2)).add(a0.mul(a0).mul(u3)).sub(a0.mul(a0).mul(a0).mul(u4)).add(a0.mul(a0).mul(a0).mul(a0).mul(a0).mul(Rat.of(2n)));
  if (D.isZero()) throw new Error('Pan (16): on the exceptional hypersurface 27u3 - 18u5u4 + 5u5^3 = 0');
  const a1 = N.div(D);
  const b1 = a0.mul(Rat.of(2n));
  const b2 = u4.sub(a0.mul(b1)).sub(a1);
  const b3 = u3.sub(a0.mul(b2)).sub(a1.mul(b1));
  const b4 = u2.sub(a0.mul(b3)).sub(a1.mul(b2));
  const a0m1 = a0.sub(Rat.ONE);
  const a3 = b3.sub(a0m1.mul(b2)).add(a0m1.mul(a0.mul(a0).sub(Rat.ONE))).div(Rat.of(2n)).sub(a1);
  const a2 = b2.sub(a0.mul(a0).sub(Rat.ONE)).sub(a3).sub(a1.mul(Rat.of(2n)));
  const a4 = b4.sub(a2.add(a1).mul(a3.add(a1)));
  const a5 = u0.sub(a1.mul(b4));
  return { alphas: [a0, a1, a2, a3, a4, a5], D, N };
}
const term = (base, c) => c.isZero() ? base : (c.isNeg() ? `${base} − ${c.neg().toString()}` : `${base} + ${c.toString()}`);
export function compilePan16(u) {
  const { alphas: [a0, a1, a2, a3, a4, a5], D, N } = decodePan16(u);
  const lines = [
    { lhs: 'z', rhs: term(`(${term('x', a0)}) * x`, a1), mul: true },
    { lhs: 'w', rhs: term('z + x', a2), mul: false },
    { lhs: 'q', rhs: term(`(${term('z − x', a3)}) * w`, a4), mul: true },
    { lhs: 'P', rhs: term('q * z', a5), mul: true },
  ];
  return { lines, mults: 3, alphas: [a0, a1, a2, a3, a4, a5], D, N };
}
// ---- Pan's general scheme (0.7) at n = 6 (exact rational; survey p. 108 with n = 4k+2, k = 1):
//      P = x p5 + a6,  p5 = p1 q4 + l5,  p1 = x + l1,  q4 = (x^2 + x + l2)(x^2 + l3) + l4.
//      Decoder (stage 1 of tools/numstab_pan07.py, rational): p5 = (P - u0)/x monic quintic; the quotient
//      of p5 - l5 by (x + l1) must have x^3-coefficient 1, i.e. l1 = u5 - 1 (row x^4 of p5: unit pivot);
//      l5 = p5(-l1) (remainder, unit pivot); q4 = (p5 - l5)/(x + l1) = x^4 + x^3 + b2 x^2 + b3 x + b4;
//      l3 = b3, l2 = b2 - b3, l4 = b4 - l2 l3 (Lemma 3.5 / Todd: three unit pivots).  No division by data. ----
export function decodePan07_6(u) {
  if (u.length !== 7 || !u[6].isOne()) throw new Error('Pan (0.7) n=6: monic sextic required');
  const F = Q, X = P.X(F);
  const p5 = u.slice(1);                                   // (P - u0)/x, ascending, monic quintic
  const l1 = p5[4].sub(Rat.ONE);
  const l5 = P.evalAt(F, p5, l1.neg());
  const [q4, rem] = P.divmod(F, P.sub(F, p5, [l5]), P.add(F, X, [l1]));
  if (!(rem.length === 0 || rem.every(c => c.isZero()))) throw new Error('Pan (0.7) n=6: division remainder');
  while (q4.length < 5) q4.push(Rat.ZERO);
  if (!q4[4].isOne() || !q4[3].isOne()) throw new Error('Pan (0.7) n=6: quartic not of the form x^4 + x^3 + ...');
  const l3 = q4[1], l2 = q4[2].sub(q4[1]), l4 = q4[0].sub(l2.mul(l3));
  return { lams: [l1, l2, l3, l4, l5], a6: u[0] };
}
export function compilePan07_6(u) {
  const { lams: [l1, l2, l3, l4, l5], a6 } = decodePan07_6(u);
  const lines = [
    { lhs: 's', rhs: 'x * x', mul: true },
    { lhs: 's1', rhs: 's + x', mul: false },
    { lhs: 'p1', rhs: term('x', l1), mul: false },
    { lhs: 'q', rhs: term(`(${term('s1', l2)}) * (${term('s', l3)})`, l4), mul: true },
    { lhs: 'p5', rhs: term('p1 * q', l5), mul: true },
    { lhs: 'P', rhs: term('x * p5', a6), mul: true },
  ];
  return { lines, mults: 4, lams: [l1, l2, l3, l4, l5] };
}
export function pan07_6Poly(lams, a6) {
  const F = Q, X = P.X(F);
  const [l1, l2, l3, l4, l5] = lams;
  const s = P.mul(F, X, X), s1 = P.add(F, s, X);
  const q = P.add(F, P.mul(F, P.add(F, s1, [l2]), P.add(F, s, [l3])), [l4]);
  const p5 = P.add(F, P.mul(F, P.add(F, X, [l1]), q), [l5]);
  const out = P.add(F, P.mul(F, X, p5), [a6]);
  while (out.length < 7) out.push(Rat.ZERO);
  return out;
}
// ---- Knuth's scheme (12) (TAOCP 2, 4.6.4, eqs. (12)-(14)): z = (x+a0)x+a1, w = (x+a2)z+a3,
//      u = ((w+z+a4)w+a5) (monic).  beta6 = a real root of the cubic (13), found by exact bisection. ----
const R = c => Rat.of(BigInt(c));
function realRootsExactCubic(c) {            // c = [c0, c1, c2, c3] ascending, c3 != 0, Rat; roots to 2^-128
  const f = y => c[0].add(c[1].mul(y)).add(c[2].mul(y).mul(y)).add(c[3].mul(y).mul(y).mul(y));
  let B = Rat.ONE;                          // Cauchy bound 1 + max |c_i/c_3|
  for (let i = 0; i < 3; i++) { const q = ratAbs(c[i].div(c[3])); if (ratLog10(q) > ratLog10(B)) B = q; }
  B = B.add(Rat.ONE);
  const G = 4096, roots = [];
  let prevY = B.neg(), prevS = f(prevY);
  for (let i = 1; i <= G; i++) {
    const y = B.neg().add(B.mul(R(2)).mul(new Rat(BigInt(i), BigInt(G))));
    const sY = f(y);
    if (sY.isZero()) { roots.push(y); }
    else if (!prevS.isZero() && prevS.isNeg() !== sY.isNeg()) {
      let lo = prevY, hi = y, slo = prevS;
      for (let it = 0; it < 140; it++) {
        const mid = lo.add(hi).div(R(2)); const sm = f(mid);
        if (sm.isZero()) { lo = hi = mid; break; }
        if (sm.isNeg() === slo.isNeg()) { lo = mid; slo = sm; } else hi = mid;
      }
      roots.push(lo.add(hi).div(R(2)));
    }
    prevY = y; prevS = sY;
  }
  return roots;
}
export function compileKnuth12(u) {
  if (u.length !== 7 || !u[6].isOne()) throw new Error('Knuth (12): monic sextic required');
  const [u0, u1, u2, u3, u4, u5] = u;
  const b1 = u5.sub(Rat.ONE).div(R(2));
  const b2 = u4.sub(b1.mul(b1.add(Rat.ONE)));
  const b3 = u3.sub(b1.mul(b2));
  const b4 = b1.sub(b2);
  const b5 = u2.sub(b1.mul(b3));
  const cubic = [u1.sub(b2.mul(b5)), b5.mul(R(2)).sub(b2.mul(b4)).sub(b3), b4.mul(R(2)).sub(b2).add(Rat.ONE), R(2)];
  const roots = realRootsExactCubic(cubic);
  if (roots.length === 0) throw new Error('Knuth (12): no real root bracketed (cannot happen for a cubic)');
  let best = null;
  for (const b6 of roots) {
    const b7 = b6.mul(b6).add(b4.mul(b6)).add(b5);
    const b8 = b3.sub(b6).sub(b7);
    const a0 = b2.sub(b6.mul(R(2)));
    const a2 = b1.sub(a0);
    const a1 = b6.sub(a0.mul(a2));
    const a3 = b7.sub(a1.mul(a2));
    const a4 = b8.sub(b7).sub(a1);
    const a5 = u0.sub(b7.mul(b8));
    const lines = [
      { lhs: 'z', rhs: term(`(${term('x', a0)}) * x`, a1), mul: true },
      { lhs: 'w', rhs: term(`(${term('x', a2)}) * z`, a3), mul: true },
      { lhs: 'P', rhs: term(`(${term('w + z', a4)}) * w`, a5), mul: true },
    ];
    const maj = evalLines(lines, R(2), mkMajorant);
    // preprocessing residual: the chain's exact polynomial vs u (only x^1, x^0 can differ, by the cubic residual)
    const F = Q, X = P.X(F);
    const z = P.add(F, P.mul(F, P.add(F, X, [a0]), X), [a1]);
    const w = P.add(F, P.mul(F, P.add(F, X, [a2]), z), [a3]);
    const out = P.add(F, P.mul(F, P.add(F, P.add(F, w, z), [a4]), w), [a5]);
    let resid = -Infinity;
    for (let i = 0; i <= 6; i++) { const dlt = ratAbs((out[i] ?? Rat.ZERO).sub(u[i])); if (!dlt.isZero()) resid = Math.max(resid, ratLog10(dlt)); }
    const cand = { lines, mults: 3, alphas: [a0, a1, a2, a3, a4, a5], b6, logMaj2: ratLog10(maj), logResid: resid, nroots: roots.length };
    if (!best || cand.logMaj2 < best.logMaj2) best = cand;
  }
  return best;
}
// induced sextic from Pan's keys (exact): expand the chain
export function pan16Poly(al) {
  const F = Q;
  const [a0, a1, a2, a3, a4, a5] = al;
  const x = P.X(F);
  const z = P.add(F, P.mul(F, P.add(F, x, [a0]), x), [a1]);
  const w = P.add(F, P.add(F, z, x), [a2]);
  const v = P.add(F, P.sub(F, z, x), [a3]);
  const q = P.add(F, P.mul(F, v, w), [a4]);
  const out = P.add(F, P.mul(F, q, z), [a5]);
  while (out.length < 7) out.push(Rat.ZERO);
  return out;
}

// ---- measurement of one chain on one (P, x) ----
function measure(ch, coeffs, x, n) {
  const exact = P.evalAt(Q, coeffs, x);
  let Ssum = Rat.ZERO, xp = Rat.ONE, ax = ratAbs(x);
  for (let i = 0; i <= n; i++) { Ssum = Ssum.add(ratAbs(coeffs[i]).mul(xp)); xp = xp.mul(ax); }
  const xd = ratToDouble(x);
  let approx, maj;
  if (ch.ours) { approx = evalOurs(ch.ours, xd, 'double'); maj = evalOurs(ch.ours, ax, 'maj'); }
  else { approx = evalLines(ch.lines, xd, mkDouble); maj = evalLines(ch.lines, ax, mkMajorant); }
  const logA = ratLog10(maj) - ratLog10(Ssum);
  const err = Number.isFinite(approx) ? Math.abs(approx - ratToDouble(exact)) / (U * ratToDouble(Ssum)) : Infinity;
  const trace = [];
  if (!ch.ours) evalLines(ch.lines, xd, mkTraceDouble(trace));
  return { logA, err, approx, exact: ratToDouble(exact), S: ratToDouble(Ssum), nInexact: trace.length, firstInexact: trace[0] ?? null };
}
const summarize = a => { const s = [...a].sort((p, q) => p - q); return { median: s[Math.floor(s.length / 2)], max: s[s.length - 1] }; };
const fmtRow = (name, r) => `${name.padEnd(16)} rho=${String(r.rho).padStart(3)}  log10A med=${r.logA.median.toFixed(1)} max=${r.logA.max.toFixed(1)}  err/(uS) med=${r.err.median.toExponential(2)} max=${r.err.max.toExponential(2)}  samples=${r.samples}${r.skipped ? ' skipped=' + r.skipped : ''}`;

// experiments run only when this file is the entry point (it is also imported for its compilers)
const IS_MAIN = process.argv[1] !== undefined && import.meta.url === pathToFileURL(process.argv[1]).href;
const WHAT = IS_MAIN ? (process.argv[2] ?? 'all') : 'none';
const OUT = process.argv[3];
const results = {};

// ================= corpus (prescribed coefficients, n = 6) =================
if (WHAT === 'all' || WHAT === 'corpus') {
  const n = 6, TRIALS = 12;
  seed = 12345n;
  const rows = {};
  const stat = name => (rows[name] ??= { rho: null, rhoTrials: [], A: [], err: [], skipped: 0, per: [] });
  const field = core.rationals();
  for (let trial = 0; trial < TRIALS; trial++) {
    const coeffs = [...Array.from({ length: n }, () => new Rat(BigInt(rint(-5, 5)))), Rat.ONE];
    if (coeffs.every((c, i) => i === n || c.isZero())) continue;
    const xs = Array.from({ length: 3 }, () => new Rat(BigInt(rint(-128, 128)), 64n));
    const chains = {};
    chains.Horner = { lines: compileHorner(coeffs, Q).lines, cr: 0 };
    chains.Estrin = { lines: compileEstrin(coeffs, Q).lines, cr: 0 };
    chains['Rabin–Winograd'] = { lines: compileRW(coeffs, Q).lines, cr: 1 };
    try { chains['Motzkin–Eve'] = { lines: compileMotzkin(coeffs.map(ratToDouble)).lines, cr: 1 }; } catch (e) { stat('Motzkin–Eve').skipped++; }
    try {
      const b = compileBelaga(coeffs.map(ratToDouble));
      if (b.preprocessing === 'complex') { stat('Belaga').skipped++; stat('Belaga').complex = (stat('Belaga').complex ?? 0) + 1; }
      else chains.Belaga = { lines: b.lines, cr: 1 };
    } catch (e) { stat('Belaga').skipped++; }
    const params = core.decode(n, coeffs, field);
    chains['this paper'] = { ours: core.compile_paper_params_chain(params, null) };
    try { chains['Pan (16)'] = { lines: compilePan16(coeffs).lines, cr: 1 }; } catch (e) { stat('Pan (16)').skipped++; }
    try { chains['Pan (0.7)'] = { lines: compilePan07_6(coeffs).lines, cr: 1 }; } catch (e) { stat('Pan (0.7)').skipped++; }
    (results.corpusPolys ??= []).push({ trial, coeffs: coeffs.map(c => c.toString()), xs: xs.map(x => x.toString()) });
    try { const k12 = compileKnuth12(coeffs); chains['Knuth (12)'] = { lines: k12.lines, cr: 1 }; (stat('Knuth (12)').resid ??= []).push(k12.logResid); (stat('Knuth (12)').nroots ??= []).push(k12.nroots); } catch (e) { stat('Knuth (12)').skipped++; }
    for (const [name, ch] of Object.entries(chains)) {
      const st = stat(name);
      // rho is a property of the schedule; a constant that happens to vanish drops a rounding, so the
      // per-trial value is input-dependent and the generic depth is the maximum over the trials
      const r = ch.ours
        ? rhoOurs(core.compile_paper_params_chain(Array.from({ length: n }, (_, i) => new Rat(BigInt(2 * i + 3), 7n)), null))
        : rhoLines(ch.lines, ch.cr);
      st.rhoTrials.push(r); st.rho = Math.max(st.rho ?? 0, r);
      for (const x of xs) { const m = measure(ch, coeffs, x, n); st.A.push(m.logA); st.err.push(m.err); st.per.push({ trial, x: x.toString(), logA: m.logA, err: m.err }); }
    }
  }
  results.corpus = {};
  console.log('--- degree-6 corpus, prescribed coefficients (12 monic sextics, coefficients in [-5,5], 3 dyadic x in [-2,2]) ---');
  for (const name of ['Horner', 'Estrin', 'Rabin–Winograd', 'Motzkin–Eve', 'Belaga', 'Knuth (12)', 'this paper', 'Pan (16)', 'Pan (0.7)']) {
    const st = rows[name]; if (!st || st.A.length === 0) { console.log(`${name.padEnd(16)} (no samples; skipped=${st?.skipped ?? 0}${st?.complex ? ', complex constants=' + st.complex : ''})`); continue; }
    const r = { rho: st.rho, rhoTrials: st.rhoTrials, logA: summarize(st.A), err: summarize(st.err), samples: st.err.length, skipped: st.skipped, complex: st.complex ?? 0, per: st.per };
    results.corpus[name] = r;
    const rhoNote = st.rhoTrials.some(v => v !== st.rho) ? ` rho per trial=[${st.rhoTrials.join(',')}] (max = generic)` : '';
    console.log(fmtRow(name, r) + (st.complex ? ` complex=${st.complex}` : '') + (st.resid ? ` cubic-residual log10 max=${Math.max(...st.resid).toFixed(0)} real roots=${st.nroots.join('')}` : '') + rhoNote);
  }
  // which sample gives each row's maximum (the A maximum and the error maximum need not coincide)
  for (const name of ['Pan (16)', 'this paper', 'Motzkin–Eve', 'Belaga', 'Knuth (12)']) {
    const st = rows[name]; if (!st || st.per.length === 0) continue;
    const amax = st.per.reduce((a, b) => (b.logA > a.logA ? b : a)), emax = st.per.reduce((a, b) => (b.err > a.err ? b : a));
    console.log(`  ${name}: A max = ${(10 ** amax.logA).toFixed(0)} (log10 ${amax.logA.toFixed(3)}) at trial ${amax.trial}, x = ${amax.x} (err there ${amax.err.toExponential(2)});  err max = ${emax.err.toExponential(3)} at trial ${emax.trial}, x = ${emax.x} (log10 A there ${emax.logA.toFixed(3)})`);
  }
  for (const p of results.corpusPolys) console.log(`  trial ${p.trial}: P = [${p.coeffs.join(', ')}]  x in {${p.xs.join(', ')}}`);
  // Pan parameter sizes on the corpus
  seed = 12345n;
  const dens = [];
  for (let trial = 0; trial < TRIALS; trial++) {
    const coeffs = [...Array.from({ length: n }, () => new Rat(BigInt(rint(-5, 5)))), Rat.ONE];
    for (let i = 0; i < 3; i++) rint(-128, 128);
    try { const p = compilePan16(coeffs); dens.push({ D: p.D.toString(), maxLogAlpha: Math.max(...p.alphas.map(a => a.isZero() ? -Infinity : ratLog10(ratAbs(a)))) }); } catch (e) { dens.push({ D: '0' }); }
  }
  results.corpusPanParams = dens;
  console.log('Pan (16) on the corpus: D = ' + dens.map(d => d.D).join(', '));
  console.log('Pan (16) on the corpus: max log10|alpha| = ' + dens.map(d => d.maxLogAlpha?.toFixed(1)).join(', '));
}

// ================= approach to the hypersurface =================
if (WHAT === 'all' || WHAT === 'hyper') {
  seed = 777n;
  console.log('--- approach to H = {D = 0}: u3 = 2 a0 u4 - 5 a0^3 + 2^-k (a0 = u5/3 integer), other coefficients random in [-5,5] ---');
  results.hyper = [];
  const KS = [0, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40];
  for (let fam = 0; fam < 3; fam++) {
    const u5 = [0, 3, -3][fam], a0 = u5 / 3;
    const u4 = rint(-5, 5), u2 = rint(-5, 5), u1 = rint(-5, 5), u0 = rint(-5, 5);
    const xs = [new Rat(3n, 2n), new Rat(-5n, 4n), new Rat(1n, 2n)];
    const u3base = 2 * a0 * u4 - 5 * a0 ** 3;
    console.log(`family ${fam}: u5=${u5} u4=${u4} u2=${u2} u1=${u1} u0=${u0}  (u3 = ${u3base} + 2^-k); x in {3/2, -5/4, 1/2}`);
    let prev = null; const slopes = [];
    for (const k of KS) {
      const u3 = new Rat(BigInt(u3base) * (1n << BigInt(k)) + 1n, 1n << BigInt(k));
      const coeffs = [u0, u1, u2].map(c => new Rat(BigInt(c))).concat([u3, new Rat(BigInt(u4)), new Rat(BigInt(u5)), Rat.ONE]);
      const p = compilePan16(coeffs);
      const ch = { lines: p.lines, cr: 1 };
      const As = [], errs = [], ms = [];
      for (const x of xs) { const m = measure(ch, coeffs, x, 6); As.push(m.logA); errs.push(m.err); ms.push(m); }
      const hs = { lines: compileHorner(coeffs, Q).lines, cr: 0 };
      const herr = xs.map(x => measure(hs, coeffs, x, 6).err);
      // error mechanism: which constants are exactly representable, where the evaluation first rounds, and
      // whether the double result is exactly 0 (fl(q z) = -fl(alpha_5): the reported error is then |P(x)|/(u S) <= 1/u)
      const exactConsts = p.alphas.map(exactConst);
      const mech = ms.map(m => ({ x: m.x, nInexact: m.nInexact, first: m.firstInexact, zero: m.approx === 0, errOverA: m.err / 10 ** m.logA }));
      const row = { fam, k, u: { u5, u4, u2, u1, u0 }, xs: xs.map(x => x.toString()), logD: ratLog10(ratAbs(p.D)), logN: ratLog10(ratAbs(p.N)), logA1: ratLog10(ratAbs(p.alphas[1])), logA5: ratLog10(ratAbs(p.alphas[5])),
        logA: summarize(As), err: summarize(errs), hornerErr: summarize(herr), exactConsts, mech };
      results.hyper.push(row);
      const slopeV = prev ? (row.logA.median - prev.logA.median) / ((k - prev.k) * Math.log10(2)) : null;   // between k-4 and k
      if (slopeV !== null) { row.slope = -slopeV; slopes.push({ k, slope: -slopeV }); }
      const slope = slopeV === null ? '   -' : slopeV.toFixed(2);
      const mechS = `consts exact=${exactConsts.map(b => (b ? 1 : 0)).join('')} inexact ops/x=${mech.map(m => m.nInexact).join(',')} first=${mech.map(m => (m.first ? m.first.op + '@' + m.first.size.toExponential(1) : '-')).join(',')} zero result=${mech.map(m => (m.zero ? 1 : 0)).join('')}`;
      console.log(`  k=${String(k).padStart(2)} D=2^-${k} log10|N|=${row.logN.toFixed(2)} log10|a1|=${row.logA1.toFixed(1)} log10|a5|=${row.logA5.toFixed(1)}  log10A med=${row.logA.median.toFixed(1)} max=${row.logA.max.toFixed(1)} [d log10A / d log10 D = -${slope} between k-4 and k]  err/(uS) med=${row.err.median.toExponential(2)} max=${row.err.max.toExponential(2)}  Horner max=${row.hornerErr.max.toExponential(2)}  ${mechS}`);
      prev = row;
    }
    const s8 = slopes.filter(s => s.k >= 8), s12 = slopes.filter(s => s.k >= 12);
    console.log(`  family ${fam} slopes: ${slopes.map(s => `k=${s.k}: ${s.slope.toFixed(3)}`).join('  ')}`);
    console.log(`  family ${fam}: |slope + 3| < 0.05 for all k >= 8: ${s8.every(s => Math.abs(s.slope + 3) < 0.05)};  |slope + 3| < 0.005 for all k >= 12: ${s12.every(s => Math.abs(s.slope + 3) < 0.005)}`);
  }
}

// ================= Pan's keys as the data =================
if (WHAT === 'all' || WHAT === 'pankeys') {
  seed = 4242n;
  console.log('--- prescribed keys for Pan (16): alpha_j = k/16, |k| <= 16 (12 key vectors, 3 dyadic x) ---');
  const As = [], errs = [], ratios = [];
  let rho = null;
  for (let trial = 0; trial < 12; trial++) {
    const al = Array.from({ length: 6 }, () => new Rat(BigInt(rint(-16, 16)), 16n));
    const coeffs = pan16Poly(al);
    const xs = Array.from({ length: 3 }, () => new Rat(BigInt(rint(-128, 128)), 64n));
    const p = compilePan16(coeffs);                    // re-decode: must return the keys (off H)
    const same = p.alphas.every((a, i) => a.eq(al[i]));
    if (!same) console.log('  (re-decoding did not return the keys: D = ' + p.D.toString() + ')');
    const ch = { lines: p.lines, cr: 1 };
    if (rho === null) rho = rhoLines(ch.lines, 1);
    for (const x of xs) { const m = measure(ch, coeffs, x, 6); As.push(m.logA); errs.push(m.err); }
  }
  results.pankeys = { rho, logA: summarize(As), err: summarize(errs), samples: errs.length };
  console.log(fmtRow('Pan (16) keys', results.pankeys));
}


// ================= validate: exact identity checks =================
if (WHAT === 'all' || WHAT === 'validate') {
  console.log('--- validate: exact identity checks of the emitted chains (rational arithmetic; no floating point) ---');
  const pts = [-3, -2, -1, 0, 1, 2, 3].map(v => Rat.of(BigInt(v)));    // 7 points determine a degree-6 polynomial
  const mkRat = wire => ({ zero: Rat.ZERO, lit: t => litRat(t), wire, add: (a, b) => a.add(b), sub: (a, b) => a.sub(b), mul: (a, b) => a.mul(b) });
  const cases = [];
  seed = 12345n;
  for (let trial = 0; trial < 12; trial++) {                           // the corpus sextics (same stream)
    const coeffs = [...Array.from({ length: 6 }, () => new Rat(BigInt(rint(-5, 5)))), Rat.ONE];
    for (let i = 0; i < 3; i++) rint(-128, 128);
    cases.push({ tag: `corpus ${trial}`, coeffs });
  }
  seed = 20260905n;
  for (let trial = 0; trial < 200; trial++) {                          // random rational monic sextics
    const coeffs = [...Array.from({ length: 6 }, () => { const num = rint(-50, 50), den = rint(1, 12); return new Rat(BigInt(num), BigInt(den)); }), Rat.ONE];
    cases.push({ tag: `random ${trial}`, coeffs });
  }
  cases.push({ tag: 'Knuth ex. 22', coeffs: [-1, -3, 1, -2, 1, -3, 1].map(v => Rat.of(BigInt(v))) });
  cases.push({ tag: 'x^6 + x (on H, N=1)', coeffs: [0, 1, 0, 0, 0, 0, 1].map(v => Rat.of(BigInt(v))) });
  cases.push({ tag: 'x^6 (on H, N=0)', coeffs: [0, 0, 0, 0, 0, 0, 1].map(v => Rat.of(BigInt(v))) });
  const tally = { pan16: { ok: 0, onH: 0, onHtags: [], fail: [] }, pan07: { ok: 0, fail: [] } };
  for (const { tag, coeffs } of cases) {
    // Pan (16)
    try {
      const c = compilePan16(coeffs);
      const okPts = pts.every(x => evalLines(c.lines, x, mkRat).eq(P.evalAt(Q, coeffs, x)));
      const poly = pan16Poly(c.alphas);
      const okPoly = poly.length === 7 && poly.every((v, i) => v.eq(coeffs[i]));
      if (okPts && okPoly) tally.pan16.ok++; else tally.pan16.fail.push(tag);
    } catch (e) { if (/hypersurface/.test(e.message)) { tally.pan16.onH++; tally.pan16.onHtags.push(tag); } else tally.pan16.fail.push(tag + ': ' + e.message); }
    // Pan (0.7) at n = 6
    try {
      const c = compilePan07_6(coeffs);
      const okPts = pts.every(x => evalLines(c.lines, x, mkRat).eq(P.evalAt(Q, coeffs, x)));
      const poly = pan07_6Poly(c.lams, coeffs[0]);
      const okPoly = poly.length === 7 && poly.every((v, i) => v.eq(coeffs[i]));
      if (okPts && okPoly) tally.pan07.ok++; else tally.pan07.fail.push(tag);
    } catch (e) { tally.pan07.fail.push(tag + ': ' + e.message); }
  }
  console.log(`cases: ${cases.length} = 12 corpus sextics + 200 random rational monic sextics (num in [-50,50], den in [1,12], LCG seed 20260905) + Knuth ex. 22 + x^6 + x + x^6`);
  console.log(`Pan (16): chain == P at 7 points AND expanded chain == coefficient vector: ${tally.pan16.ok} ok, ${tally.pan16.onH} on H (no parameters, refused: ${tally.pan16.onHtags.join('; ')}), ${tally.pan16.fail.length} failures ${JSON.stringify(tally.pan16.fail)}`);
  console.log(`Pan (0.7) n=6: chain == P at 7 points AND expanded chain == coefficient vector: ${tally.pan07.ok} ok, ${tally.pan07.fail.length} failures ${JSON.stringify(tally.pan07.fail)}`);
  results.validate = { cases: cases.length, pan16: tally.pan16, pan07: tally.pan07 };
}

// ================= scale: coefficient scaling towards H =================
if (WHAT === 'all' || WHAT === 'scale') {
  console.log('--- scale: u3 = (1 + 2^-k) u3_H, u3_H = 2 a0 u4 - 5 a0^3, D = 2^-k u3_H (corpus sextics with u5 = +-3); k = inf is the point on H ---');
  results.scale = [];
  seed = 12345n;
  const polys = [];
  for (let trial = 0; trial < 12; trial++) {
    const coeffs = [...Array.from({ length: 6 }, () => new Rat(BigInt(rint(-5, 5)))), Rat.ONE];
    const xs = Array.from({ length: 3 }, () => new Rat(BigInt(rint(-128, 128)), 64n));
    polys.push({ trial, coeffs, xs });
  }
  const KS = [0, 2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 24, 28, 32, 36, 40, Infinity];
  const field = core.rationals();
  for (const { trial, coeffs, xs } of polys) {
    const u5 = coeffs[5];
    if (!(u5.eq(Rat.of(3n)) || u5.eq(Rat.of(-3n)))) continue;
    const a0 = u5.div(Rat.of(3n));
    const u3H = a0.mul(coeffs[4]).mul(Rat.of(2n)).sub(a0.mul(a0).mul(a0).mul(Rat.of(5n)));
    if (u3H.isZero()) { console.log(`  trial ${trial}: u3_H = 0, scaling cannot reach H; skipped`); continue; }
    console.log(`  corpus trial ${trial}: P = [${coeffs.map(c => c.toString()).join(', ')}], u3_H = ${u3H.toString()} (corpus u3 = ${coeffs[3].toString()}), x in {${xs.map(x => x.toString()).join(', ')}}`);
    console.log('    k      D        log10|a1| |a2| |a3| |a4| |a5|   log10A med  max   Pan err med    max        Horner max   this-paper max');
    for (const k of KS) {
      const u3 = k === Infinity ? u3H : u3H.mul(Rat.ONE.add(new Rat(1n, 1n << BigInt(k))));
      const c = coeffs.slice(); c[3] = u3;
      let row = { trial, k, u3: u3.toString() };
      try {
        const p = compilePan16(c);
        const ch = { lines: p.lines, cr: 1 };
        const As = [], errs = [];
        for (const x of xs) { const m = measure(ch, c, x, 6); As.push(m.logA); errs.push(m.err); }
        const hs = { lines: compileHorner(c, Q).lines, cr: 0 };
        const herr = xs.map(x => measure(hs, c, x, 6).err);
        const ours = { ours: core.compile_paper_params_chain(core.decode(6, c, field), null) };
        const oerr = xs.map(x => measure(ours, c, x, 6).err);
        const la = p.alphas.map(a => a.isZero() ? -Infinity : ratLog10(ratAbs(a)));
        const exactConsts = p.alphas.map(exactConst);
        row = { ...row, D: p.D.toString(), logD: ratLog10(ratAbs(p.D)), logAlpha: la, logA: summarize(As), err: summarize(errs), hornerErr: summarize(herr), oursErr: summarize(oerr), exactConsts };
        console.log(`    ${String(k).padStart(3)}  2^-${String(k).padEnd(2)}·${u3H.toString().padEnd(4)} ${la.slice(1).map(v => v.toFixed(1).padStart(5)).join(' ')}   ${row.logA.median.toFixed(1).padStart(6)} ${row.logA.max.toFixed(1).padStart(6)}   ${row.err.median.toExponential(2)}  ${row.err.max.toExponential(2)}   ${row.hornerErr.max.toExponential(2)}    ${row.oursErr.max.toExponential(2)}`);
      } catch (e) {
        row.error = e.message;
        console.log(`    ${String(k).padStart(3)}  D = 0: ${e.message}`);
      }
      results.scale.push(row);
    }
  }
}


// ================= odd: Belaga on the corpus degrees 7, 15, 31 (the harness's stream, DEGREES = [7,15,31]) =================
if (WHAT === 'all' || WHAT === 'odd') {
  console.log('--- odd degrees 7, 15, 31 (the stream of tools/numstab.mjs with DEGREES=[7,15,31], 12 trials): Belaga (numeric, website compiler; skipped when its constants are complex) and Horner (replay check) ---');
  seed = 12345n;
  results.odd = {};
  for (const n of [7, 15, 31]) {
    const rows = {};
    const stat = name => (rows[name] ??= { rho: null, rhoTrials: [], A: [], err: [], skipped: 0, complex: 0 });
    for (let trial = 0; trial < 12; trial++) {
      const coeffs = [...Array.from({ length: n }, () => new Rat(BigInt(rint(-5, 5)))), Rat.ONE];
      if (coeffs.every((c, i) => i === n || c.isZero())) continue;
      const xs = Array.from({ length: 3 }, () => new Rat(BigInt(rint(-128, 128)), 64n));
      const chains = {};
      chains.Horner = { lines: compileHorner(coeffs, Q).lines, cr: 0 };
      try {
        const b = compileBelaga(coeffs.map(ratToDouble));
        if (b.preprocessing === 'complex') { stat('Belaga').skipped++; stat('Belaga').complex++; }
        else chains.Belaga = { lines: b.lines, cr: 1 };
      } catch (e) { stat('Belaga').skipped++; (stat('Belaga').errors ??= []).push(`trial ${trial}: ${e.message}`); }
      for (const [name, ch] of Object.entries(chains)) {
        const st = stat(name);
        const r = rhoLines(ch.lines, ch.cr);
        st.rhoTrials.push(r); st.rho = Math.max(st.rho ?? 0, r);       // generic depth = max over trials
        for (const x of xs) { const m = measure(ch, coeffs, x, n); st.A.push(m.logA); st.err.push(m.err); }
      }
    }
    results.odd[n] = {};
    for (const name of ['Horner', 'Belaga']) {
      const st = rows[name]; if (!st || st.A.length === 0) { console.log(`n=${n} ${name.padEnd(16)} (no samples; skipped=${st?.skipped ?? 0}, complex=${st?.complex ?? 0})`); results.odd[n][name] = { samples: 0, skipped: st?.skipped ?? 0, complex: st?.complex ?? 0 }; continue; }
      const r = { rho: st.rho, rhoTrials: st.rhoTrials, logA: summarize(st.A), err: summarize(st.err), samples: st.err.length, skipped: st.skipped, complex: st.complex, overflow: st.err.filter(e => !Number.isFinite(e)).length, errors: st.errors };
      results.odd[n][name] = r;
      const rhoNote = st.rhoTrials.some(v => v !== st.rho) ? ` rho per trial=[${st.rhoTrials.join(',')}] (max = generic)` : '';
      console.log(`n=${n} ` + fmtRow(name, r) + (st.complex ? ` complex=${st.complex}` : '') + (st.errors ? ' ' + st.errors.join(' | ') : '') + rhoNote);
    }
  }
}

// ================= rho: generic rounding depth of every line-chain scheme =================
if (WHAT === 'all' || WHAT === 'rho') {
  console.log('--- rho: rounding depth on a generic monic polynomial (coefficients (2i+3)/7: no constant vanishes), n = 6, 7, 15, 31 ---');
  results.rhoGeneric = {};
  for (const n of [6, 7, 15, 31]) {
    const coeffs = [...Array.from({ length: n }, (_, i) => new Rat(BigInt(2 * i + 3), 7n)), Rat.ONE];
    const out = {};
    out.Horner = rhoLines(compileHorner(coeffs, Q).lines, 0);
    out.Estrin = rhoLines(compileEstrin(coeffs, Q).lines, 0);
    out['Rabin–Winograd'] = rhoLines(compileRW(coeffs, Q).lines, 1);
    try { out['Motzkin–Eve'] = rhoLines(compileMotzkin(coeffs.map(ratToDouble)).lines, 1); } catch (e) { out['Motzkin–Eve'] = null; }
    try { const b = compileBelaga(coeffs.map(ratToDouble)); out.Belaga = b.preprocessing === 'complex' ? null : rhoLines(b.lines, 1); } catch (e) { out.Belaga = null; }
    out['this paper'] = rhoOurs(core.compile_paper_params_chain(Array.from({ length: n }, (_, i) => new Rat(BigInt(2 * i + 3), 7n)), null));
    if (n === 6) {
      out['Pan (16)'] = rhoLines(compilePan16(coeffs).lines, 1);
      out['Pan (0.7)'] = rhoLines(compilePan07_6(coeffs).lines, 1);
      out['Knuth (12)'] = rhoLines(compileKnuth12(coeffs).lines, 1);
    }
    results.rhoGeneric[n] = out;
    console.log(`n=${n}: ` + Object.entries(out).map(([k, v]) => `${k}=${v === null ? 'n/a (complex constants on this polynomial)' : v}`).join('  '));
  }
  // cross-check: the maximum over the corpus/odd trials must equal the generic value
  const cmp = (n, block) => { for (const [name, r] of Object.entries(block ?? {})) { const g = results.rhoGeneric[n]?.[name]; if (g != null && r.rho != null && g !== r.rho) console.log(`  WARNING n=${n} ${name}: generic rho ${g} != max over trials ${r.rho}`); } };
  if (results.corpus) cmp(6, results.corpus);
  if (results.odd) for (const n of Object.keys(results.odd)) cmp(n, results.odd[n]);
}

if (OUT && existsSync(OUT)) { writeFileSync(`${OUT}/numstab_pan.json`, JSON.stringify(results, (k, v) => typeof v === 'bigint' ? v.toString() : v, 1)); console.log(`wrote ${OUT}/numstab_pan.json`); }
