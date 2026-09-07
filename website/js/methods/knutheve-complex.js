// Knuth-Eve "adaptation of coefficients" over the complex numbers.
//
// SCHEME.  Motzkin's / Knuth's (1962) scheme, i.e. the Knuth-Eve
// construction of motzkin.js WITHOUT Eve's real-rootedness search:
//     y = x + c,  w = y^2,  z = y + e  (n odd)  or  z = w + b*y + e  (n even),
//     p(x) = (...((z (w - s_1) + c_1)(w - s_2) + c_2)...)(w - s_K) + c_K,
//     K = ceil(n/2) - 1,
// where p(y) = E(w) + y O(w) is the even/odd split of the shifted polynomial,
// the nodes s_k are the K roots of O (they always exist over C once
// deg O = K), and the constants c_k are the Newton-form (divided-difference)
// values of E at the nodes.  Over C the shift is never needed to make the
// odd part split, so c = 0 - except for an even degree whose coefficient of
// x^(n-1) vanishes while the odd part does not (then deg O < K, e.g.
// x^n + x): such a polynomial is shifted by a small c chosen among a few
// candidates by the measured error.  An even polynomial (O = 0, e.g. x^n - 1
// at even n) needs no shift at all: any nodes work and the chain is Horner in
// w.  A shift is also tried when the unshifted chain rounds badly.
//
// MULTIPLICATION COUNT: floor(n/2) + 1 for a monic input
//     1 (w = y*y) + K = ceil(n/2) - 1 (peels) + [n even] (b*y),
// or floor(n/2) for an even polynomial (no b*y line), and one more for a
// non-monic input (the final scale line P = lc * P~, emitted HERE - the
// caller must not scale again); at most n + 1 additions.
//
// PREPROCESSING is numerical (complex roots by an Aberth-Ehrlich iteration
// in complex doubles, Newton-polished; divided differences in complex
// double-double); the printed constants are complex doubles.  Every complex
// constant is printed as the canonical token "(re+imi)" / "(re-imi)" (both
// parts always present, no spaces); a real-valued constant prints as a
// plain number, so a real polynomial whose nodes happen to be distinct reals
// yields a real chain (a repeated real node may keep a rounding-noise
// imaginary part and print as a complex token).
//
// VERIFICATION: the emitted chain (the printed rhs strings) is re-parsed and
// evaluated over complex doubles by motzkin.js's verifyLinesComplex at its
// SAMPLE_ZS - the real grid plus points with Im != 0 (three circles and the
// unit-box corners) - against direct Horner evaluation; maxRelError is
//   max |chain - horner| / max(|horner|, 1e-3 * sum_i |p_i| max(1,|z|)^i).

import {
  C, cAdd, cSub, cMul, cDiv, cNeg, cAbs, isZeroC, hornerComplex,
  fmt, fmtC, appendConst, verifyLinesComplex, SAMPLE_ZS, relErrorAtComplex,
} from './motzkin.js';

// The canonical complex token "(re+imi)" is defined once, in ../tokens.js
// (COMPLEX_SRC / COMPLEX_TOKEN); fmtC in motzkin.js prints it.

// ---------- coefficient coercion ----------

function toC(v, what = 'coefficient') {
  if (typeof v === 'number') return C(v, 0);
  if (typeof v === 'bigint') return C(Number(v), 0);
  if (v && typeof v === 'object') {
    if ('re' in v) {
      const part = u => (typeof u === 'number' ? u : typeof u === 'bigint' ? Number(u)
        : u && typeof u === 'object' && 'n' in u && 'd' in u ? Number(u.n) / Number(u.d) : Number(u));
      return C(part(v.re), part(v.im ?? 0));
    }
    if ('n' in v && 'd' in v) return C(Number(v.n) / Number(v.d), 0);
  }
  throw new Error(`bad ${what} ${String(v)}`);
}
const finiteC = z => Number.isFinite(z.re) && Number.isFinite(z.im);

// ---------- complex double-double ----------
// {re: [hi, lo], im: [hi, lo]}: the divided-difference constants are formed
// from the (exactly) shifted coefficients in double-double so that the
// printed 17-digit constants are correctly rounded values of the scheme.

const SPLIT = 134217729;                  // 2^27 + 1 (Dekker splitting)
function twoProd(a, b) {
  const p = a * b;
  const a1 = SPLIT * a, ah = a1 - (a1 - a), al = a - ah;
  const b1 = SPLIT * b, bh = b1 - (b1 - b), bl = b - bh;
  return [p, ((ah * bh - p) + ah * bl + al * bh) + al * bl];
}
function twoSum(a, b) {
  const s = a + b, bb = s - a;
  return [s, (a - (s - bb)) + (b - bb)];
}
function quick(s, e) { const h = s + e; return [h, e - (h - s)]; }
function ddAdd(a, b) { const [s, e] = twoSum(a[0], b[0]); return quick(s, e + a[1] + b[1]); }
function ddMulD(a, x) { const [p, e] = twoProd(a[0], x); return quick(p, e + a[1] * x); }
const ddNeg = a => [-a[0], -a[1]];
const ddNum = a => a[0] + a[1];

const cddOf = z => ({ re: [z.re, 0], im: [z.im, 0] });
const cddAdd = (a, b) => ({ re: ddAdd(a.re, b.re), im: ddAdd(a.im, b.im) });
/** complex dd times complex double */
const cddMulC = (a, z) => ({
  re: ddAdd(ddMulD(a.re, z.re), ddNeg(ddMulD(a.im, z.im))),
  im: ddAdd(ddMulD(a.re, z.im), ddMulD(a.im, z.re)),
});
const cddNum = a => C(ddNum(a.re), ddNum(a.im));
const cddAbs = a => cAbs(cddNum(a));

function cddHorner(pd, z) {               // cdd-poly at complex double z -> cdd
  let v = cddOf(C(0));
  for (let i = pd.length - 1; i >= 0; i--) v = cddAdd(cddMulC(v, z), pd[i]);
  return v;
}

/** The coefficients of p(y) = u(y - c) in complex double-double (Ruffini-Horner). */
function shiftedCoeffs(u, c) {
  const n = u.length - 1, V = u.map(cddOf), T = cNeg(c);
  if (!isZeroC(c)) for (let i = 0; i < n; i++) for (let j = n - 1; j >= i; j--) V[j] = cddAdd(V[j], cddMulC(V[j + 1], T));
  return V;
}

// ---------- complex root finder ----------

/** Fujiwara's bound for a complex polynomial (ascending). */
function rootBoundC(p) {
  const d = p.length - 1;
  let R = 0;
  for (let i = 1; i <= d; i++) R = Math.max(R, Math.pow(cAbs(p[d - i]) / cAbs(p[d]), 1 / i));
  return R > 0 ? 2 * R : 1;
}

// Newton polish in complex arithmetic (no real snap: over C a root is what it is).
function polishRootC(pc, z0) {
  let z = z0;
  for (let it = 0; it < 30; it++) {
    let dv = C(0), v = C(0);
    for (let i = pc.length - 1; i >= 0; i--) { dv = cAdd(cMul(dv, z), v); v = cAdd(cMul(v, z), pc[i]); }
    if (isZeroC(dv)) break;
    let step = cDiv(v, dv);
    const sa = cAbs(step), cap = 0.25 * (1 + cAbs(z));
    if (!Number.isFinite(sa)) break;
    if (sa > cap) step = C(step.re * cap / sa, step.im * cap / sa);
    const nz = cSub(z, step);
    if (!finiteC(nz)) break;
    z = nz;
    if (sa <= 1e-16 * (1 + cAbs(z))) break;
  }
  return z;
}

/**
 * All roots of a complex polynomial (ascending {re, im} coefficients), or
 * null when the iteration does not converge: Aberth-Ehrlich simultaneous
 * iteration from a circle inside Fujiwara's bound, Newton polish, residual
 * check |p(z)| <= 1e-8 sum |a_i| |z|^i.  Exact roots at 0 are split off.
 */
export function polyRootsC(coeffs) {
  const pc = coeffs.map(v => toC(v));
  let d = pc.length - 1;
  while (d > 0 && isZeroC(pc[d])) d--;
  if (d <= 0) return [];
  const a = pc.slice(0, d + 1).map(v => cDiv(v, pc[d]));  // monic
  let zeros = 0;
  while (zeros < d && isZeroC(a[zeros])) zeros++;
  const out = [];
  for (let i = 0; i < zeros; i++) out.push(C(0));
  const b = a.slice(zeros);                        // b[0] != 0
  d = b.length - 1;
  if (d === 0) return out;
  if (d === 1) return out.concat([cNeg(b[0])]);
  const R = rootBoundC(b);
  let r0 = Math.pow(cAbs(b[0]), 1 / d);
  r0 = Math.min(Math.max(r0, 1e-3 * R), R);
  const z = [];
  for (let k = 0; k < d; k++) {
    const ang = (2 * Math.PI * k) / d + 0.4;       // offset avoids the axes
    z.push(C(r0 * Math.cos(ang), r0 * Math.sin(ang)));
  }
  let converged = false;
  for (let it = 0; it < 500 && !converged; it++) {
    let maxRel = 0;
    for (let k = 0; k < d; k++) {
      let dv = C(0), v = C(0);
      for (let i = d; i >= 0; i--) { dv = cAdd(cMul(dv, z[k]), v); v = cAdd(cMul(v, z[k]), b[i]); }
      if (isZeroC(v)) continue;
      const w = isZeroC(dv) ? C(1e-8 * (1 + cAbs(z[k]))) : cDiv(v, dv);   // Newton step
      let sum = C(0);
      for (let j = 0; j < d; j++) {
        if (j === k) continue;
        const diff = cSub(z[k], z[j]);
        if (cAbs(diff) < 1e-300) continue;
        sum = cAdd(sum, cDiv(C(1), diff));
      }
      let step = cDiv(w, cSub(C(1), cMul(w, sum)));   // Aberth correction
      const sa = cAbs(step), cap = 0.5 * (1 + cAbs(z[k]));
      if (!Number.isFinite(sa)) {
        z[k] = C(R * Math.cos(2.4 * k + 0.1 * it), R * Math.sin(2.4 * k + 0.1 * it));
        maxRel = Infinity;
        continue;
      }
      if (sa > cap) step = C(step.re * cap / sa, step.im * cap / sa);
      z[k] = cSub(z[k], step);
      maxRel = Math.max(maxRel, cAbs(step) / (1 + cAbs(z[k])));
    }
    if (maxRel < 1e-15) converged = true;
  }
  const roots = z.map(zk => polishRootC(b, zk));
  for (const r of roots) {
    let scale = 0, rp = 1;
    const ar = cAbs(r);
    for (let i = 0; i <= d; i++) { scale += cAbs(b[i]) * rp; rp *= ar; }
    if (!(cAbs(hornerComplex(b, r)) <= 1e-8 * scale)) return null;
  }
  return out.concat(roots);
}

// ---------- verification against complex Horner ----------
// One verifier for every complex-coefficient row: motzkin.js's
// verifyLinesComplex (its rhs evaluator over complex doubles, the sample set
// SAMPLE_ZS - the real grid plus points with Im != 0 - and the |.|-relative
// error with the 1e-3 S(z) floor), re-exported here for the tests.
export { verifyLinesComplex, SAMPLE_ZS };
/** |got - p(z)| / max(|p(z)|, 1e-3 * sum_i |p_i| max(1,|z|)^i). */
export const relErrorAtC = relErrorAtComplex;

// ---------- constant quantization ----------

const quantD = (v, digits, tiny) => { const r = parseFloat(fmt(v, digits)); return Math.abs(r) <= tiny ? 0 : r; };
/** The complex value rounded to `digits` significant digits; a part below
 *  `tiny` (or below the printing resolution of the whole number) is 0. */
function quantC(z, digits, tiny = 0) {
  const t = Math.max(tiny, Math.pow(10, -digits) * cAbs(z));
  return C(quantD(z.re, digits, t), quantD(z.im, digits, t));
}

// ---------- chain emission ----------
// y = x + c, w = y*y, base z, then the peels from the innermost node
// sArr[K-1] to the outermost sArr[0] (cs[k] is the constant added after the
// multiplication by w - sArr[k]).  Height is the multiplicative depth.

function emitChain(n, c, sArr, cs, eBase, bLead, digits) {
  const odd = n % 2 === 1;
  const lines = [];
  const depth = { x: 0 };
  let mults = 0, adds = 0;
  const push = (lhs, rhs, mul, deps) => {
    lines.push({ lhs, rhs, mul });
    depth[lhs] = Math.max(0, ...deps.map(dp => depth[dp])) + (mul ? 1 : 0);
    if (mul) mults++;
  };
  let yName = 'x';
  if (!isZeroC(c)) {
    yName = 'y';
    push('y', appendConst('x', c, digits), false, ['x']);
    adds++;
  }
  push('w', `${yName} * ${yName}`, true, [yName]);
  let accExpr, accDeps;
  if (odd) {                                       // base: y + e
    accExpr = appendConst(yName, eBase, digits);
    if (accExpr !== yName) adds++;
    accDeps = [yName];
  } else if (!isZeroC(bLead)) {                    // base: w + b*y + e
    push('z', `${fmtC(bLead, digits)} * ${yName}`, true, [yName]);
    accExpr = appendConst('w + z', eBase, digits);
    adds += accExpr === 'w + z' ? 1 : 2;
    accDeps = ['w', 'z'];
  } else {
    accExpr = appendConst('w', eBase, digits);
    if (accExpr !== 'w') adds++;
    accDeps = ['w'];
  }
  const K = sArr.length;
  if (K === 0) push('P', accExpr, false, accDeps);   // degree 2: the base is the result
  for (let k = K - 1; k >= 0; k--) {               // innermost peel first
    const factor = appendConst('w', cNeg(sArr[k]), digits);
    if (factor !== 'w') adds++;
    const accAtom = /^[A-Za-z_]\w*$/.test(accExpr) ? accExpr : `(${accExpr})`;
    const rhs = `${accAtom} * (${factor})`;
    const withC = appendConst(rhs, cs[k], digits);
    if (withC !== rhs) adds++;
    const lhs = k === 0 ? 'P' : `t${K - 1 - k}`;
    push(lhs, withC, true, [...accDeps, 'w']);
    accExpr = lhs;
    accDeps = [lhs];
  }
  return { lines, mults, adds, height: depth.P };
}

// ---------- adapted constants and their numeric model ----------

/** Divided-difference constants of E at the nodes (complex double-double),
 *  quantized to the printed precision. */
function chainConstants(qcdd, sArr, digits) {
  const n = qcdd.length - 1;
  const E = [], O = [];
  for (let j = 0; j <= n; j++) (j % 2 ? O : E).push(qcdd[j]);
  let qSum = 0;
  for (const c of qcdd) qSum += cddAbs(c);
  const tiny = Math.pow(10, -digits) * qSum;
  const quant = v => quantC(cddNum(v), digits, tiny);
  let Ec = E.slice();
  const cs = [];
  for (const s of sArr) {
    const dE = Ec.length - 1, Eq = new Array(dE);
    Eq[dE - 1] = Ec[dE];
    for (let j = dE - 2; j >= 0; j--) Eq[j] = cddAdd(Ec[j + 1], cddMulC(Eq[j + 1], s));
    cs.push(quant(cddAdd(Ec[0], cddMulC(Eq[0], s))));
    Ec = Eq;
  }
  return { cs, eBase: quant(Ec[0]), bLead: n % 2 === 0 ? quant(O[O.length - 1]) : C(1) };
}

// Exactly the operations, in the same order, that the printed rhs strings
// perform (see emitChain and evalRhs), so the search optimizes the error of
// the chain that will actually be emitted.
function evalChainModel(n, c, sArr, k, x) {
  const odd = n % 2 === 1;
  const y = isZeroC(c) ? x : cAdd(x, c);
  const w = cMul(y, y);
  let acc;
  if (odd) acc = isZeroC(k.eBase) ? y : cAdd(y, k.eBase);
  else if (!isZeroC(k.bLead)) { acc = cAdd(w, cMul(k.bLead, y)); if (!isZeroC(k.eBase)) acc = cAdd(acc, k.eBase); }
  else acc = isZeroC(k.eBase) ? w : cAdd(w, k.eBase);
  for (let i = sArr.length - 1; i >= 0; i--) {
    const f = isZeroC(sArr[i]) ? w : cAdd(w, cNeg(sArr[i]));
    acc = cMul(acc, f);
    if (!isZeroC(k.cs[i])) acc = cAdd(acc, k.cs[i]);
  }
  return acc;
}

function modelError(pc, n, c, sArr, k) {
  let maxRel = 0;
  for (const z of SAMPLE_ZS) {
    const err = relErrorAtC(pc, z, evalChainModel(n, c, sArr, k, z));
    if (err > maxRel) maxRel = err;
    if (maxRel === Infinity) break;
  }
  return maxRel;
}

// ---------- peel orderings ----------

// Greedily pick the node minimizing the next divided-difference constant.
function greedyOrder(Edd, sArr, skipFirst) {
  let E = Edd.slice();
  const rem = sArr.slice(), out = [];
  let first = true;
  while (rem.length) {
    const vals = rem.map(s => cddAbs(cddHorner(E, s)));
    let bi = 0;
    if (first && skipFirst && rem.length > 1) {
      bi = [...vals.keys()].sort((a, b) => vals[a] - vals[b])[1];
    } else {
      for (let i = 1; i < rem.length; i++) if (vals[i] < vals[bi]) bi = i;
    }
    first = false;
    const s = rem.splice(bi, 1)[0];
    out.push(s);
    const dE = E.length - 1, Eq = new Array(dE);
    Eq[dE - 1] = E[dE];
    for (let j = dE - 2; j >= 0; j--) Eq[j] = cddAdd(E[j + 1], cddMulC(Eq[j + 1], s));
    E = Eq;
  }
  return out;
}

// Leja-style: start nearest zero, then maximize distance products.
function lejaOrder(sArr) {
  const rem = sArr.slice(), out = [];
  if (!rem.length) return out;
  let bi = 0;
  for (let i = 1; i < rem.length; i++) if (cAbs(rem[i]) < cAbs(rem[bi])) bi = i;
  out.push(rem.splice(bi, 1)[0]);
  while (rem.length) {
    let best = 0, bv = -Infinity;
    for (let i = 0; i < rem.length; i++) {
      let lp = 0;
      for (const o of out) lp += Math.log(cAbs(cSub(rem[i], o)) + 1e-300);
      if (lp > bv) { bv = lp; best = i; }
    }
    out.push(rem.splice(best, 1)[0]);
  }
  return out;
}

function altOrder(sortedAsc) {            // large, small, large2, small2, ...
  const out = [];
  let lo = 0, hi = sortedAsc.length - 1, takeHi = true;
  while (lo <= hi) { out.push(takeHi ? sortedAsc[hi--] : sortedAsc[lo++]); takeHi = !takeHi; }
  return out;
}

// ---------- peel-order search (same starts, local search and budget as motzkin.js) ----------

function searchOrder(pc, n, c, qcdd, sArr, digits, budget) {
  const Edd = qcdd.filter((_, j) => j % 2 === 0);
  const asc = sArr.slice().sort((a, b) => cAbs(a) - cAbs(b));
  const cache = new Map();
  let evals = 0;
  const cost = ord => {
    const key = ord.map(s => `${s.re},${s.im}`).join(';');
    let v = cache.get(key);
    if (v === undefined) {
      evals++;
      v = modelError(pc, n, c, ord, chainConstants(qcdd, ord, digits));
      cache.set(key, v);
    }
    return v;
  };
  let seed = 0x9e3779b9 ^ (n * 7919);
  const rnd = () => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed / 4294967296; };
  const shuffled = () => {
    const o = sArr.slice();
    for (let i = o.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [o[i], o[j]] = [o[j], o[i]]; }
    return o;
  };
  const starts = [
    greedyOrder(Edd, sArr, false), greedyOrder(Edd, sArr, true),
    asc.slice().reverse(), asc, lejaOrder(sArr), altOrder(asc),
  ];
  let best = null, bestErr = Infinity;
  const localSearch = ord0 => {
    let ord = ord0.slice(), cur = cost(ord);
    let improved = true;
    while (improved && evals < budget) {
      improved = false;
      for (let i = 0; i < ord.length && !improved; i++) {
        for (let j = i + 1; j < ord.length; j++) {
          const t = ord.slice();
          [t[i], t[j]] = [t[j], t[i]];
          const cst = cost(t);
          if (cst < cur) { ord = t; cur = cst; improved = true; break; }
          if (evals >= budget) break;
        }
      }
    }
    if (cur < bestErr) { bestErr = cur; best = ord; }
    return cur;
  };
  for (const st of starts) { localSearch(st); if (bestErr < 1e-10) return { ord: best, err: bestErr }; }
  for (let t = 0; t < 40 && evals < budget && bestErr >= 1e-10; t++) localSearch(shuffled());
  return { ord: best, err: bestErr };
}

// ---------- shifts ----------

const round7 = v => parseFloat(fmt(v, 7));

// The shift 0 first; then, only when needed (degenerate odd part, or a poor
// unshifted chain), a few small real and imaginary shifts.  Every printed
// shift is a short decimal, so the model and the printed chain agree.
function shiftCandidates(pc, n) {
  const RB = rootBoundC(pc);
  const mags = [...new Set([0.5 / n, 1 / n, 0.5, 1, 0.25 * RB, 0.5 * RB].map(round7))].filter(m => m > 0);
  const out = [];
  for (const m of mags) for (const dir of [C(-1), C(1), C(0, 1), C(0, -1)]) out.push(C(m * dir.re, m * dir.im));
  return out;
}

const SCREEN_BUDGET = 1200;               // model evaluations per candidate shift
const REFINE_BUDGET = 4000;               // ... for the best candidates
const REFINE_TOP = 3;
const GOOD = 1e-10;                       // stop searching shifts below this error
const SHIFT_IF_WORSE = 1e-9;              // try shifts when c = 0 rounds worse than this

function prepareShift(pc, n, c) {
  const K = Math.ceil(n / 2) - 1;
  const qcdd = shiftedCoeffs(pc, c);
  const O = [];
  for (let j = 1; j <= n; j += 2) O.push(cddNum(qcdd[j]));
  if (O.every(isZeroC)) {                  // even polynomial p(y) = E(w): no odd part, any nodes work; 0 = Horner in w
    const ord = Array.from({ length: K }, () => C(0));
    return { err: modelError(pc, n, c, ord, chainConstants(qcdd, ord, 17)), ord, qcdd, c };
  }
  // degenerate odd part: deg O < K, i.e. p_{n-1} - n c = 0 for even n (exact, as
  // in motzkin.js; a tolerance relative to the coefficient sum rejects healthy
  // rescaled Taylor polynomials whose lower coefficients are ~n!/j!)
  if (O.length !== K + 1 || cAbs(O[K]) === 0) return null;
  const roots = polyRootsC(O);
  if (!roots || roots.length !== K) return null;
  const s17 = roots.map(r => quantC(r, 17));
  if (!s17.every(finiteC)) return null;
  const r = searchOrder(pc, n, c, qcdd, s17, 17, SCREEN_BUDGET);
  return { err: r.err, ord: r.ord, qcdd, c };
}

// ---------- main entry point ----------

/**
 * Knuth-Eve adaptation over C for a polynomial with complex (or real)
 * coefficients, constant term first: coeffs[i] is a plain number or
 * {re, im}.  Any degree; a non-monic input is normalised and gets the final
 * scale line P = lc * P~ (counted in mults) - do not scale it again.
 */
export function compileKnuthEveComplex(coeffs) {
  if (!Array.isArray(coeffs) || coeffs.length === 0)
    throw new Error('need a nonempty coefficient array');
  const pc = coeffs.map(v => toC(v));
  if (!pc.every(finiteC)) throw new Error('coefficients must be finite numbers');
  const n = pc.length - 1, lc = pc[n];
  if (n > 0 && isZeroC(lc)) throw new Error('leading coefficient must be nonzero');
  const scaled = n > 0 && !(lc.re === 1 && lc.im === 0);
  const p = scaled ? pc.map(v => cDiv(v, lc)) : pc;
  const K = Math.ceil(n / 2) - 1;

  const finish = (chain, digits, note, extra) => {
    const lines = chain.lines.map(l => ({ ...l }));
    let { mults, adds, height } = chain;
    if (scaled) {
      lines[lines.length - 1].lhs = 'P̃';
      lines.push({ lhs: 'P', rhs: `${fmtC(lc, digits)} * P̃`, mul: true });
      mults += 1;
      height += 1;
    }
    const maxRelError = verifyLinesComplex(lines, pc);
    return {
      name: 'Knuth-Eve adaptation over C', lines, mults, adds, height,
      preprocessing: 'complex', preprocessingLabel: 'complex roots (numeric)',
      exact: false, maxRelError, note, ...extra,
    };
  };

  if (n <= 1) {                                    // elementary base cases
    let lines, adds = 0;
    if (n === 0) lines = [{ lhs: 'P', rhs: fmtC(p[0], 17), mul: false }];
    else {
      const rhs = appendConst('x', quantC(p[0], 17), 17);
      adds = rhs === 'x' ? 0 : 1;
      lines = [{ lhs: 'P', rhs, mul: false }];
    }
    return finish({ lines, mults: 0, adds, height: 0 }, 17,
      `elementary degree-${n} base case of the Knuth–Eve scheme over C`, { shift: C(0) });
  }

  // The unshifted polynomial, then (only if needed) a few small shifts; for
  // each the nodes are the complex roots of the odd part and the peel order
  // is searched.
  const prepared = [];
  const zero = prepareShift(p, n, C(0));
  if (zero) prepared.push(zero);
  if (!zero || zero.err > SHIFT_IF_WORSE) {
    for (const c of shiftCandidates(p, n)) {
      const cand = prepareShift(p, n, c);
      if (!cand) continue;
      prepared.push(cand);
      if (cand.err < GOOD) break;
    }
  }
  if (!prepared.length) {
    throw new Error('the odd part of the shifted polynomial is degenerate ' +
      'for every shift tried, or its roots could not be found');
  }
  prepared.sort((a, b) => a.err - b.err);
  let best = prepared[0];
  if (best.err >= GOOD) {
    for (const cand of prepared.slice(0, REFINE_TOP)) {
      const r = searchOrder(p, n, cand.c, cand.qcdd, cand.ord, 17, REFINE_BUDGET);
      if (r.err < best.err) best = { ...cand, err: r.err, ord: r.ord };
    }
  }

  // Emit with 13 printed digits when that is accurate enough, else 17; the
  // printed strings are what is verified.
  let chosen = null;
  for (const digits of [13, 17]) {
    const sArr = best.ord.map(s => quantC(s, digits));
    const k = chainConstants(best.qcdd, sArr, digits);
    const chain = emitChain(n, best.c, sArr, k.cs, k.eBase, k.bLead, digits);
    const err = verifyLinesComplex(chain.lines, p);
    if (!chosen || err < chosen.err) chosen = { err, chain, digits };
    if (err <= 1e-9) break;
  }
  if (!(chosen.err <= 1e-3)) {
    throw new Error('the adapted constants exceed double precision at this degree - ' +
      `max relative error ${chosen.err.toExponential(3)} over ${prepared.length} shifts and their peel orders`);
  }
  const c = best.c;
  const shiftText = isZeroC(c) ? 'no shift is needed over C' : `after the shift y = x + ${fmtC(c, 7)} ` +
    '(the odd part of the unshifted polynomial is degenerate or rounds badly)';
  const note = 'coefficient adaptation over C (Motzkin 1955; Knuth 1962; the Knuth–Eve scheme without ' +
    `Eve's real-rootedness search): ${shiftText}; the constants are the complex roots of the odd part ` +
    'and its divided differences - algebraic numbers found numerically, so the chain is only correct ' +
    'up to floating-point error' + (scaled ? '; the leading coefficient is restored by a final scale line' : '');
  return finish(chosen.chain, chosen.digits, note, { shift: c });
}
