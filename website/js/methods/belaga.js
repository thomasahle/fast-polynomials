// Belaga's preconditioning scheme for polynomial evaluation.
//
//   E. G. Belaga, "Some problems involved in the computation of polynomials",
//     Dokl. Akad. Nauk SSSR 123 (1958) 775-777, Theorem 1; displayed as
//     scheme (0.5) / Theorem 3.2 in V. Ya. Pan, "Methods of computing values
//     of polynomials", Russian Math. Surveys 21:1 (1966) 105-136.
//
// SCHEME. With y = s_1 = x (x + a_1),
//     s_2     = (s_1 + x + a_2) (s_1 + a_3) + a_4,
//     s_{k+1} = s_k (s_1 + a_{2k+1}) + a_{2k+2}          (k = 2, ..., l-1),
//     P       = s_l                     (n = 2l),
//     P       = x s_l + a_n             (n = 2l+1),
// so a monic degree-n polynomial costs exactly ceil(n/2) multiplications
// (l = floor(n/2) products for the s_k plus one for x*s_l when n is odd) and
// n + 1 additions: 1 for y, 4 for s_2, 2 for each further s_k and 1 for
// a_n, i.e. 2l + 1 + [n odd] = n + 1 (Pan 1966: scheme (0.5) attains the
// lower bounds of his Theorem 2.1 - n additions, floor(n/2) + 1
// multiplications - "to within one addition" for even n; a general, non-
// monic polynomial costs one more multiplication for the leading
// coefficient, the floor(n/2) + 2 of Knuth TAOCP 4.6.4).  For even n the
// multiplication count is Pan's bound; Motzkin's ceil(n/2) bound is one
// lower, which is why this scheme is only a comparison row here.
//
// PREPROCESSING (the reason the constants live in R or C, not Q).  Writing
// s_l = A(y) + x B(y) with y = x^2 + a_1 x, the recurrence gives
//     B(y) = (y + a_3)(y + a_5) ... (y + a_{2l-1})    (monic, degree l-1),
// and A monic of degree l.  Comparing the x^{n-1} coefficient forces
// a_1 = (c_{n-1} - 1)/l, which is rational; but a_3, a_5, ... are the negated
// roots of B, and B is whatever the (unique) decomposition P = A(y) + x B(y)
// produces, so for n >= 6 the scheme needs every root of a polynomial of
// degree l-1 - real or complex.  The scheme has exactly n parameters for the
// n coefficients of a monic polynomial: there is NO free parameter (no shift
// as in the Motzkin-Eve method) that could move the roots of B onto the real
// line, and Pan (1966, p. 108) states outright that in scheme (0.5) the
// parameters "turn out, in general, to be complex for real coefficients" -
// his scheme (0.7) is the real-parameter alternative, at the cost of one more
// multiplication.  So complex constants here are a property of the scheme,
// not a failure: the row reports them as such.
// Then a_{2k} = A_k(-a_{2k-1}) and A_{k-1} = (A_k - a_{2k}) / (y + a_{2k-1})
// peel A down to A_2 = y^2 + (a_2 + a_3) y + a_2 a_3 + a_4.  For odd n one
// first strips the x factor: P = [y B(y) + a_n] + x [A(y) - a_1 B(y)].
// For n <= 5 the polynomial B is linear, so the preprocessing is rational.
// Degree 3 uses the two-multiplication form P = (x + a_1)(x^2 + a_2) + a_3.
//
// ARITHMETIC.  The decomposition P = A(y) + x B(y) is computed exactly
// (dyadic rationals on BigInt: every double is one) from the double
// coefficients and the printed a_1; the roots of B come from an Aberth iteration in doubles polished by
// Newton steps whose residuals B(z), B'(z) are evaluated exactly, so each
// simple root is correct to the last bit.  A complex root pair r, conj(r)
// occupies two adjacent factors (y + a)(y + conj a) = y^2 + 2 Re(a) y + |a|^2
// and the peeling divides by that REAL quadratic: of the three constants a
// pair contributes, a_{2k+1} = -r and a_{2k+3} = -conj(r) are conjugates,
// the inner additive constant is real and only the outer one is complex.
// Every other constant is real by construction (no imaginary parts have to
// be "recognised" as rounding noise), and all of them are peeled with the
// rounded (printed) values of the nodes so that the chain is consistent to
// the last printed digit.  The order of the factors is free; it changes the
// size of the constants and the rounding error of the chain a lot, so it is
// searched (heuristic orders plus a swap-based local search), scored by the
// verification below.
//
// VERIFICATION as in motzkin.js: the emitted rhs strings are re-parsed and
// evaluated at 69 sample points against Horner (over complex doubles when the
// constants are complex); constants are printed with 13 significant digits,
// escalated to 17 when the verification demands it.  compileBelaga throws
// only if the best chain is wrong to more than 1e-3: like every adapted
// chain its rounding error grows with the degree (the intermediate values
// are of the size of A and x B separately, which can far exceed P), and
// unlike Motzkin-Eve there is no shift to improve the conditioning.

import {
  C, cAbs, cDiv, isZeroC, polyRoots, fmt, appendConst, verifyLines,
  rat, rSub, rDiv, R1, ratFromDouble, ratToDouble,
} from './motzkin.js';

// ---------- dyadic arithmetic: n / 2^e on BigInt ----------
// Every double is dyadic, and so is everything the peeling produces from
// doubles by ring operations, so the preprocessing is exact without any gcd.

const dy = (n, e = 0) => ({ n, e });
const D0 = dy(0n), D1 = dy(1n);
function dyFromDouble(v) {
  if (!Number.isFinite(v)) throw new Error(`non-finite value ${v}`);
  if (v === 0) return D0;
  let e = 0;
  while (!Number.isInteger(v)) { v *= 2; e++; }
  return dy(BigInt(v), e);
}
function dyAdd(a, b) {
  const e = Math.max(a.e, b.e);
  return dy((a.n << BigInt(e - a.e)) + (b.n << BigInt(e - b.e)), e);
}
function dySub(a, b) {
  const e = Math.max(a.e, b.e);
  return dy((a.n << BigInt(e - a.e)) - (b.n << BigInt(e - b.e)), e);
}
const dyMul = (a, b) => dy(a.n * b.n, a.e + b.e);
const dyIsZero = a => a.n === 0n;
const bitLen = x => (x === 0n ? 0 : (x < 0n ? -x : x).toString(2).length);
function dyToDouble(a) {
  if (a.n === 0n) return 0;
  const neg = a.n < 0n, m = neg ? -a.n : a.n;
  const sh = bitLen(m) - 64;
  const q = sh > 0 ? m >> BigInt(sh) : m << BigInt(-sh);
  const v = Number(q) * Math.pow(2, sh - a.e);
  return neg ? -v : v;
}

// ---------- exact decomposition P = A(y) + x B(y), y = x^2 + a1 x ----------

function splitXY(p, a1) {                          // dyadic arrays, ascending
  let cur = p.slice();
  const A = [], B = [];
  for (;;) {
    if (cur.length <= 2) { A.push(cur[0] ?? D0); B.push(cur[1] ?? D0); break; }
    const m = cur.length - 1;
    const q = new Array(m - 1).fill(D0);
    const rem = cur.slice();
    for (let i = m; i >= 2; i--) { const c = rem[i]; q[i - 2] = c; rem[i] = D0; rem[i - 1] = dySub(rem[i - 1], dyMul(c, a1)); }
    A.push(rem[0]); B.push(rem[1]);
    cur = q;
  }
  return [A, B];
}

// Newton polish of a root of the dyadic polynomial B (ascending) at the
// complex double z, with B(z) and B'(z) evaluated exactly (Gaussian integers
// after clearing the powers of two; the Newton step is their ratio).
function polishExact(B, z) {
  const d = B.length - 1;
  const eB = Math.max(...B.map(c => c.e));
  const Bn = B.map(c => c.n << BigInt(eB - c.e));
  for (let it = 0; it < 4; it++) {
    const zr = dyFromDouble(z.re), zi = dyFromDouble(z.im);
    const e = Math.max(zr.e, zi.e), Zr = zr.n << BigInt(e - zr.e), Zi = zi.n << BigInt(e - zi.e);
    const up = 1n << BigInt(e);
    // V_i = V_{i+1} Z + Bn_i 2^(e (d - i)),  DV_i = DV_{i+1} Z + V_{i+1} 2^e
    let vr = 0n, vi = 0n, dr = 0n, di = 0n, pw = 1n;
    for (let i = d; i >= 0; i--) {
      [dr, di] = [dr * Zr - di * Zi + vr * up, dr * Zi + di * Zr + vi * up];
      [vr, vi] = [vr * Zr - vi * Zi + Bn[i] * pw, vr * Zi + vi * Zr];
      pw *= up;
    }
    const sh = BigInt(Math.max(0, Math.max(bitLen(dr), bitLen(di)) - 200));
    const v = C(Number(vr >> sh), Number(vi >> sh)), dv = C(Number(dr >> sh), Number(di >> sh));
    if (isZeroC(v) || isZeroC(dv)) break;
    const step = cDiv(v, dv);
    if (!Number.isFinite(step.re) || !Number.isFinite(step.im)) break;
    const cap = 0.1 * (1 + cAbs(z)), sa = cAbs(step);
    if (sa > cap) break;                           // not in the Newton basin: keep the Aberth root
    z = C(z.re - step.re, z.im === 0 ? 0 : z.im - step.im);
    if (sa <= 1e-17 * (1 + cAbs(z))) break;
  }
  return z;
}

// Real roots and conjugate pairs of B: [{ re }, ...] and [{ re, im > 0 }, ...]
function rootBlocks(roots) {
  const reals = [], pairs = [];
  const cplx = [];
  for (const r of roots) (r.im === 0 ? reals : cplx).push(r);
  while (cplx.length) {
    const z = cplx.shift();
    let bj = -1, bd = Infinity;
    for (let j = 0; j < cplx.length; j++) {
      const dd = Math.hypot(cplx[j].re - z.re, cplx[j].im + z.im);
      if (dd < bd) { bd = dd; bj = j; }
    }
    if (bj < 0) return null;                       // an unpaired complex root: not a real polynomial's root set
    const z2 = cplx.splice(bj, 1)[0];
    pairs.push(C(0.5 * (z.re + z2.re), 0.5 * Math.abs(z.im - z2.im)));
  }
  return { reals: reals.map(r => ({ type: 'r', r: r.re })), pairs: pairs.map(r => ({ type: 'p', r })) };
}

// ---------- exact peeling of A for a given factor order ----------
// order: blocks from the innermost (the a_3 block) outward.  Returns the
// constants a_2 .. a_{2l} as complex doubles (already rounded to `digits`).

const quant = (v, digits) => parseFloat(fmt(v, digits));

// A = Q (y + a) + rho, exact
function divLinear(A, a) {
  const d = A.length - 1, Q = new Array(d);
  let carry = A[d];
  for (let j = d - 1; j >= 0; j--) { Q[j] = carry; carry = dySub(A[j], dyMul(a, carry)); }
  return [Q, carry];
}
// A = Q (y^2 + s y + t) + (lam y + mu), exact
function divQuad(A, s, t) {
  const rem = A.slice(), d = A.length - 1;
  const Q = new Array(Math.max(0, d - 1)).fill(D0);
  for (let i = d; i >= 2; i--) {
    const c = rem[i];
    Q[i - 2] = c;
    rem[i] = D0;
    rem[i - 1] = dySub(rem[i - 1], dyMul(c, s));
    rem[i - 2] = dySub(rem[i - 2], dyMul(c, t));
  }
  return [Q, rem[1] ?? D0, rem[0] ?? D0];
}

function decode(A0, order, digits) {
  const alphas = [];                               // index k -> a_k (complex double)
  // node positions: block j occupies k, (k+1 for a pair); a_{2k+1} = -r
  const pos = [];
  let k = 1;
  for (const b of order) { pos.push(k); k += b.type === 'p' ? 2 : 1; }
  let A = A0.slice();
  for (let j = order.length - 1; j >= 1; j--) {
    const b = order[j], kk = pos[j];
    if (b.type === 'r') {
      const a = quant(-b.r, digits);
      alphas[2 * kk + 1] = C(a);
      const [Q, rho] = divLinear(A, dyFromDouble(a));
      alphas[2 * kk + 2] = C(quant(dyToDouble(rho), digits));
      A = Q;
    } else {
      const ar = quant(-b.r.re, digits), ai = quant(-b.r.im, digits);   // a = -r (inner), conj(a) (outer)
      alphas[2 * kk + 1] = C(ar, ai);
      alphas[2 * kk + 3] = C(ar, -ai);
      const arD = dyFromDouble(ar), aiD = dyFromDouble(ai);
      const [Q, lam, mu] = divQuad(A, dyMul(dy(2n), arD), dyAdd(dyMul(arD, arD), dyMul(aiD, aiD)));
      const lq = quant(dyToDouble(lam), digits);
      alphas[2 * kk + 2] = C(lq);
      // outer constant: mu - lam conj(a) = (mu - lq ar) + i (lq ai)
      alphas[2 * kk + 4] = C(quant(dyToDouble(dySub(mu, dyMul(dyFromDouble(lq), arD))), digits), quant(lq * ai, digits));
      A = Q;
    }
  }
  // base block at position 1
  const b = order[0];
  if (b.type === 'r') {
    // A = y^2 + p y + q = (y + a_2)(y + a_3) + a_4
    const a3 = quant(-b.r, digits);
    alphas[3] = C(a3);
    const a2 = quant(dyToDouble(dySub(A[1], dyFromDouble(a3))), digits);
    alphas[2] = C(a2);
    alphas[4] = C(quant(dyToDouble(dySub(A[0], dyMul(dyFromDouble(a2), dyFromDouble(a3)))), digits));
  } else {
    // A = (y + a_2)(y + a_3)(y + a_5) + a_4 (y + a_5) + a_6,  a_5 = conj(a_3)
    const ar = quant(-b.r.re, digits), ai = quant(-b.r.im, digits);
    alphas[3] = C(ar, ai);
    alphas[5] = C(ar, -ai);
    const arD = dyFromDouble(ar), aiD = dyFromDouble(ai);
    const s = dyMul(dy(2n), arD), t = dyAdd(dyMul(arD, arD), dyMul(aiD, aiD));
    const [Q] = divQuad(A, s, t);                  // Q = y + a_2'
    const a2 = quant(dyToDouble(Q[0]), digits);
    alphas[2] = C(a2);
    // remainder of A - (y + a2)(y^2 + s y + t), keeping its linear part
    const a2D = dyFromDouble(a2);
    const prod = [dyMul(a2D, t), dyAdd(t, dyMul(a2D, s)), dyAdd(s, a2D), D1];
    const rem = A.map((c, i) => dySub(c, prod[i] ?? D0));
    const lq = quant(dyToDouble(rem[1]), digits);
    alphas[4] = C(lq);
    alphas[6] = C(quant(dyToDouble(dySub(rem[0], dyMul(dyFromDouble(lq), arD))), digits), quant(lq * ai, digits));
  }
  return alphas;
}

// ---------- chain emission ----------

function emit(n, a1, alphas, aN, digits) {
  const lines = [];
  const depth = { x: 0 };
  let mults = 0, adds = 0;
  const push = (lhs, rhs, mul, deps) => {
    lines.push({ lhs, rhs, mul });
    depth[lhs] = 1 + Math.max(0, ...deps.map(dp => depth[dp]));
    if (mul) mults++;
  };
  const l = Math.floor(n / 2), odd = n % 2 === 1;
  const yFactor = appendConst('x', C(a1), digits);
  if (yFactor !== 'x') adds++;
  push('y', `x * (${yFactor})`, true, ['x']);
  // s_2
  const f1 = appendConst('y + x', alphas[2], digits); adds += 1 + (f1 !== 'y + x' ? 1 : 0);
  const f2 = appendConst('y', alphas[3], digits); if (f2 !== 'y') adds++;
  let rhs = `(${f1}) * (${f2})`;
  const w2 = appendConst(rhs, alphas[4], digits); if (w2 !== rhs) adds++;
  let acc = (l === 2 && !odd) ? 'P' : (l === 2 ? 's' : 'z');
  push(acc, w2, true, ['x', 'y']);
  for (let k = 2; k < l; k++) {
    const fac = appendConst('y', alphas[2 * k + 1], digits); if (fac !== 'y') adds++;
    rhs = `${acc} * (${fac})`;
    const w = appendConst(rhs, alphas[2 * k + 2], digits); if (w !== rhs) adds++;
    const lhs = (k === l - 1) ? (odd ? 's' : 'P') : `t${k - 1}`;
    push(lhs, w, true, [acc, 'y']);
    acc = lhs;
  }
  if (odd) {
    rhs = `x * ${acc}`;
    const w = appendConst(rhs, C(aN), digits); if (w !== rhs) adds++;
    push('P', w, true, ['x', acc]);
  }
  return { lines, mults, adds, height: depth.P };
}

// ---------- factor-order search ----------

function heuristicOrders(blocks) {
  const mag = b => (b.type === 'r' ? Math.abs(b.r) : cAbs(b.r));
  const re = b => (b.type === 'r' ? b.r : b.r.re);
  const by = f => blocks.slice().sort((a, b) => f(a) - f(b));
  const realsFirst = ord => ord.filter(b => b.type === 'r').concat(ord.filter(b => b.type === 'p'));
  const seen = new Set(), out = [];
  const add = ord => { const key = ord.map(b => blocks.indexOf(b)).join(','); if (!seen.has(key)) { seen.add(key); out.push(ord); } };
  add(by(mag).reverse());                          // largest factor innermost
  add(realsFirst(by(mag).reverse()));
  add(by(mag));
  add(by(re));
  add(by(re).reverse());
  add(realsFirst(by(mag)));
  add(blocks.slice());
  return out;
}

function searchOrder(blocks, cost, budget) {
  let evals = 0, best = null, bestErr = Infinity;
  const cache = new Map();
  const score = ord => {
    const key = ord.map(b => blocks.indexOf(b)).join(',');
    let v = cache.get(key);
    if (v === undefined) { evals++; v = cost(ord); cache.set(key, v); }
    return v;
  };
  let seed = 0x2545f491 ^ (blocks.length * 7919);
  const rnd = () => { seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0; return seed / 4294967296; };
  const localSearch = ord0 => {
    let ord = ord0.slice(), cur = score(ord);
    let improved = true;
    while (improved && evals < budget) {
      improved = false;
      for (let i = 0; i < ord.length && !improved; i++) {
        for (let j = i + 1; j < ord.length; j++) {
          const t = ord.slice();
          [t[i], t[j]] = [t[j], t[i]];
          const c = score(t);
          if (c < cur) { ord = t; cur = c; improved = true; break; }
          if (evals >= budget) break;
        }
      }
    }
    if (cur < bestErr) { bestErr = cur; best = ord; }
  };
  for (const st of heuristicOrders(blocks)) { localSearch(st); if (bestErr < 1e-11) return { ord: best, err: bestErr }; }
  for (let t = 0; t < 20 && evals < budget && bestErr >= 1e-11; t++) {
    const o = blocks.slice();
    for (let i = o.length - 1; i > 0; i--) { const j = Math.floor(rnd() * (i + 1)); [o[i], o[j]] = [o[j], o[i]]; }
    localSearch(o);
  }
  return { ord: best, err: bestErr };
}

// ---------- main entry point ----------

const ORDER_BUDGET = 160;                 // chain verifications per precision level

export function compileBelaga(coeffs) {
  if (!Array.isArray(coeffs) || coeffs.length < 4)
    throw new Error('Belaga: need a degree >= 3 polynomial');
  const p = coeffs.map(Number);
  if (!p.every(Number.isFinite))
    throw new Error('Belaga: coefficients must be finite numbers');
  const n = p.length - 1;
  if (p[n] !== 1)
    throw new Error('Belaga: input must be monic (coeffs[n] === 1)');

  const finish = (chain, mode, err, pairs = 0) => {
    const degB = Math.floor(n / 2) - 1;
    let note = 'Belaga 1958 (Pan 1966, scheme (0.5)): ceil(n/2) multiplications, n+1 additions; ';
    if (n <= 5) note += 'preprocessing is rational at this degree';
    else if (mode === 'real') {
      note += `the constants a_3, a_5, ... are the roots of a degree-${degB} polynomial B ` +
        'fixed by the input (a_1 = (c_{n-1} - 1)/l is rational); they happen to be real here ' +
        'but are algebraic numbers found numerically, so the chain is only correct up to floating-point error';
    } else {
      note += `needs complex parameters for this polynomial: B (degree ${degB}, fixed by the input) has ` +
        `${pairs} complex-conjugate root pair${pairs === 1 ? '' : 's'}, and the scheme has no free ` +
        'parameter (a_1 = (c_{n-1} - 1)/l is forced) that could make them real - Pan 1966 notes that ' +
        'the parameters of scheme (0.5) are in general complex for real coefficients; the chain below ' +
        'evaluates P over C (complex arithmetic roughly doubles the real cost)';
    }
    return {
      name: 'Belaga scheme',
      lines: chain.lines, mults: chain.mults, adds: chain.adds, height: chain.height,
      preprocessing: mode, exact: false, note, maxRelError: err,
    };
  };

  if (n === 3) {                                       // (x + a1)(x^2 + a2) + a3
    const a1 = p[2], a2 = p[1], a3 = p[0] - p[1] * p[2];
    let best = null;
    for (const digits of [13, 17]) {
      const lines = [{ lhs: 'y', rhs: 'x * x', mul: true }];
      const f = appendConst('x', C(a1), digits), g = appendConst('y', C(a2), digits);
      const rhs = `(${f}) * (${g})`;
      lines.push({ lhs: 'P', rhs: appendConst(rhs, C(a3), digits), mul: true });
      const adds = (f !== 'x') + (g !== 'y') + (lines[1].rhs !== rhs);
      const err = verifyLines(lines, p);
      if (!best || err < best.err) best = { err, chain: { lines, mults: 2, adds, height: 2 } };
      if (err <= 1e-9) break;
    }
    return finish(best.chain, 'real', best.err);
  }

  const l = Math.floor(n / 2), odd = n % 2 === 1;
  const uDy = p.map(dyFromDouble);
  const a1exact = rDiv(rSub(ratFromDouble(p[n - 1]), R1), rat(BigInt(l)));
  let best = null;
  for (const digits of [13, 17]) {
    const a1 = quant(ratToDouble(a1exact), digits);
    let [A, B] = splitXY(uDy, dyFromDouble(a1)), aN = 0;
    if (odd) {
      // P = [y B + a_n] + x [A - a1 B]:  the split gave A' = y B + a_n, B' = A - a1 B
      const Ap = A, Bp = B;
      aN = quant(dyToDouble(Ap[0] ?? D0), digits);
      B = Ap.slice(1);                                 // (A' - a_n)/y
      A = Bp.map((v, i) => dyAdd(v, dyMul(dyFromDouble(a1), B[i] ?? D0)));   // B' + a1 B
    }
    A = A.slice(0, l + 1); B = B.slice(0, l);
    while (A.length < l + 1) A.push(D0);
    while (B.length < l) B.push(D0);
    // A is monic exactly; B is monic up to the rounding of a1 (its leading
    // coefficient is 1 + l (a1 - a1exact)), which does not move its roots
    if (dyIsZero(B[l - 1]) || !dyIsZero(dySub(A[l], D1)))
      throw new Error('Belaga: preprocessing failed (decomposition P = A(y) + x B(y) is not monic)');
    const Bd = B.map(dyToDouble);
    let roots = polyRoots(Bd);
    if (!roots) throw new Error('Belaga: the root-finding iteration failed to converge on the roots of B');
    roots = roots.map(z => polishExact(B, z));
    const blk = rootBlocks(roots);
    if (!blk) throw new Error('Belaga: preprocessing failed (the roots of B do not form conjugate pairs)');
    const blocks = blk.reals.concat(blk.pairs);
    const pairs = blk.pairs.length;
    const cost = ord => {
      const alphas = decode(A, ord, digits);
      const chain = emit(n, a1, alphas, aN, digits);
      return verifyLines(chain.lines, p);
    };
    const r = searchOrder(blocks, cost, ORDER_BUDGET);
    const chain = emit(n, a1, decode(A, r.ord, digits), aN, digits);
    if (!best || r.err < best.err) best = { err: r.err, chain, mode: pairs ? 'complex' : 'real', pairs };
    if (best.err <= 1e-9) break;
  }
  if (!(best.err <= 1e-3)) {
    throw new Error('Belaga: the constants exceed double precision for this polynomial - max relative error ' +
      `${best.err.toExponential(3)} (a_1 = (c_{n-1} - 1)/l and the roots of B are fixed by the input, so ` +
      'unlike Motzkin-Eve there is no shift to improve the conditioning of the chain; its intermediate ' +
      'values A(y) and x B(y) far exceed P(x) here)');
  }
  return finish(best.chain, best.mode, best.err, best.pairs);
}
