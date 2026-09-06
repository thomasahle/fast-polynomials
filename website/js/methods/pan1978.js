// Pan's optimal odd-degree schemes over C.
//
//   V. Ya. Pan, "Computational complexity of computing polynomials over the
//   fields of real and complex numbers", STOC 1978, pp. 162-172.
//
// This module implements scheme (4) in degree 11 and the full family (3) in
// every odd degree n = 2k+1 >= 13.  These schemes are not monic-only: the
// leading coefficient is carried by a cancellation inside the circuit, so a
// non-monic input does not need a final scaling multiplication.  The count is
//     (n+1)/2 multiplications and n+2 additions
// when all displayed shifts are nonzero.  An even degree n >= 12 is reduced
// to the odd degree n-1 by P(x) = x·Q(x) + a_0 (one more multiplication, so
// n/2 + 1 in all, and one more addition unless a_0 = 0).
//
// Pan proves that scheme (3) represents almost every complex polynomial, and
// proves that scheme (4) represents every degree-11 polynomial.  He does not
// print a coefficient-to-parameter formula.  Consequently this comparison
// compiler follows a solution branch of the EXPLICIT coefficient map by
// predictor/corrector homotopy continuation.  It is deliberately labelled
// numeric and verifies the literal emitted chain independently at 69 points.
// Failure to track a branch is reported as such; it is not evidence that the
// target lies on Pan's exceptional algebraic set.
//
// COEFFICIENTS.  The input is an ascending array (constant term first) of
// plain numbers or complex {re, im} doubles.  The scheme is Pan's complex
// scheme in either case; a real input is verified at the 69 real sample
// points of verifyLines (its real/complex parameter report is unchanged),
// and an input with a nonzero imaginary part is verified by
// verifyLinesComplex at real and non-real sample points against complex
// Horner.  Constants are printed with fmtC's canonical "(a+bi)" token.

import {
  C, cAbs, isZeroC, appendConst, verifyLines, verifyLinesComplex, toComplex,
} from './motzkin.js';

// A wire is a polynomial in x together with its forward derivatives with
// respect to all D parameters.  Coefficients and derivatives are stored as
// separate real/imaginary Float64Arrays; J is row-major (coefficient, param).

function zeroWire(deg, D) {
  return {
    vr: new Float64Array(deg + 1), vi: new Float64Array(deg + 1),
    jr: new Float64Array((deg + 1) * D), ji: new Float64Array((deg + 1) * D), D,
  };
}

function xWire(D) {
  const w = zeroWire(1, D);
  w.vr[1] = 1;
  return w;
}

function shifted(a, param, f) {
  const n = a.vr.length, D = a.D;
  const w = {
    vr: a.vr.slice(), vi: a.vi.slice(), jr: a.jr.slice(), ji: a.ji.slice(), D,
  };
  w.vr[0] += f[param].re;
  w.vi[0] += f[param].im;
  w.jr[param] += 1;
  return w;
}

function addWire(a, b, sign = 1, maxDegree = Infinity) {
  const D = a.D, n = Math.min(Math.max(a.vr.length, b.vr.length), maxDegree + 1);
  const w = zeroWire(n - 1, D);
  for (let i = 0; i < n; i++) {
    if (i < a.vr.length) {
      w.vr[i] += a.vr[i]; w.vi[i] += a.vi[i];
      const ao = i * D, wo = i * D;
      for (let p = 0; p < D; p++) { w.jr[wo + p] += a.jr[ao + p]; w.ji[wo + p] += a.ji[ao + p]; }
    }
    if (i < b.vr.length) {
      w.vr[i] += sign * b.vr[i]; w.vi[i] += sign * b.vi[i];
      const bo = i * D, wo = i * D;
      for (let p = 0; p < D; p++) { w.jr[wo + p] += sign * b.jr[bo + p]; w.ji[wo + p] += sign * b.ji[bo + p]; }
    }
  }
  return w;
}

function mulWire(a, b) {
  const D = a.D, na = a.vr.length, nb = b.vr.length;
  const w = zeroWire(na + nb - 2, D);
  for (let i = 0; i < na; i++) {
    const ar = a.vr[i], ai = a.vi[i], ao = i * D;
    for (let j = 0; j < nb; j++) {
      const br = b.vr[j], bi = b.vi[j], bo = j * D, k = i + j, ko = k * D;
      w.vr[k] += ar * br - ai * bi;
      w.vi[k] += ar * bi + ai * br;
      for (let p = 0; p < D; p++) {
        const dar = a.jr[ao + p], dai = a.ji[ao + p];
        const dbr = b.jr[bo + p], dbi = b.ji[bo + p];
        w.jr[ko + p] += dar * br - dai * bi + ar * dbr - ai * dbi;
        w.ji[ko + p] += dar * bi + dai * br + ar * dbi + ai * dbr;
      }
    }
  }
  return w;
}

function nested(start, quadratic, count, firstParam, f) {
  let acc = start;
  for (let j = 0; j < count; j++)
    acc = mulWire(shifted(acc, firstParam + 2 * j, f), shifted(quadratic, firstParam + 2 * j + 1, f));
  return acc;
}

// The literal polynomial coefficient map for one of Pan's displayed schemes.
function coefficientMap(f, spec) {
  const n = spec.n, D = n + 1, x = xWire(D);
  const q2 = mulWire(shifted(x, 0, f), shifted(x, 0, f));
  const p3 = mulWire(shifted(x, 1, f), shifted(q2, 2, f));

  if (n === 11) {
    const p5 = mulWire(shifted(p3, 3, f), shifted(q2, 4, f));
    const p5b = mulWire(shifted(p3, 5, f), shifted(q2, 6, f));
    const q3 = addWire(p5b, p5, -1, 3);
    const p8 = mulWire(shifted(p5, 7, f), shifted(q3, 8, f));
    return shifted(mulWire(shifted(p8, 9, f), shifted(q3, 10, f)), 11, f);
  }

  const p3b = mulWire(shifted(x, 3, f), shifted(q2, 4, f));
  const p2 = addWire(p3b, p3, -1, 2);             // Pan: p2 = p3* - p3
  const { k, ell, m, rBar, qBar } = spec;
  const pLow = nested(p3, p2, ell - 1, 5, f);
  const q3 = qBar ? p3b : p3;
  const r3 = rBar ? p3b : p3;
  const qLow = nested(q3, p2, k - m - ell - 2, 2 * ell + 3, f);
  const pEven = mulWire(
    shifted(pLow, 2 * k - 2 * m - 1, f),
    shifted(qLow, 2 * k - 2 * m, f),
  );
  const rOdd = nested(r3, q2, m - 1, 2 * k - 2 * m + 1, f);
  return shifted(mulWire(shifted(pEven, n - 2, f), shifted(rOdd, n - 1, f)), n, f);
}

const abs2 = (r, i) => r * r + i * i;

function residualNorm(vr, vi, target) {
  let out = 0;
  for (let i = 0; i < vr.length; i++)
    out = Math.max(out, Math.hypot(vr[i] - target[i].re, vi[i] - target[i].im) / (1 + cAbs(target[i])));
  return out;
}

// Partial-pivoted complex Gaussian elimination.  Each row is scaled before
// entry, so the pivot threshold is relative to the largest matrix entry.
function solveComplex(jr0, ji0, br0, bi0, D, rowWeights = null) {
  const ar = jr0.slice(), ai = ji0.slice(), br = br0.slice(), bi = bi0.slice();
  const columnScale = new Float64Array(D);
  for (let r = 0; r < D; r++) {
    const s = rowWeights ? rowWeights[r] : 1;
    br[r] *= s; bi[r] *= s;
    for (let c = 0; c < D; c++) {
      const z = r * D + c;
      ar[z] *= s; ai[z] *= s;
      columnScale[c] = Math.max(columnScale[c], Math.hypot(ar[z], ai[z]));
    }
  }
  for (let c = 0; c < D; c++) {
    const s = columnScale[c];
    if (!(s > 0) || !Number.isFinite(s)) return null;
    for (let r = 0; r < D; r++) {
      const z = r * D + c;
      ar[z] /= s; ai[z] /= s;
    }
  }
  const matrixMax = 1;

  for (let k = 0; k < D; k++) {
    let piv = k, best = abs2(ar[k * D + k], ai[k * D + k]);
    for (let r = k + 1; r < D; r++) {
      const q = abs2(ar[r * D + k], ai[r * D + k]);
      if (q > best) { best = q; piv = r; }
    }
    if (!(Math.sqrt(best) > 5e-16 * matrixMax)) return null;
    if (piv !== k) {
      for (let c = k; c < D; c++) {
        const a = k * D + c, b = piv * D + c;
        [ar[a], ar[b]] = [ar[b], ar[a]]; [ai[a], ai[b]] = [ai[b], ai[a]];
      }
      [br[k], br[piv]] = [br[piv], br[k]]; [bi[k], bi[piv]] = [bi[piv], bi[k]];
    }
    const pk = k * D + k, pr = ar[pk], pi = ai[pk], pd = abs2(pr, pi);
    for (let r = k + 1; r < D; r++) {
      const rk = r * D + k, xr = ar[rk], xi = ai[rk];
      const fr = (xr * pr + xi * pi) / pd, fi = (xi * pr - xr * pi) / pd;
      ar[rk] = 0; ai[rk] = 0;
      for (let c = k + 1; c < D; c++) {
        const rc = r * D + c, kc = k * D + c, kr = ar[kc], ki = ai[kc];
        ar[rc] -= fr * kr - fi * ki;
        ai[rc] -= fr * ki + fi * kr;
      }
      const bkr = br[k], bki = bi[k];
      br[r] -= fr * bkr - fi * bki;
      bi[r] -= fr * bki + fi * bkr;
    }
  }

  const xr = new Float64Array(D), xi = new Float64Array(D);
  for (let r = D - 1; r >= 0; r--) {
    let sr = br[r], si = bi[r];
    for (let c = r + 1; c < D; c++) {
      const z = r * D + c;
      sr -= ar[z] * xr[c] - ai[z] * xi[c];
      si -= ar[z] * xi[c] + ai[z] * xr[c];
    }
    const z = r * D + r, d = abs2(ar[z], ai[z]);
    xr[r] = (sr * ar[z] + si * ai[z]) / d;
    xi[r] = (si * ar[z] - sr * ai[z]) / d;
    if (!Number.isFinite(xr[r]) || !Number.isFinite(xi[r])) return null;
  }
  for (let c = 0; c < D; c++) { xr[c] /= columnScale[c]; xi[c] /= columnScale[c]; }
  return { r: xr, i: xi };
}

function rngFor(seed0) {
  let seed = seed0 >>> 0;
  return () => {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed / 4294967296;
  };
}

const cloneParams = f => f.map(z => C(z.re, z.im));
const maxParam = f => Math.max(0, ...f.map(cAbs));

function principalRoot(z, degree) {
  const radius = Math.pow(cAbs(z), 1 / degree);
  const angle = Math.atan2(z.im, z.re) / degree;
  return C(radius * Math.cos(angle), radius * Math.sin(angle));
}

// The top coefficient is an explicit pivot, not something continuation needs
// to discover.  In (3) it is (f3-f1)^(k-m-3); in (4) it is (f6-f4)^2.
// Fixing that difference to a root of the requested leading coefficient also
// keeps the continuation away from the obviously singular zero-pivot slice.
function seedLeadingPivot(f, target, spec) {
  const degree = spec.n === 11 ? 2 : spec.k - spec.m - 3;
  const delta = principalRoot(target[spec.n], degree);
  const lo = spec.n === 11 ? 4 : 1, hi = spec.n === 11 ? 6 : 3;
  const mid = C(0.5 * (f[lo].re + f[hi].re), 0.5 * (f[lo].im + f[hi].im));
  f[lo] = C(mid.re - 0.5 * delta.re, mid.im - 0.5 * delta.im);
  f[hi] = C(mid.re + 0.5 * delta.re, mid.im + 0.5 * delta.im);
}

function pathAt(t, start, target, wiggle) {
  const s = 4 * t * (1 - t), out = new Array(target.length);
  for (let i = 0; i < out.length; i++) out[i] = C(
    (1 - t) * start[i].re + t * target[i].re + s * wiggle[i].re,
    (1 - t) * start[i].im + t * target[i].im + s * wiggle[i].im,
  );
  return out;
}

function pathDerivative(t, start, target, wiggle) {
  const s = 4 * (1 - 2 * t), out = new Array(target.length);
  for (let i = 0; i < out.length; i++) out[i] = C(
    target[i].re - start[i].re + s * wiggle[i].re,
    target[i].im - start[i].im + s * wiggle[i].im,
  );
  return out;
}

function mapValues(f, spec) {
  const w = coefficientMap(f, spec);
  return Array.from(w.vr, (re, i) => C(re, w.vi[i]));
}

function correct(pred, wanted, spec) {
  let f = cloneParams(pred);
  for (let it = 0; it < 12; it++) {
    const w = coefficientMap(f, spec), err = residualNorm(w.vr, w.vi, wanted);
    if (err <= 2e-11) return f;
    const D = f.length, br = new Float64Array(D), bi = new Float64Array(D), weights = new Float64Array(D);
    for (let i = 0; i < D; i++) {
      br[i] = wanted[i].re - w.vr[i]; bi[i] = wanted[i].im - w.vi[i];
      weights[i] = 1 / (1 + cAbs(wanted[i]));
    }
    const delta = solveComplex(w.jr, w.ji, br, bi, D, weights);
    if (!delta) return null;
    let dn = 0;
    for (let i = 0; i < D; i++) dn = Math.max(dn, Math.hypot(delta.r[i], delta.i[i]));
    const cap = 2 * (1 + maxParam(f));
    const baseScale = dn > cap ? cap / dn : 1;
    let accepted = null, best = err;
    for (const shrink of [1, 0.5, 0.25, 0.125]) {
      const a = baseScale * shrink;
      const cand = f.map((z, i) => C(z.re + a * delta.r[i], z.im + a * delta.i[i]));
      if (maxParam(cand) > 1e8) continue;
      const cv = coefficientMap(cand, spec);
      const ce = residualNorm(cv.vr, cv.vi, wanted);
      if (ce < best) { accepted = cand; best = ce; break; }
    }
    if (!accepted) return null;
    f = accepted;
  }
  const w = coefficientMap(f, spec);
  return residualNorm(w.vr, w.vi, wanted) <= 2e-9 ? f : null;
}

// Track one nonsingular branch from a known parameter vector to the target.
function track(target, spec, seed) {
  const D = target.length, rnd = rngFor(seed);
  let f = Array.from({ length: D }, () => C(1.2 * (rnd() - 0.5), 1.2 * (rnd() - 0.5)));
  seedLeadingPivot(f, target, spec);
  const start = mapValues(f, spec);
  const wiggle = target.map((z, i) => {
    if (i === spec.n) return C(0);
    const scale = 0.04 * (1 + cAbs(z) + cAbs(start[i]));
    return C(scale * (rnd() - 0.5), scale * (rnd() - 0.5));
  });
  let t = 0, h = 0.04, steps = 0;
  while (t < 1 - 1e-14 && steps < 600) {
    const step = Math.min(h, 1 - t), w = coefficientMap(f, spec);
    const deriv = pathDerivative(t, start, target, wiggle);
    const br = new Float64Array(D), bi = new Float64Array(D), weights = new Float64Array(D);
    const here = pathAt(t, start, target, wiggle);
    for (let i = 0; i < D; i++) {
      br[i] = deriv[i].re; bi[i] = deriv[i].im; weights[i] = 1 / (1 + cAbs(here[i]));
    }
    const tangent = solveComplex(w.jr, w.ji, br, bi, D, weights);
    if (!tangent) { h *= 0.5; if (h < 2e-6) return null; continue; }
    let move = 0;
    for (let i = 0; i < D; i++) move = Math.max(move, step * Math.hypot(tangent.r[i], tangent.i[i]));
    if (move > 1.5 * (1 + maxParam(f))) { h *= 0.5; if (h < 2e-6) return null; continue; }
    const pred = f.map((z, i) => C(z.re + step * tangent.r[i], z.im + step * tangent.i[i]));
    const next = correct(pred, pathAt(t + step, start, target, wiggle), spec);
    if (!next) { h *= 0.5; if (h < 2e-6) return null; continue; }
    f = next; t += step; steps++;
    h = Math.min(0.12, h * 1.35);
  }
  if (t < 1 - 1e-12) return null;
  f = correct(f, target, spec);
  if (!f || maxParam(f) > 1e7) return null;
  const w = coefficientMap(f, spec);
  return residualNorm(w.vr, w.vi, target) <= 2e-8 ? f : null;
}

function variants(n) {
  if (n === 11) return [{ n, kind: 'scheme (4)' }];
  const k = (n - 1) / 2, out = [];
  for (let m = 2; m <= k - 4; m++) {
    for (let ell = 1; ell <= Math.floor((k - m) / 2); ell++) {
      for (const rBar of [false, true]) for (const qBar of [false, true])
        out.push({ n, k, ell, m, rBar, qBar, kind: 'scheme (3)' });
    }
  }
  // Pan explicitly recommends choosing among variants for accuracy.  A small
  // top pivot exponent k-m-3 is markedly better conditioned, then prefer
  // balanced outer factors and the unbarred version printed in the paper.
  out.sort((a, b) => {
    const ba = Math.abs((2 * a.k - 2 * a.m) - (2 * a.m + 1));
    const bb = Math.abs((2 * b.k - 2 * b.m) - (2 * b.m + 1));
    return (a.k - a.m - 3) - (b.k - b.m - 3) || ba - bb || a.ell - b.ell ||
      Number(a.rBar) - Number(b.rBar) || Number(a.qBar) - Number(b.qBar);
  });
  return out;
}

function emit(params, spec, digits) {
  const n = spec.n, lines = [], depth = { x: 0 };
  let mults = 0, adds = 0, serial = 0;
  const push = (lhs, rhs, mul, deps) => {
    lines.push({ lhs, rhs, mul });
    depth[lhs] = Math.max(0, ...deps.map(d => depth[d] ?? 0)) + (mul ? 1 : 0);
    if (mul) mults++;
  };
  const shiftedName = (name, i) => {
    const out = appendConst(name, params[i], digits);
    if (out !== name) adds++;
    return out;
  };
  const product = (lhs, left, li, right, ri) => {
    push(lhs, `(${shiftedName(left, li)}) * (${shiftedName(right, ri)})`, true, [left, right]);
    return lhs;
  };
  const nest = (start, quadratic, count, first, prefix) => {
    let acc = start;
    for (let j = 0; j < count; j++) acc = product(`${prefix}${++serial}`, acc, first + 2 * j, quadratic, first + 2 * j + 1);
    return acc;
  };

  const u = shiftedName('x', 0);
  push('u0', u, false, ['x']);
  push('q2', 'u0 * u0', true, ['u0']);
  product('p3', 'x', 1, 'q2', 2);

  if (n === 11) {
    product('p5', 'p3', 3, 'q2', 4);
    product('p5b', 'p3', 5, 'q2', 6);
    push('q3', 'p5b - p5', false, ['p5b', 'p5']); adds++;
    product('p8', 'p5', 7, 'q3', 8);
    const left = shiftedName('p8', 9), right = shiftedName('q3', 10);
    let rhs = `(${left}) * (${right})`;
    const withC = appendConst(rhs, params[11], digits); if (withC !== rhs) adds++;
    push('P', withC, true, ['p8', 'q3']);
    return { lines, mults, adds, height: depth.P };
  }

  product('p3b', 'x', 3, 'q2', 4);
  push('p2', 'p3b - p3', false, ['p3b', 'p3']); adds++;
  const { k, ell, m, rBar, qBar } = spec;
  const pLow = nest('p3', 'p2', ell - 1, 5, 'a');
  const qLow = nest(qBar ? 'p3b' : 'p3', 'p2', k - m - ell - 2, 2 * ell + 3, 'b');
  const pEven = product('pe', pLow, 2 * k - 2 * m - 1, qLow, 2 * k - 2 * m);
  const rOdd = nest(rBar ? 'p3b' : 'p3', 'q2', m - 1, 2 * k - 2 * m + 1, 'r');
  const left = shiftedName(pEven, n - 2), right = shiftedName(rOdd, n - 1);
  let rhs = `(${left}) * (${right})`;
  const withC = appendConst(rhs, params[n], digits); if (withC !== rhs) adds++;
  push('P', withC, true, [pEven, rOdd]);
  return { lines, mults, adds, height: depth.P };
}

function isComplex(params) {
  const scale = 1 + Math.max(0, ...params.map(z => Math.abs(z.re)));
  return params.some(z => Math.abs(z.im) > 2e-10 * scale);
}

// Scheme (4) in degree 11 and family (3) in odd degree >= 13, on validated
// complex coefficients (constant term first).
function compileOddScheme(target) {
  const n = target.length - 1;
  if (isZeroC(target[n])) throw new Error('Pan 1978: the leading coefficient must be nonzero');
  const complexInput = target.some(z => z.im !== 0);
  const p = target.map(z => z.re);
  const verify = complexInput ? lines => verifyLinesComplex(lines, target) : lines => verifyLines(lines, p);

  let best = null, attempts = 0;
  const maxAttempts = 64;
  for (const spec of variants(n)) {
    const seedsForVariant = n === 11 ? maxAttempts : 4;
    for (let seedIndex = 0; seedIndex < seedsForVariant; seedIndex++) {
      if (attempts++ >= maxAttempts) break;
      const seed = (0x9e3779b9 ^ (n * 65537) ^ (spec.ell ?? 0) * 8191 ^ (spec.m ?? 0) * 131 ^
                    Number(spec.rBar) * 17 ^ Number(spec.qBar) * 31 ^ seedIndex * 104729) >>> 0;
      const params = track(target, spec, seed);
      if (!params) continue;
      for (const digits of [13, 17]) {
        const chain = emit(params, spec, digits), err = verify(chain.lines);
        if (!best || err < best.err) best = { params, spec, chain, err };
        if (err <= 1e-8) break;
      }
      if (best && best.err <= 1e-8) break;
    }
    if (best && best.err <= 1e-8) break;
    if (attempts >= maxAttempts) break;
  }
  if (!best || !(best.err <= 1e-3)) {
    const coverage = n === 11
      ? `Pan proves scheme (4) represents every degree-11 complex polynomial, but the numerical path can still become singular`
      : `Scheme (3) is guaranteed only for almost every polynomial`;
    throw new Error(
      `Pan 1978: numerical continuation did not find a verified ${((n + 1) / 2)}-multiplication ` +
      `parameterization. ${coverage}; a numerical failure does not by itself prove non-representability.`,
    );
  }

  const complex = complexInput || isComplex(best.params), spec = best.spec;
  const variant = n === 11 ? 'scheme (4)' :
    `scheme (3), ell=${spec.ell}, m=${spec.m}, r3=${spec.rBar ? 'p3*' : 'p3'}, q3=${spec.qBar ? 'p3*' : 'p3'}`;
  const scope = n === 11 ? 'Pan proves this degree-11 scheme works for every complex polynomial' :
    'Pan proves the displayed low-addition family works for almost every complex polynomial';
  return {
    name: 'Pan 1978 odd scheme',
    lines: best.chain.lines, mults: best.chain.mults, adds: best.chain.adds, height: best.chain.height,
    preprocessing: complex ? 'complex' : 'real', exact: false, maxRelError: best.err,
    preprocessingLabel: complex ? 'complex algebraic system (numeric)' : 'real algebraic system (numeric)',
    note: `Pan 1978 ${variant}: ${(n + 1) / 2} multiplications for the original, possibly non-monic ` +
      `degree-${n} polynomial${complexInput ? ' with complex coefficients' : ''}; ${scope}. Parameters were ` +
      `obtained here by deterministic numerical homotopy on Pan's explicit coefficient map and the printed ` +
      `chain was independently verified${complexInput ? ' at real and non-real sample points' : ''}.`,
  };
}

// Even degree n >= 12: P(x) = x·Q(x) + a_0 with Q the odd degree-(n-1)
// polynomial a_1 + a_2 x + ... + a_n x^(n-1) compiled by the odd scheme, for
// one more multiplication (n/2 + 1 in all) and one more addition unless
// a_0 = 0.  The printed chain is verified again as a whole.
function compileEvenLift(target) {
  const n = target.length - 1;
  const lower = compileOddScheme(target.slice(1));
  const lines = lower.lines.map(line => ({ ...line }));
  lines[lines.length - 1].lhs = 'Q';
  const product = 'x * Q', rhs = appendConst(product, target[0], 17);
  lines.push({ lhs: 'P', rhs, mul: true });
  const complexInput = target.some(z => z.im !== 0);
  const err = complexInput ? verifyLinesComplex(lines, target) : verifyLines(lines, target.map(z => z.re));
  if (!(err <= 1e-3))
    throw new Error(`Pan 1978: the degree-${n} even lift failed printed-chain verification (${err})`);
  const complex = lower.preprocessing === 'complex' || target[0].im !== 0;
  return {
    ...lower, name: 'Pan 1978 even-degree lift', lines,
    mults: lower.mults + 1, adds: lower.adds + (rhs === product ? 0 : 1),
    height: lower.height + 1, maxRelError: err,
    preprocessing: complex ? 'complex' : 'real',
    preprocessingLabel: complex ? 'complex algebraic system (numeric)' : 'real algebraic system (numeric)',
    note: `Pan even-degree reduction P(x) = x·Q_${n - 1}(x) + a_0, followed by ` + lower.note,
  };
}

const LOW_DEGREE_MESSAGE =
  "Pan 1978's complex schemes start at degree 11 (scheme (4); family (3) from 13); " +
  'Knuth–Eve and Belaga give ⌊n/2⌋+1 multiplications for a monic polynomial here.';

/** Pan's complex compiler: scheme (4) at degree 11, family (3) in every odd
 * degree >= 13, and the one-product lift P = x·Q + a_0 in even degree >= 12.
 * Coefficients ascend (constant term first), plain numbers or {re, im}. */
export function compilePan1978(coeffs) {
  if (!Array.isArray(coeffs)) throw new Error('Pan 1978: need a coefficient array');
  const n = coeffs.length - 1;
  if (n < 11) throw new Error(LOW_DEGREE_MESSAGE);
  const target = coeffs.map(toComplex);
  if (!target.every(z => Number.isFinite(z.re) && Number.isFinite(z.im)))
    throw new Error('Pan 1978: coefficients must be finite numbers');
  return n % 2 === 0 ? compileEvenLift(target) : compileOddScheme(target);
}
