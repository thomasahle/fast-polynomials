// Pan's multiplication-optimal real-field scheme.
//
//   V. Ya. Pan, "Computational complexity of computing polynomials over the
//   fields of real and complex numbers", STOC 1978, Theorem 10 / scheme (9).
//
// For every real polynomial of odd degree n = 2k+1 >= 9, Pan proves that one
// of four sign choices has a representation
//
//   q2  = (x+f0)^2
//   p2  = q2 + gamma*x                         gamma in {+1,-1}
//   q4  = (p2+f1)(q2+f2)
//   p5  = (q4+f3)(x+f4)
//   p5* = (q4+f5)(x+f6)
//   p4  = p5* - p5 + delta*2^N*q2             delta in {+1,-1}
//   p9  = (p5+f7)(p4+f8)
//   qn  = (p9,q2,k-4,9)
//   P   = qn+fn,
//
// using (n+1)/2 multiplications, n+4 additions/subtractions, and one radix
// shift.  Multiplication by 2^N is the separately counted radix shift, not M.
//
// Pan does not print a coefficient decoder.  This comparison implementation
// uses explicit top-window divisions, Eve's monic quadratic peels, affine
// pivots for the degree-9 core, and a small deterministic Newton block for the
// remaining coupled equations.  It tries the four signs and nonnegative N,
// and independently reparses and verifies the emitted chain at 69 points.
// Numerical failure is reported rather than confused with a theorem failure.

import {
  C, appendConst, verifyLines, eveOddDecompositionCandidates,
} from './motzkin.js';

function zeroWire(deg, D) {
  return { v: new Float64Array(deg + 1), j: new Float64Array((deg + 1) * D), D };
}

function xWire(D) {
  const w = zeroWire(1, D);
  w.v[1] = 1;
  return w;
}

function shifted(a, param, f) {
  const w = { v: a.v.slice(), j: a.j.slice(), D: a.D };
  w.v[0] += f[param];
  w.j[param] += 1;
  return w;
}

function addWire(a, b, scale = 1, maxDegree = Infinity) {
  const D = a.D, size = Math.min(Math.max(a.v.length, b.v.length), maxDegree + 1);
  const w = zeroWire(size - 1, D);
  for (let i = 0; i < size; i++) {
    const wo = i * D;
    if (i < a.v.length) {
      w.v[i] += a.v[i];
      const ao = i * D;
      for (let p = 0; p < D; p++) w.j[wo + p] += a.j[ao + p];
    }
    if (i < b.v.length) {
      w.v[i] += scale * b.v[i];
      const bo = i * D;
      for (let p = 0; p < D; p++) w.j[wo + p] += scale * b.j[bo + p];
    }
  }
  return w;
}

function mulWire(a, b) {
  const D = a.D, w = zeroWire(a.v.length + b.v.length - 2, D);
  for (let i = 0; i < a.v.length; i++) {
    const ao = i * D;
    for (let j = 0; j < b.v.length; j++) {
      const bo = j * D, k = i + j, ko = k * D;
      w.v[k] += a.v[i] * b.v[j];
      for (let p = 0; p < D; p++)
        w.j[ko + p] += a.j[ao + p] * b.v[j] + a.v[i] * b.j[bo + p];
    }
  }
  return w;
}

function nested(start, q2, count, firstParam, f) {
  let acc = start;
  for (let i = 0; i < count; i++)
    acc = mulWire(shifted(acc, firstParam + 2 * i, f), shifted(q2, firstParam + 2 * i + 1, f));
  return acc;
}

function coefficientMap(f, spec) {
  const { n, gamma, delta, N } = spec, D = n + 1, x = xWire(D);
  const q2 = mulWire(shifted(x, 0, f), shifted(x, 0, f));
  const p2 = addWire(q2, x, gamma);
  const q4 = mulWire(shifted(p2, 1, f), shifted(q2, 2, f));
  const p5 = mulWire(shifted(q4, 3, f), shifted(x, 4, f));
  const p5b = mulWire(shifted(q4, 5, f), shifted(x, 6, f));
  let p4 = addWire(p5b, p5, -1, 4);
  p4 = addWire(p4, q2, delta * Math.pow(2, N), 4);
  const p9 = mulWire(shifted(p5, 7, f), shifted(p4, 8, f));
  return shifted(nested(p9, q2, (n - 9) / 2, 9, f), n, f);
}

// Pan's separate real degree-8 scheme (6), Theorem 8.  It represents every
// monic real octic for one of epsilon=+1,-1:
//   q2=(x+f0)^2,
//   p3=(x+f1)(q2+f2),
//   p6=(p3+f3)(p3+epsilon*q2+f4),
//   P8=(p6+f5)(q2+f6)+f7.
function coefficientMap8(f, epsilon) {
  const D = 8, x = xWire(D);
  const q2 = mulWire(shifted(x, 0, f), shifted(x, 0, f));
  const p3 = mulWire(shifted(x, 1, f), shifted(q2, 2, f));
  const r3 = shifted(addWire(p3, q2, epsilon), 4, f);
  const p6 = mulWire(shifted(p3, 3, f), r3);
  const p8 = mulWire(shifted(p6, 5, f), shifted(q2, 6, f));
  return shifted(p8, 7, f);
}

function residualNorm(w, target) {
  let e = 0;
  for (let i = 0; i < target.length; i++) e = Math.max(e, Math.abs(w.v[i] - target[i]) / (1 + Math.abs(target[i])));
  return e;
}

// Row- and column-scaled Gaussian elimination with partial pivoting.
function solveLinear(j0, b0, D, rowWeights) {
  const a = j0.slice(), b = b0.slice(), col = new Float64Array(D);
  for (let r = 0; r < D; r++) {
    const s = rowWeights?.[r] ?? 1;
    b[r] *= s;
    for (let c = 0; c < D; c++) {
      const z = r * D + c;
      a[z] *= s;
      col[c] = Math.max(col[c], Math.abs(a[z]));
    }
  }
  for (let c = 0; c < D; c++) {
    if (!(col[c] > 0) || !Number.isFinite(col[c])) return null;
    for (let r = 0; r < D; r++) a[r * D + c] /= col[c];
  }
  for (let k = 0; k < D; k++) {
    let pivot = k, best = Math.abs(a[k * D + k]);
    for (let r = k + 1; r < D; r++) {
      const q = Math.abs(a[r * D + k]);
      if (q > best) { best = q; pivot = r; }
    }
    if (!(best > 5e-15)) return null;
    if (pivot !== k) {
      for (let c = k; c < D; c++) [a[k * D + c], a[pivot * D + c]] = [a[pivot * D + c], a[k * D + c]];
      [b[k], b[pivot]] = [b[pivot], b[k]];
    }
    const pk = a[k * D + k];
    for (let r = k + 1; r < D; r++) {
      const q = a[r * D + k] / pk;
      a[r * D + k] = 0;
      for (let c = k + 1; c < D; c++) a[r * D + c] -= q * a[k * D + c];
      b[r] -= q * b[k];
    }
  }
  const x = new Float64Array(D);
  for (let r = D - 1; r >= 0; r--) {
    let s = b[r];
    for (let c = r + 1; c < D; c++) s -= a[r * D + c] * x[c];
    x[r] = s / a[r * D + r];
    if (!Number.isFinite(x[r])) return null;
  }
  for (let c = 0; c < D; c++) x[c] /= col[c];
  return x;
}

function rngFor(seed0) {
  let seed = seed0 >>> 0;
  return () => {
    seed = (Math.imul(seed, 1664525) + 1013904223) >>> 0;
    return seed / 4294967296;
  };
}

const maxParam = f => Math.max(0, ...f.map(Math.abs));

function correct8(pred, wanted, epsilon) {
  const D = 8;
  let f = pred.slice();
  for (let it = 0; it < 16; it++) {
    const w = coefficientMap8(f, epsilon);
    const residual = Float64Array.from(wanted, (v, i) => v - w.v[i]);
    const err = Math.max(...residual.map((v, i) => Math.abs(v) / (1 + Math.abs(wanted[i]))));
    if (err <= 2e-11) return f;
    const weights = Float64Array.from(wanted, v => 1 / (1 + Math.abs(v)));
    const step = solveLinear(w.j.slice(0, D * D), residual, D, weights);
    if (!step) return null;
    const dn = Math.max(...step.map(Math.abs)), cap = 3 * (1 + maxParam(f));
    const base = dn > cap ? cap / dn : 1;
    let accepted = null, best = err;
    for (const shrink of [1, 0.5, 0.25, 0.125, 0.0625]) {
      const cand = f.map((v, i) => v + base * shrink * step[i]);
      if (maxParam(cand) > 1e12) continue;
      const cw = coefficientMap8(cand, epsilon);
      const ce = residualNorm(cw, wanted);
      if (ce < best) { accepted = cand; best = ce; break; }
    }
    if (!accepted) return null;
    f = accepted;
  }
  return residualNorm(coefficientMap8(f, epsilon), wanted) <= 2e-8 ? f : null;
}

// Predictor/corrector on the explicit eight coefficient equations.  The
// square solve is the displayed finite coefficient block, not an existence
// argument: every emitted result is independently checked afterward.
function track8(wanted, epsilon, seed) {
  const D = 8, rnd = rngFor(seed);
  let f = Array.from({ length: D }, () => 1.2 * (rnd() - 0.5));
  const start = Array.from(coefficientMap8(f, epsilon).v.slice(0, D));
  const wiggle = wanted.map((v, i) => 0.04 * (1 + Math.abs(v) + Math.abs(start[i])) * (rnd() - 0.5));
  const path = t => wanted.map((v, i) => (1 - t) * start[i] + t * v + 4 * t * (1 - t) * wiggle[i]);
  const derivative = t => wanted.map((v, i) => v - start[i] + 4 * (1 - 2 * t) * wiggle[i]);
  let t = 0, h = 0.04, steps = 0;
  while (t < 1 - 1e-14 && steps < 700) {
    const dt = Math.min(h, 1 - t), w = coefficientMap8(f, epsilon), here = path(t);
    const tangent = solveLinear(w.j.slice(0, D * D), Float64Array.from(derivative(t)), D,
      Float64Array.from(here, v => 1 / (1 + Math.abs(v))));
    if (!tangent) { h *= 0.5; if (h < 2e-6) return null; continue; }
    const move = dt * Math.max(...tangent.map(Math.abs));
    if (move > 2 * (1 + maxParam(f))) { h *= 0.5; if (h < 2e-6) return null; continue; }
    const pred = f.map((v, i) => v + dt * tangent[i]);
    const next = correct8(pred, path(t + dt), epsilon);
    if (!next) { h *= 0.5; if (h < 2e-6) return null; continue; }
    f = next; t += dt; steps++; h = Math.min(0.12, 1.35 * h);
  }
  if (t < 1 - 1e-12) return null;
  return correct8(f, wanted, epsilon);
}

function divideByQ2Node(p, f0, node) {
  const divisor = [f0 * f0 - node, 2 * f0, 1], rem = p.slice();
  const q = new Array(p.length - 2).fill(0);
  for (let i = p.length - 1; i >= 2; i--) {
    const c = rem[i]; q[i - 2] = c;
    rem[i] = 0; rem[i - 1] -= c * divisor[1]; rem[i - 2] -= c * divisor[0];
  }
  return { quotient: q, constant: rem[0], linear: rem[1] };
}

function combinations(values, count, limit = 500) {
  const out = [], chosen = [];
  const go = start => {
    if (out.length >= limit) return;
    if (chosen.length === count) { out.push(chosen.slice()); return; }
    for (let i = start; i <= values.length - (count - chosen.length); i++) {
      chosen.push(values[i]); go(i + 1); chosen.pop();
      if (out.length >= limit) return;
    }
  };
  go(0);
  return out;
}

// Descend from P_n to P_9 by the literal Eve factor pivots.  Each selected
// root s gives P=(Q)(q2-s)+c; the vanishing linear remainder is checked.
function reduceToBase9(p, f0, selected, loose = false) {
  let cur = p.slice();
  const outer = [], linearResiduals = [];
  for (let j = selected.length - 1; j >= 0; j--) {
    const d = divideByQ2Node(cur, f0, selected[j]);
    let scale = 1;
    for (const v of cur) scale = Math.max(scale, Math.abs(v));
    linearResiduals.push(d.linear / scale);
    if (!loose && Math.abs(d.linear) > 2e-6 * scale) return null;
    outer.push({ index: cur.length - 1, factor: -selected[j], constant: d.constant });
    cur = d.quotient;
  }
  return cur.length === 10 ? { base: cur, outer, linearResiduals } : null;
}

// Explicit decoder for all but three rows of the degree-9 core.  With
// s=[x^3]q4 and L=[x^9]P, the x^8 and x^7 rows divide out f4 and f1+f2.
// Then x^6, x^5, x^4, and x^0 successively pivot f5-f3, f8, f7, and f9.
// The returned x,x^2,x^3 residuals are the only coupled base equations.
function decodeBaseResidual(base, f0, spec, f1, f3) {
  const conv = (a, b) => {
    const out = new Array(a.length + b.length - 1).fill(0);
    for (let i = 0; i < a.length; i++) for (let j = 0; j < b.length; j++) out[i + j] += a[i] * b[j];
    return out;
  };
  const plus0 = (a, c) => { const out = a.slice(); out[0] += c; return out; };
  const L = base[9], s = 4 * f0 + spec.gamma;
  if (!Number.isFinite(L) || Math.abs(L) < 1e-15) return null;
  const f4 = base[8] / L - 2 * s;
  const q4x2 = (base[7] - spec.delta * Math.pow(2, spec.N)) / (2 * L) -
    0.5 * s * s - f4 * s;
  const f2 = q4x2 - 6 * f0 * f0 - 2 * f0 * spec.gamma - f1;
  const q2 = [f0 * f0, 2 * f0, 1];
  const p2 = q2.slice(); p2[1] += spec.gamma;
  const q4 = conv(plus0(p2, f1), plus0(q2, f2));
  const A = conv(plus0(q4, f3), [f4, 1]);
  const B = q4.map(v => L * v), D = spec.delta * Math.pow(2, spec.N);
  for (let i = 0; i < 3; i++) B[i] += D * q2[i];
  let AB = conv(A, B);
  const h = base[6] - AB[6];
  B[0] += f3 * L + h * (L + f4);
  B[1] += h;
  AB = conv(A, B);
  const f8 = base[5] - AB[5];
  const f7 = (base[4] - AB[4] - f8 * A[4]) / L;
  const out = conv(plus0(A, f7), plus0(B, f8));
  const f9 = base[0] - out[0];
  const f = [f0, f1, f2, f3, f4, f3 + h, f4 + L, f7, f8, f9];
  if (!f.every(Number.isFinite)) return null;
  return { f, residual: [base[1] - out[1], base[2] - out[2], base[3] - out[3]] };
}

// Pan's "third application of Fact 2 plus additional techniques": start at
// an Eve chart, then move the common shift f0 and the selected quadratic
// nodes together.  The equations are completely explicit: one vanishing
// linear remainder for every monic division, followed by the one unused row
// of the 2x2 degree-9 block above.
function solveOuterChart(p, initialShift, initialNodes, spec, seed) {
  const D = initialNodes.length + 3, nodeCount = initialNodes.length;
  const evaluate = z => {
    const reduced = reduceToBase9(p, z[0], z.slice(1, 1 + nodeCount), true);
    if (!reduced) return null;
    const base = decodeBaseResidual(reduced.base, z[0], spec, z[D - 2], z[D - 1]);
    if (!base) return null;
    return {
      residual: reduced.linearResiduals.concat(base.residual.map((v, i) =>
        v / (1 + Math.abs(reduced.base[i + 1])))),
      reduced, base,
    };
  };
  const norm = r => Math.max(...r.map(Math.abs));
  const rnd = rngFor(seed ^ 0xd1b54a35), starts = [[0, 0]];
  for (const radius of [0.3, 1, 3, 10, 30])
    for (let rep = 0; rep < 2; rep++) starts.push([2 * radius * (rnd() - 0.5), 2 * radius * (rnd() - 0.5)]);
  for (const tail of starts) {
    let z = [initialShift, ...initialNodes, ...tail], cur = evaluate(z);
    if (!cur) continue;
    for (let it = 0; it < 55; it++) {
      const err = norm(cur.residual);
      if (err <= 3e-9) break;
      const J = new Float64Array(D * D);
      let finite = true;
      for (let c = 0; c < D; c++) {
        const h = 3e-5 * (1 + Math.abs(z[c])), zp = z.slice(), zm = z.slice();
        zp[c] += h; zm[c] -= h;
        const ep = evaluate(zp), em = evaluate(zm);
        if (!ep || !em) { finite = false; break; }
        for (let r = 0; r < D; r++) J[r * D + c] = (ep.residual[r] - em.residual[r]) / (2 * h);
      }
      if (!finite) break;
      const step = solveLinear(J, Float64Array.from(cur.residual, v => -v), D);
      if (!step) break;
      let accepted = null, best = err;
      for (const shrink of [1, 0.5, 0.25, 0.125, 0.0625, 0.03125]) {
        const cand = z.map((v, i) => v + shrink * step[i]);
        if (maxParam(cand) > 1e13) continue;
        const ev = evaluate(cand);
        if (!ev) continue;
        const e = norm(ev.residual);
        if (e < best) { accepted = { z: cand, ev }; best = e; break; }
      }
      if (!accepted) break;
      z = accepted.z; cur = accepted.ev;
    }
    if (norm(cur.residual) > 2e-7) continue;
    const n = p.length - 1, f = new Array(n + 1).fill(0);
    for (let i = 0; i <= 9; i++) f[i] = cur.base.f[i];
    for (const layer of cur.reduced.outer) {
      f[layer.index - 1] = layer.factor;
      f[layer.index] = layer.constant;
    }
    const full = coefficientMap(f, spec);
    if (residualNorm(full, p) <= 2e-6) return { f, shift: z[0], nodes: z.slice(1, 1 + nodeCount) };
  }
  return null;
}

function emit(f, spec, digits) {
  const { n, gamma, delta, N } = spec, lines = [], depth = { x: 0 };
  let mults = 0, adds = 0, serial = 0;
  const push = (lhs, rhs, mul, deps, extra = {}) => {
    lines.push({ lhs, rhs, mul, ...extra });
    depth[lhs] = Math.max(0, ...deps.map(d => depth[d] ?? 0)) + (mul ? 1 : 0);
    if (mul) mults++;
  };
  const shift = (wire, i) => {
    const out = appendConst(wire, C(f[i]), digits);
    if (out !== wire) adds++;
    return out;
  };
  const product = (lhs, a, ai, b, bi) => {
    push(lhs, `(${shift(a, ai)}) * (${shift(b, bi)})`, true, [a, b]);
    return lhs;
  };
  const u0 = shift('x', 0);
  push('u0', u0, false, ['x']);
  push('q2', 'u0 * u0', true, ['u0']);
  push('p2', gamma > 0 ? 'q2 + x' : 'q2 - x', false, ['q2', 'x']); adds++;
  product('q4', 'p2', 1, 'q2', 2);
  product('p5', 'q4', 3, 'x', 4);
  product('p5b', 'q4', 5, 'x', 6);
  const scale = Math.pow(2, N), signed = delta > 0 ? '+' : '-';
  const radix = N === 0 ? 'q2' : `${scale}·q2`;
  push('p4', `p5b - p5 ${signed} ${radix}`, false, ['p5b', 'p5', 'q2'], { radixShift: N }); adds += 2;
  product('p9', 'p5', 7, 'p4', 8);
  let acc = 'p9';
  for (let i = 0; i < (n - 9) / 2; i++) acc = product(`q${11 + 2 * i}_${++serial}`, acc, 9 + 2 * i, 'q2', 10 + 2 * i);
  const final = appendConst(acc, C(f[n]), digits); if (final !== acc) adds++;
  push('P', final, false, [acc]);
  return { lines, mults, adds, height: depth.P };
}

function emit8(f, epsilon, digits) {
  const lines = [], depth = { x: 0 };
  let mults = 0, adds = 0;
  const shift = (wire, i) => {
    const out = appendConst(wire, C(f[i]), digits);
    if (out !== wire) adds++;
    return out;
  };
  const product = (lhs, left, right, deps) => {
    lines.push({ lhs, rhs: `(${left}) * (${right})`, mul: true });
    depth[lhs] = Math.max(...deps.map(d => depth[d] ?? 0)) + 1;
    mults++;
  };
  const u0 = shift('x', 0);
  lines.push({ lhs: 'u0', rhs: u0, mul: false }); depth.u0 = 0;
  product('q2', 'u0', 'u0', ['u0']);
  product('p3', shift('x', 1), shift('q2', 2), ['x', 'q2']);
  let right = epsilon > 0 ? 'p3 + q2' : 'p3 - q2'; adds++;
  const withF4 = appendConst(right, C(f[4]), digits);
  if (withF4 !== right) adds++;
  product('p6', shift('p3', 3), withF4, ['p3', 'q2']);
  product('p8', shift('p6', 5), shift('q2', 6), ['p6', 'q2']);
  const final = appendConst('p8', C(f[7]), digits);
  if (final !== 'p8') adds++;
  lines.push({ lhs: 'P', rhs: final, mul: false }); depth.P = depth.p8;
  return { lines, mults, adds, height: depth.P };
}

function compilePanEight(p) {
  const lc = p[8], target = p.slice(0, 8).map(v => v / lc);
  let best = null;
  for (const epsilon of [1, -1]) {
    for (let attempt = 0; attempt < 48; attempt++) {
      const seed = (0x27d4eb2d ^ (epsilon + 2) * 65537 ^ attempt * 104729) >>> 0;
      const f = track8(target, epsilon, seed);
      if (!f) continue;
      for (const digits of [13, 17]) {
        const chain = emit8(f, epsilon, digits);
        if (lc !== 1) {
          chain.lines[chain.lines.length - 1].lhs = 'Ptilde';
          chain.lines.push({ lhs: 'P', rhs: `${lc} * Ptilde`, mul: true });
          chain.mults++; chain.height++;
        }
        const err = verifyLines(chain.lines, p);
        if (!best || err < best.err) best = { chain, err, epsilon };
        if (err <= 1e-8) break;
      }
      if (best?.err <= 1e-8) break;
    }
    if (best?.err <= 1e-8) break;
  }
  if (!best || best.err > 1e-3)
    throw new Error('Pan degree 8: numerical continuation on the two explicit scheme-(6) coefficient maps failed; ' +
      'Theorem 8 is exact, so this is a numerical decoder failure');
  return {
    name: 'Pan degree-8 scheme', lines: best.chain.lines,
    mults: best.chain.mults, adds: best.chain.adds, height: best.chain.height,
    preserveChainForm: false,
    preprocessing: 'real', preprocessingLabel: 'real algebraic system (numeric)', exact: false,
    maxRelError: best.err,
    note: `Pan 1978 Theorem 8 / scheme (6), epsilon=${best.epsilon}: every monic real octic uses 4 ` +
      `multiplications and at most 9 additions${lc === 1 ? '' : '; this non-monic input uses the Corollary 1 output scaling, for 5 multiplications total'}. ` +
      `Parameters were recovered from the explicit eight-row coefficient block and the printed chain independently verified.`,
  };
}

// Search budget.  Each cell of the enumeration below (spec × Eve candidate ×
// node subset) is one solveOuterChart: 11 Newton starts of up to 55
// finite-difference iterations, 2–4 ms.  Without limits an input whose best
// chain verifies just above ACCEPT (the e^x Taylor polynomials do, ≈3e-8)
// runs the whole product — 16,800 cells at degree 16, 60,480 at degree 20 —
// almost all of it after the best chain was already found.  So: node subsets
// are ranked by how well the plain Eve peels already fit (a division chain,
// no Newton) and the best-ranked subsets are tried under every spec before
// the next rank; the search stops EXTRA_CELLS after a chain verifies at GOOD
// (the trace on e^x at degree 16: first verified chain at cell 11, the best
// ones near cell 1000); and MAX_CELLS bounds the whole compile, shared by the
// conditioning rescales in round-robin slices so none of them starves.
const ACCEPT = 1e-8;        // stop at once
const GOOD = 1e-6;          // good enough: keep looking a little longer for a better chain
const EXTRA_CELLS = 1200;   // ≈ 3–4 s
const MAX_CELLS = 4000;     // ≈ 10–15 s worst case
const SLICE = 800;          // cells per conditioning rescale per round

function specifications(n, maxN = 32) {
  const Ns = [0, 1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 28, 32];
  for (let N = 36; N < maxN; N += 4) Ns.push(N);
  if (maxN > 32 && !Ns.includes(maxN)) Ns.push(maxN);
  const out = [];
  for (const N of Ns) for (const gamma of [1, -1]) for (const delta of [1, -1]) out.push({ n, N, gamma, delta });
  return out;
}

/** budget: { cells, skip = 0, best = null } — run at most `cells` new cells,
 *  skipping the first `skip` of the (deterministic) enumeration, continuing from
 *  a `best` found earlier; on return / throw it carries `best`, the number of
 *  cells consumed (`used`) and whether the enumeration `finished`. */
function compilePanOddCore(coeffs, budget = { cells: MAX_CELLS }) {
  if (!Array.isArray(coeffs) || coeffs.length < 10)
    throw new Error('Pan real: scheme (9) starts at odd degree 9');
  const p = coeffs.map(Number), n = p.length - 1;
  if (!p.every(Number.isFinite)) throw new Error('Pan real: coefficients must be finite numbers');
  if (n % 2 === 0) throw new Error(`Pan real: scheme (9) is for odd degrees (you entered degree ${n})`);
  if (p[n] === 0) throw new Error('Pan real: the leading coefficient must be nonzero');

  let best = budget.best ?? null, attempts = 0;
  budget.used = 0; budget.finished = false;
  const ratio = Math.max(1, ...p.slice(0, n).map(v => Math.abs(v / p[n])));
  const rootBound = 1 + ratio;
  const maxN = Math.min(1020, Math.max(32,
    Math.ceil(Math.log2(1 + Math.abs(p[n - 1]) + n * rootBound)) + 4));

  const outerCount = (n - 9) / 2;
  const eve = eveOddDecompositionCandidates(p).sort((a, b) =>
    Number(b.tag === 'eve' || b.tag === 'bound') - Number(a.tag === 'eve' || a.tag === 'bound'));
  // node subsets of a candidate, best-fitting first: the max vanishing-remainder
  // residual of the plain Eve peels does not depend on the spec, so rank once
  const ranked = new Map();
  const subsetsOf = candidate => {
    if (!ranked.has(candidate)) {
      const score = sel => {
        const r = reduceToBase9(p, candidate.shift, sel, true);
        return r ? Math.max(0, ...r.linearResiduals.map(Math.abs)) : Infinity;
      };
      ranked.set(candidate, combinations(candidate.nodes, outerCount)
        .map(sel => [score(sel), sel]).sort((a, b) => a[0] - b[0]).map(x => x[1]));
    }
    return ranked.get(candidate);
  };
  let sinceGood = 0, index = 0, exhausted = false;
  const specs = specifications(n, maxN);
  const ranks = Math.max(0, ...eve.map(c => subsetsOf(c).length));
  search:
  for (let rank = 0; rank < ranks; rank++) {
    for (const candidate of eve) {
      const selected = subsetsOf(candidate)[rank];
      if (!selected) continue;
      for (const spec of specs) {
        if (index++ < (budget.skip ?? 0)) continue;              // done in an earlier slice
        if (budget.cells <= 0) { exhausted = true; break search; }
        if (best && best.err <= GOOD && ++sinceGood > EXTRA_CELLS) break search;
        budget.cells--; budget.used++;
        const seed = (0x85ebca6b ^ n * 65537 ^ spec.N * 8191 ^ (spec.gamma + 2) * 131 ^
                      (spec.delta + 2) * 17 ^ index * 104729) >>> 0;
        const solved = solveOuterChart(p, candidate.shift, selected, spec, seed); attempts++;
        if (!solved) continue;
        const f = solved.f;
        for (const digits of [13, 17]) {
          const chain = emit(f, spec, digits), err = verifyLines(chain.lines, p);
          if (!best || err < best.err) best = {
            spec, chain, err, shift: solved.shift, selected: solved.nodes,
          };
          if (err <= ACCEPT) break;
        }
        if (best?.err <= ACCEPT) break search;
      }
    }
  }
  budget.best = best; budget.finished = !exhausted;
  if (!best || best.err > 1e-3)
    throw new Error(`Pan real: Eve's explicit outer decomposition and ${attempts} degree-9 sign/radix branches did not find a verified ` +
      `${(n + 1) / 2}-multiplication real parameterization${exhausted ? ' within the search budget' : ''}. ` +
      `Pan's theorem is exact; this reports a numerical coupled-solver failure.`);

  const { spec, chain } = best;
  return {
    name: 'Pan 1978 real scheme', lines: chain.lines, mults: chain.mults, adds: chain.adds, height: chain.height,
    radixShifts: spec.N === 0 ? 0 : 1, radixExponent: spec.N,
    preprocessing: 'real', preprocessingLabel: 'real algebraic system (numeric)', exact: false,
    maxRelError: best.err,
    note: `Pan 1978 Theorem 10 / scheme (9): ${(n + 1) / 2} multiplications, ${n + 4} additions, ` +
      `${spec.N === 0 ? 'a trivial radix shift (N=0)' : `one radix shift by 2^${spec.N}`}; ` +
      `gamma=${spec.gamma}, delta=${spec.delta}. The outer factors were recovered by Eve's explicit real-root peels ` +
      `and Pan's coupled compatibility step (shift f0=${best.shift}); the finite residual block was solved numerically ` +
      `and the printed chain independently verified.`,
  };
}

function withInputRadixScale(r, p, exponent) {
  if (exponent === 0) return r;
  const scale = Math.pow(2, exponent);
  const lines = [
    { lhs: 'z', rhs: `${scale}·x`, mul: false, radixShift: exponent },
    ...r.lines.map(line => ({ ...line, rhs: line.rhs.replace(/\bx\b/g, 'z') })),
  ];
  const err = verifyLines(lines, p);
  if (!(err <= 1e-3)) return null;
  return {
    ...r, lines, maxRelError: err, preserveChainForm: false,
    radixShifts: (r.radixShifts ?? 0) + 1,
    inputRadixExponent: exponent,
    radixAdditionCost: (r.radixExponent ?? 0) + Math.max(0, exponent),
    note: `For numerical conditioning the explicit decoder used Q(z)=P(z/2^${exponent}) ` +
      `and the exact radix substitution z=2^${exponent}x. ` + r.note,
  };
}

function compileOddWithConditioning(p) {
  const n = p.length - 1;
  const limit = Math.max(1, Math.floor(900 / n));
  const rawIdeal = Math.round(Math.log2(Math.abs(p[n])) / n);
  const ideal = Math.max(-limit, Math.min(limit, rawIdeal));
  const exponents = [];
  const add = b => { if (Math.abs(b) <= limit && !exponents.includes(b)) exponents.push(b); };
  if (ideal !== 0) { add(ideal); add(ideal - 1); add(ideal + 1); add(0); }
  else { add(0); add(-1); add(1); add(-2); add(2); }

  // every rescale gets SLICE cells per round until one succeeds, the searches
  // are exhausted, or MAX_CELLS are spent in total
  let lastError = null, total = MAX_CELLS;
  const states = exponents.map(exponent => {
    const q = p.map((v, i) => v * Math.pow(2, -exponent * i));
    return { exponent, q, skip: 0, best: null, done: !q.every(Number.isFinite) || q[n] === 0 };
  });
  while (total > 0 && states.some(s => !s.done)) {
    for (const s of states) {
      if (s.done || total <= 0) continue;
      const budget = { cells: Math.min(SLICE, total), skip: s.skip, best: s.best };
      try {
        const r = compilePanOddCore(s.q, budget);
        const scaled = withInputRadixScale(r, p, s.exponent);
        if (scaled) return scaled;
        s.done = true;
      } catch (e) { lastError = e; if (budget.finished) s.done = true; }
      total -= budget.used ?? 0; s.skip += budget.used ?? 0; s.best = budget.best ?? s.best;
    }
  }
  throw lastError ?? new Error('Pan real: no numerically safe power-of-two decoding chart was found');
}

function compileEvenLift(p) {
  const n = p.length - 1;
  const lower = compilePan1978Real(p.slice(1));
  const lines = lower.lines.map(line => ({ ...line }));
  lines[lines.length - 1].lhs = 'Q';
  const product = 'x * Q', rhs = appendConst(product, C(p[0]), 17);
  lines.push({ lhs: 'P', rhs, mul: true });
  const err = verifyLines(lines, p);
  if (!(err <= 1e-3))
    throw new Error(`Pan real: the degree-${n} even lift failed printed-chain verification (${err})`);
  return {
    ...lower, name: 'Pan even-degree lift', lines,
    mults: lower.mults + 1, adds: lower.adds + (rhs === product ? 0 : 1),
    height: lower.height + 1, maxRelError: err, preserveChainForm: false,
    note: `Pan even-degree reduction P(x)=x Q_${n - 1}(x)+a_0, followed by ` + lower.note,
  };
}

/** Pan's real compiler: the separate degree-8 construction, scheme (9) in
 * odd degree >= 9, and a one-product lift in even degree >= 10. */
export function compilePan1978Real(coeffs) {
  if (!Array.isArray(coeffs) || coeffs.length === 0)
    throw new Error('Pan real: need a nonempty coefficient array');
  const p = coeffs.map(Number), n = p.length - 1;
  if (!p.every(Number.isFinite)) throw new Error('Pan real: coefficients must be finite numbers');
  if (n > 0 && p[n] === 0) throw new Error('Pan real: the leading coefficient must be nonzero');
  if (n < 8)
    throw new Error(`Pan: the separate real construction begins at degree 8; use Knuth--Eve in degree ${n}. ` +
      `In particular, a general degree-7 polynomial provably needs 5 multiplications (Pan 1978, Table 3), ` +
      `so the 4-multiplication half-count cannot extend to degree 7`);
  if (n === 8) return compilePanEight(p);
  if (n % 2 === 0) return compileEvenLift(p);
  return compileOddWithConditioning(p);
}
