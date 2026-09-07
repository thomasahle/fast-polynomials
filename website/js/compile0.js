// char-0 compilation pipeline: source text -> decode -> verified chain.
// Backed by ./char0/core.js (faithful port of tools/polychain.py +
// tools/poly_schedule.py). Field modes (ids of js/field.js FIELDS):
//   'Q'     exact rationals (constants grow explosively beyond degree ~40)
//   'R'     the same exact rational preprocessing, with the constants displayed
//           and emitted in C as doubles (≈ numeric: only that rounding is inexact)
//   'C'     the same exact preprocessing over the Gaussian rationals ℚ(i)
//           (js/gauss.js), with the constants displayed as complex doubles —
//           the canonical (re±imi) token of js/tokens.js (≈ numeric, as ℝ)
//   'p61' | 'p89' | 'p127'   Mersenne primes 2^k − 1 ('p' = 'p89', the paper's)
import { parsePoly, polyToString } from './polyparse.js';
import { Rat } from './rat.js';
import { GaussRat, gaussCoreField } from './gauss.js';
import { makeResult, renderAffineChain, chainToText, paperWireNames, gateGroups, renderConstructionsForm } from './chain.js';
import { buildGraphFromAffineChain } from './graph.js';
import { char0C } from './cgen.js';
import { fieldById, ratToDouble, ratToDoubleString, primeName } from './field.js';
// the degree above which exact preprocessing is worth a warning: the same number
// the page shows as its slow threshold (uistate.js SLOW_DEGREE = MAX_DEGREE)
import { MAX_DEGREE as SLOW_DEGREE, REL_ERROR_WARN } from './methodlist.js';


let corePromise = null;
const loadCore = () => (corePromise ??= import('./char0/core.js').catch(() => {
  corePromise = null;
  throw new Error(
    'the characteristic-0 compiler is still being assembled — try the char 2 lane, ' +
    'or reload in a bit.');
}));

export async function compileChar0(src, fieldMode = 'Q') {
  const core = await loadCore();
  const fd = fieldById(fieldMode === 'p' ? 'p89' : fieldMode);
  if (fd.lane !== 'char0') throw new Error(`${fd.name} is a characteristic-2 field; use the char 2 lane`);
  const isQ = fd.id === 'Q', isR = fd.id === 'R', isC = !!fd.complex, prime = fd.prime;
  const { coeffs } = parsePoly(src, { char2: false, complex: isC });   // ℂ: every coefficient a GaussRat
  let n = coeffs.length - 1;
  if (n < 1) throw new Error('need degree ≥ 1');

  // ℚ, ℝ and ℂ share the exact decoder (over ℚ, or over ℚ(i) through the
  // duck-typed Gaussian field); they differ only in how the constants are
  // displayed (ℝ: as doubles, ℂ: as complex doubles) and in the reported status.
  const rational = isQ || isR || isC;
  const field = isC ? gaussCoreField() : rational ? core.rationals() : core.GF(prime);
  const F = isQ ? QDisplay : isR ? RDisplay : isC ? CDisplay : fpDisplay(prime);

  // move coefficients into the field
  let cs = rational ? coeffs : coeffs.map(r => field.div(field.coerce(r.n), field.coerce(r.d)));

  // monic normalization
  const lc = cs[n];                                    // display / C form of the leading coefficient
  let scaleStep = null, extraMult = 0;
  if (!F.isOne(lc)) {
    const inv = field.inv(lc);
    cs = cs.map(c => field.mul(c, inv));
    scaleStep = { lhs: 'P', rhs: `${F.toDisplay(lc)} * P̃   (leading-coefficient scale)`, mul: true };
    extraMult = 1;
  }

  const params = core.decode(n, cs, field);         // self-verifying (re-expansion check)
  const chain = core.compile_paper_params_chain(params, isC ? field : rational ? null : prime);
  chain.validate?.();

  // independent verification: exact chain.eval at random points vs Horner
  // (over ℂ at points with Im x ≠ 0 too)
  for (let trial = 0; trial < 4; trial++) {
    const x0 = isC ? new GaussRat(new Rat(BigInt(trial * 7 - 11), 3n), new Rat(BigInt(trial * 5 - 8), 4n))
      : rational ? new Rat(BigInt(trial * 7 - 11), 3n) : field.coerce(BigInt(trial) * 1234567n + 3n);
    const lhs = chain.eval(x0);
    let rhs = field.zero();
    for (let i = n; i >= 0; i--)
      rhs = field.add(field.mul(rhs, x0), cs[i]);
    if (!F.eq(lhs, rhs)) throw new Error('internal error: chain evaluation mismatch — please report this input');
  }
  // ℝ: the chain is exact, but its constants are shown and emitted as doubles;
  // report what that rounding costs (a diagnostic — no decision depends on it)
  // ℂ on a real input is ℝ's chain: report ℝ's figure (same sample points), so
  // the two fields agree to the digit; complex inputs are sampled off the axis
  const allReal = isC && coeffs.every(c => toGauss(c).isReal());
  // constants representable as doubles at all?  (a chain whose constants fit can
  // still overflow when evaluated at the sample points: a different message)
  const consts = [...chain.gates.flatMap(g => [g.left.const, g.right.const]), chain.output.const, lc];
  const fitsDouble = c => { const v = isC ? toCx(c) : { re: toDouble(c), im: 0 }; return Number.isFinite(v.re) && Number.isFinite(v.im); };
  const constantsFinite = rational && consts.every(fitsDouble);
  const maxRelError = isR ? doubleRoundingError(chain, coeffs, lc)
    : isC ? (allReal ? doubleRoundingError(chain, coeffs.map(c => toGauss(c).re), toGauss(lc).re) : complexRoundingError(chain, coeffs, lc))
      : null;

  // the math view names the products with the appendix letters (y, z, t, u, …),
  // the same names the C code and the graph use
  const lines = renderAffineChain(F, chain, { names: 'letters' });
  if (scaleStep) lines[lines.length - 1].lhs = 'P̃';
  // paper-format rendering (letter names + gadget headings) for the UI toggle
  const linesPaper = renderAffineChain(F, chain, { names: 'letters', group: true });
  if (scaleStep) linesPaper[linesPaper.length - 1].lhs = 'P̃';
  const mults = chain.gates.length + extraMult;
  const slowNote = n > SLOW_DEGREE
    ? ' — note: exact rational constants grow quickly with degree, and fractional coefficients can make preprocessing take minutes here; the Mersenne modes are instant at any size'
    : '';
  const note = isQ
    ? 'exact rational preprocessing; verified by re-expansion and random-point evaluation' + slowNote
    : isR
    ? 'exact rational preprocessing (as ℚ), verified by re-expansion and random-point evaluation; ' +
      'the constants are displayed and emitted in C as doubles (≈ numeric): ' +
      (Number.isFinite(maxRelError)
        ? `rounding them costs a max relative error of ${maxRelError.toExponential(1)} on sample evaluations of the double-precision chain` +
          (maxRelError > REL_ERROR_WARN ? ' — the exact chain constants for this input are large (compare the ℚ mode), so the rounded doubles lose accuracy' : '')
        : constantsFinite
          ? 'the double-precision chain overflows at the sample points (|x| up to 3/2): its constants are representable, so the C is emitted, but expect overflow away from small |x|'
          : 'the exact chain constants for this input exceed the double range (compare the ℚ mode), so no double-precision chain exists') +
      slowNote
    : isC
    ? 'exact preprocessing over the Gaussian rationals ℚ(i) (as ℚ), verified by re-expansion and evaluation at points with Im x ≠ 0; ' +
      `the constants are displayed${fd.cCode ? ' and emitted in C' : ''} as complex doubles (≈ numeric): ` +
      (Number.isFinite(maxRelError)
        ? `rounding them costs a max relative error of ${maxRelError.toExponential(1)} on sample evaluations of the complex-double chain` +
          (maxRelError > REL_ERROR_WARN ? ' — the exact chain constants for this input are large, so the rounded doubles lose accuracy' : '')
        : constantsFinite
          ? 'the complex-double chain overflows at the sample points (|x| up to about 1.51): its constants are representable, but expect overflow away from small |x|'
          : 'the exact chain constants for this input exceed the double range, so no complex-double chain exists') +
      slowNote
    : `preprocessing over ${fd.name} (Mersenne prime${prime === fieldById('p89').prime ? ', as in the paper\'s experiments' : ''}); verified by re-expansion and random-point evaluation`;
  const result = makeResult({
    field: F, n, lines, mults,
    adds: countAdds(chain),
    height: chainHeight(chain),
    scaleStep, note,
  });
  // the C header repeats the rounding figure (ℝ / ℂ) and, for the keyed entry point
  // of the Mersenne fields, the degree
  const copts = { scaleBy: scaleStep ? lc : null, poly: polyToString(coeffs), horner: n - 1 + extraMult, maxRelError, degree: n };
  result.chain = chain;                       // verified PolynomialChain (gate_labels parallel to gates)
  result.fieldId = fd.id;
  result.exact = fd.exact;
  result.status = fd.status;
  result.maxRelError = maxRelError;
  result.mathText = chainToText(result);      // letter names (y, z, t, …), as in the C and the graph
  result.linesPaper = scaleStep ? [...linesPaper, scaleStep] : linesPaper;
  result.mathTextOriginal = renderConstructionsForm(F, chain, scaleStep);  // rows as in sections/constructions
  // C rendering is optional: over Q / R the exact chain constants can exceed the
  // double range, in which case the math/graph views must survive without it;
  // result.cMissing then says why (the UI shows it in place of the C).
  // A field without a C emitter yet (registry cCode false) renders none, silently.
  let cError = null;
  const tryC = (mode, cstyle) => {
    try { return char0C(chain, mode, { ...copts, cstyle }); }
    catch (e) { cError = e.message; result.note += ` — no C rendering: ${e.message}`; return null; }
  };
  result.cText = fd.cCode ? tryC(fd.id, 'float') : null;
  if (fd.cCode && result.cText === null)
    result.cMissing = rational && !constantsFinite ? NO_DOUBLE_CHAIN : cError;
  // Q mode only: the same code with exact (double)NUM/DEN constants, so the UI
  // can switch constant styles without recompiling.
  result.cTextFraction = isQ && result.cText ? tryC('Q', 'fraction') : null;
  // computational graph IR (paper letter names, gadget groups, leading-coefficient scale node)
  try {
    result.graph = buildGraphFromAffineChain(chain, F,
      { names: paperWireNames(chain), groups: gateGroups(chain), scaleBy: scaleStep ? lc : null });
  } catch (e) { result.graph = null; }
  return result;
}

/** result.cMissing when the exact chain has no double rendering (ℚ / ℝ / ℂ). */
const NO_DOUBLE_CHAIN = 'an exact constant exceeds the double range, so no double-precision chain exists ' +
  '(the math view shows the exact chain; a lower degree or a Mersenne-prime field has one)';

const termVals = t => (t instanceof Map ? [...t.values()] : Object.values(t));
const termKeys = t => (t instanceof Map ? [...t.keys()] : Object.keys(t).map(Number));
const termEntries = t => (t instanceof Map ? [...t.entries()] : Object.entries(t).map(([w, k]) => [Number(w), k]));

// The port mirrors Python's int-mixing: AffineForm constants may arrive as plain
// Numbers (e.g. 0) rather than Rat/BigInt, so every display helper coerces.
const toRat = c => {
  if (c instanceof GaussRat) { if (!c.isReal()) throw new Error('complex constant where a rational was expected'); return c.re; }
  return Rat.of(typeof c === 'number' ? BigInt(c) : c);
};
const toBig = c => (typeof c === 'bigint' ? c : BigInt(c));
const toDouble = c => { const r = toRat(c); return ratToDouble(r.n, r.d); };
const toGauss = c => GaussRat.of(typeof c === 'number' ? BigInt(c) : c);
/** A Gaussian rational (or anything toGauss accepts) as { re, im } doubles. */
const toCx = c => { const g = toGauss(c); return { re: ratToDouble(g.re.n, g.re.d), im: ratToDouble(g.im.n, g.im.d) }; };

/**
 * Max relative error of the ℝ rendering: the exact rational chain evaluated in
 * double precision with every constant rounded to its nearest double (exactly
 * what the emitted C computes), against the exact value of P at sample points,
 * relative to max(1, Σ|c_i x^i|). Infinity when a constant exceeds the double
 * range (then no C is rendered either).
 */
function doubleRoundingError(chain, coeffs, lc) {
  const n = coeffs.length - 1;
  const evalForm = (f, wires) => {
    let v = toDouble(f.const);
    for (const [w, k] of termEntries(f.terms)) if (k !== 0) v += k * wires[w];
    return v;
  };
  let err = 0;
  for (const [a, b] of [[-5n, 4n], [-1n, 2n], [3n, 8n], [3n, 4n], [3n, 2n]]) {   // exact as doubles
    const xr = new Rat(a, b), x0 = Number(a) / Number(b);
    const wires = [1, x0];
    for (const g of chain.gates) wires[g.out_wire] = evalForm(g.left, wires) * evalForm(g.right, wires);
    let got = evalForm(chain.output, wires);
    if (!toRat(lc).isOne()) got *= toDouble(lc);
    let want = Rat.ZERO, mag = 0;
    for (let i = n; i >= 0; i--) { want = want.mul(xr).add(coeffs[i]); mag = mag * Math.abs(x0) + Math.abs(toDouble(coeffs[i])); }
    err = Math.max(err, Math.abs(got - toDouble(want)) / Math.max(1, mag));
  }
  return Number.isFinite(err) ? err : Infinity;
}

/**
 * The ℂ counterpart of doubleRoundingError: the exact chain over ℚ(i)
 * evaluated in complex double precision with every constant rounded to its
 * nearest complex double, against the exact value of P at sample points with
 * Im x ≠ 0, relative to max(1, Σ|c_i||x|^i) (moduli by hypot). Infinity when a
 * constant exceeds the double range.
 */
function complexRoundingError(chain, coeffs, lc) {
  const n = coeffs.length - 1;
  const cmul = (a, b) => ({ re: a.re * b.re - a.im * b.im, im: a.re * b.im + a.im * b.re });
  const evalForm = (f, wires) => {
    const v = toCx(f.const);
    for (const [w, k] of termEntries(f.terms)) if (k !== 0) { v.re += k * wires[w].re; v.im += k * wires[w].im; }
    return v;
  };
  let err = 0;
  // exact as doubles; every point has a nonzero imaginary part but one
  for (const [a, b, c, d] of [[-5n, 4n, 1n, 2n], [-1n, 2n, -3n, 4n], [3n, 8n, 0n, 1n], [3n, 4n, 1n, 4n], [3n, 2n, -1n, 8n]]) {
    const xr = new GaussRat(new Rat(a, b), new Rat(c, d)), x0 = toCx(xr), ax = Math.hypot(x0.re, x0.im);
    const wires = [{ re: 1, im: 0 }, x0];
    for (const g of chain.gates) wires[g.out_wire] = cmul(evalForm(g.left, wires), evalForm(g.right, wires));
    let got = evalForm(chain.output, wires);
    if (!toGauss(lc).isOne()) got = cmul(got, toCx(lc));
    let want = GaussRat.ZERO, mag = 0;
    for (let i = n; i >= 0; i--) { want = want.mul(xr).add(coeffs[i]); const ci = toCx(coeffs[i]); mag = mag * ax + Math.hypot(ci.re, ci.im); }
    const w = toCx(want);
    err = Math.max(err, Math.hypot(got.re - w.re, got.im - w.im) / Math.max(1, mag));
  }
  return Number.isFinite(err) ? err : Infinity;
}

function countAdds(chain) {
  let adds = 0;
  const formAdds = f => {
    let terms = termVals(f.terms).filter(k => k !== 0);
    let c = terms.reduce((s, k) => s + Math.abs(k), 0); // integer multiples = repeated adds
    if (!isZeroConst(f.const)) c += 1;
    return Math.max(0, c - 1);
  };
  // one addition per extra term of every affine factor (integer multiples are
  // repeated additions; scalar constants cost one addition when nonzero)
  for (const g of chain.gates) adds += formAdds(g.left) + formAdds(g.right);
  return adds + formAdds(chain.output);
}
const isZeroConst = c => (c instanceof Rat || c instanceof GaussRat ? c.isZero() : (typeof c === 'number' ? c === 0 : c === 0n));

function chainHeight(chain) {
  const depth = { 0: 0, 1: 0 };
  for (const g of chain.gates) {
    let d = 0;
    for (const f of [g.left, g.right])
      for (const w of termKeys(f.terms)) d = Math.max(d, depth[w] ?? 0);
    depth[g.out_wire] = d + 1;
  }
  let h = 0;
  for (const w of termKeys(chain.output.terms)) h = Math.max(h, depth[w] ?? 0);
  return h;
}

const QDisplay = {
  name: 'ℚ',
  isZero: c => toRat(c).isZero(), isOne: c => toRat(c).isOne(),
  eq: (a, b) => toRat(a).eq(toRat(b)),
  toDisplay: c => toRat(c).toString(),
};
// ℝ: the same exact elements, displayed as doubles (shortest round-trip decimals)
const RDisplay = {
  ...QDisplay, name: 'ℝ',
  toDisplay: c => { const r = toRat(c); return ratToDoubleString(r.n, r.d); },
};
// ℂ: Gaussian rationals, displayed as complex doubles — a real value prints
// exactly as ℝ prints, a non-real one as the canonical (re±imi) token
const CDisplay = {
  name: 'ℂ',
  isZero: c => toGauss(c).isZero(), isOne: c => toGauss(c).isOne(),
  eq: (a, b) => toGauss(a).eq(toGauss(b)),
  toDisplay: c => toGauss(c).toDisplay(),
};
const fpDisplay = p => ({
  name: primeName(p),
  isZero: c => toBig(c) === 0n, isOne: c => toBig(c) === 1n,
  eq: (a, b) => toBig(a) === toBig(b),
  toDisplay: c => toBig(c).toString(),
});
