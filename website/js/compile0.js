// char-0 compilation pipeline: source text -> decode -> verified chain.
// Backed by ./char0/core.js (faithful port of tools/polychain.py +
// tools/poly_schedule.py). Field modes (ids of js/field.js FIELDS):
//   'Q'     exact rationals (constants grow explosively beyond degree ~40)
//   'R'     the same exact rational preprocessing, with the constants displayed
//           and emitted in C as doubles (≈ numeric: only that rounding is inexact)
//   'p61' | 'p89' | 'p127'   Mersenne primes 2^k − 1 ('p' = 'p89', the paper's)
import { parsePoly } from './polyparse.js';
import { Rat } from './rat.js';
import { makeResult, renderAffineChain, chainToText, paperWireNames, gateGroups, renderConstructionsForm } from './chain.js';
import { buildGraphFromAffineChain } from './graph.js';
import { char0C } from './cgen.js';
import { fieldById, ratToDouble, ratToDoubleString, primeName } from './field.js';


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
  const { coeffs } = parsePoly(src, { char2: false });
  let n = coeffs.length - 1;
  if (n < 1) throw new Error('need degree ≥ 1');

  // ℚ and ℝ share the exact rational decoder; they differ only in how the
  // constants are displayed (ℝ: as doubles) and in the reported status.
  const isQ = fd.id === 'Q', isR = fd.id === 'R', rational = isQ || isR, prime = fd.prime;
  const field = rational ? core.rationals() : core.GF(prime);
  const F = isQ ? QDisplay : isR ? RDisplay : fpDisplay(prime);

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
  const chain = core.compile_paper_params_chain(params, rational ? null : prime);
  chain.validate?.();

  // independent verification: exact chain.eval at random points vs Horner
  for (let trial = 0; trial < 4; trial++) {
    const x0 = rational ? new Rat(BigInt(trial * 7 - 11), 3n) : field.coerce(BigInt(trial) * 1234567n + 3n);
    const lhs = chain.eval(x0);
    let rhs = field.zero();
    for (let i = n; i >= 0; i--)
      rhs = field.add(field.mul(rhs, x0), cs[i]);
    if (!F.eq(lhs, rhs)) throw new Error('internal error: chain evaluation mismatch — please report this input');
  }
  // ℝ: the chain is exact, but its constants are shown and emitted as doubles;
  // report what that rounding costs (a diagnostic — no decision depends on it)
  const maxRelError = isR ? doubleRoundingError(chain, coeffs, lc) : null;

  const lines = renderAffineChain(F, chain);
  if (scaleStep) lines[lines.length - 1].lhs = 'P̃';
  // paper-format rendering (appendix letter names + gadget headings) for the UI toggle
  const linesPaper = renderAffineChain(F, chain, { names: 'letters', group: true });
  if (scaleStep) linesPaper[linesPaper.length - 1].lhs = 'P̃';
  const mults = chain.gates.length + extraMult;
  const slowNote = n > 26
    ? ' — note: exact rational constants grow quickly with degree, and fractional coefficients can make preprocessing take minutes here (Cancel any time); the Mersenne modes are instant at any size'
    : '';
  const note = isQ
    ? 'exact rational preprocessing; verified by re-expansion and random-point evaluation' + slowNote
    : isR
    ? 'exact rational preprocessing (as ℚ), verified by re-expansion and random-point evaluation; ' +
      'the constants are displayed and emitted in C as doubles (≈ numeric): ' +
      (Number.isFinite(maxRelError)
        ? `rounding them costs a max relative error of ${maxRelError.toExponential(1)} on sample evaluations of the double-precision chain` +
          (maxRelError > 1e-6 ? ' — the exact chain constants for this input are large (compare the ℚ mode), so the rounded doubles lose accuracy' : '')
        : 'the exact chain constants for this input exceed the double range (compare the ℚ mode), so no double-precision chain exists') +
      slowNote
    : `preprocessing over ${fd.name} (Mersenne prime${prime === fieldById('p89').prime ? ', as in the paper\'s experiments' : ''}); verified by re-expansion and random-point evaluation`;
  const result = makeResult({
    field: F, n, lines, mults,
    adds: countAdds(chain),
    height: chainHeight(chain),
    scaleStep, note,
  });
  const copts = { scaleBy: scaleStep ? lc : null };
  result.chain = chain;                       // verified PolynomialChain (gate_labels parallel to gates)
  result.fieldId = fd.id;
  result.exact = fd.exact;
  result.status = fd.status;
  result.maxRelError = maxRelError;
  result.mathText = chainToText(result);      // index names (y0, y1, …)
  result.linesPaper = scaleStep ? [...linesPaper, scaleStep] : linesPaper;
  result.mathTextOriginal = renderConstructionsForm(F, chain, scaleStep);  // rows as in sections/constructions
  // C rendering is optional: over Q / R the exact chain constants can exceed the
  // double range, in which case the math/graph views must survive without it.
  const tryC = (mode, cstyle) => {
    try { return char0C(chain, mode, { ...copts, cstyle }); }
    catch (e) { result.note += ` — no C rendering: ${e.message}`; return null; }
  };
  result.cText = tryC(fd.id, 'float');
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

const termVals = t => (t instanceof Map ? [...t.values()] : Object.values(t));
const termKeys = t => (t instanceof Map ? [...t.keys()] : Object.keys(t).map(Number));
const termEntries = t => (t instanceof Map ? [...t.entries()] : Object.entries(t).map(([w, k]) => [Number(w), k]));

// The port mirrors Python's int-mixing: AffineForm constants may arrive as plain
// Numbers (e.g. 0) rather than Rat/BigInt, so every display helper coerces.
const toRat = c => Rat.of(typeof c === 'number' ? BigInt(c) : c);
const toBig = c => (typeof c === 'bigint' ? c : BigInt(c));
const toDouble = c => { const r = toRat(c); return ratToDouble(r.n, r.d); };

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
const isZeroConst = c => (c instanceof Rat ? c.isZero() : (typeof c === 'number' ? c === 0 : c === 0n));

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
const fpDisplay = p => ({
  name: primeName(p),
  isZero: c => toBig(c) === 0n, isOne: c => toBig(c) === 1n,
  eq: (a, b) => toBig(a) === toBig(b),
  toDisplay: c => toBig(c).toString(),
});
