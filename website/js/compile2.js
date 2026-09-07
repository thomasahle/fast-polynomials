// char-2 compilation pipeline: coefficients -> keys -> verified chain.
//
// Every degree 1..26 compiles (char2.js SUPPORTED_DEGREES):
//   odd n = 3..25   the fixed circuit CIRCUITS[n] with its exact decoder
//   n = 1, 2        P = x + a0 (no multiplication), P = x (x + a1) + a0 (one);
//                   the coefficients are the keys
//   even n = 4..26  the paper's even lift: P = x · P_{n-1} + c0 with the monic
//                   odd part P_{n-1} = (P − c0)/x decoded by the circuit of
//                   degree n−1 and one extra multiplication (floor(n/2)+1 in
//                   total), rendered as a final row like the scale row
// A non-monic input adds the leading-coefficient scale row P = lc · P̃ (one
// more multiplication), exactly as in the char-0 lane.
import * as P from './poly.js';
import { CIRCUITS, evalCircuit, decodeChar2, circuitStats, SUPPORTED_DEGREES, MAX_DEGREE,
         baseDegree } from './char2.js';
import { DEGREE_CEILING } from './methodlist.js';   // the Mersenne ceiling this message points at
import { renderGateChain, makeResult, chainToText } from './chain.js';
import { char2C } from './cgen.js';
import { polyToString } from './polyparse.js';
import { buildGraphFromLines } from './graph.js';

// How the keys were recovered (CIRCUITS[n].family); the polynomial decoders are
// defined over every field of characteristic two, the Frobenius ones take
// unique 2^t-th roots and so need a perfect field (every finite GF(2^k) is one).
const DECODER_NOTE = {
  'unitriangular': 'unit-pivot (polynomial, any characteristic-2 field)',
  'closed-form':   'closed-form back-substitution (polynomial, any characteristic-2 field)',
  'frobenius':     'unit pivots + Frobenius-root rows (finite fields GF(2^k))',
  'pivot-loop':    'unit pivots + Frobenius-root rows (finite fields GF(2^k))',
  'identity':      'identity (the coefficients are the keys; any characteristic-2 field)',
};

// Degrees 1 and 2 need no search circuit: the same gate/out spec format as
// CIRCUITS (renderGateChain, circuitStats, char2C and evalCircuit all apply),
// with key i = coefficient c_i.
const TRIVIAL = {
  1: { n: 1, keys: 1, family: 'identity', gates: [], out: { t: ['x'], k: 0 } },
  2: { n: 2, keys: 2, family: 'identity',
       gates: [{ w: 'y', l: { t: ['x'], k: null }, r: { t: ['x'], k: 1 } }],
       out: { t: ['y'], k: 0 } },
};

/** The circuit spec used for a supported degree (odd: its own; even ≥ 4: degree n−1). */
export function circuitFor(n) {
  const m = baseDegree(n);
  return CIRCUITS[m] ?? TRIVIAL[m] ?? null;
}

export function compileChar2(coeffs, F) {
  let p = P.normalize(F, coeffs);
  const n = P.deg(p);
  if (n < 1) throw new Error('need degree ≥ 1');
  if (!SUPPORTED_DEGREES.includes(n))
    throw new Error(
      `characteristic-2 chains exist for every degree up to ${MAX_DEGREE} (you entered degree ${n}); ` +
      `degree ${MAX_DEGREE + 1} is the open frontier of the paper (section "Open Problems") — ` +
      `the Mersenne-prime fields GF(2^61−1), GF(2^89−1) and GF(2^127−1) compile any degree up to ${DEGREE_CEILING.p61}.`);
  // normalize to monic; remember the leading coefficient
  const lc = p[n];
  let scaleStep = null, extraMult = 0;
  if (!F.isOne(lc)) {
    p = P.scale(F, F.inv(lc), p);
    scaleStep = { lhs: 'P', rhs: `${F.toDisplay(lc)} * P̃   (leading-coefficient scale)`, mul: true };
    extraMult = 1;
  }
  const c = [];
  for (let i = 0; i < n; i++) c.push(P.coeff(F, p, i));
  // even n ≥ 4: decode the monic odd part P_{n-1} = (P − c0)/x, i.e. the
  // coefficients c1..c_{n-1}, with the circuit of degree n−1; the lift row
  // P = x · P_{n-1} + c0 restores the input
  const m = baseDegree(n), lifted = m !== n;
  const spec = circuitFor(n);
  const cBase = lifted ? c.slice(1) : c;
  const keys = m <= 2 ? cBase : decodeChar2(m, cBase, F);   // degrees 1, 2: key i = c_i
  // verify: re-expand (lift included) and compare against the monic input
  const { coeffs: core } = evalCircuit(spec, keys, F);
  const back = lifted ? P.add(F, P.mul(F, P.X(F), core), P.C(F, c[0])) : core;
  if (!P.eqPoly(F, back, p))
    throw new Error('internal error: chain verification failed — please report this input');
  const st = circuitStats(spec);
  const coreName = lifted ? `P_${m}` : 'P';
  const liftStep = lifted
    ? { lhs: 'P', rhs: `x * ${coreName}${F.isZero(c[0]) ? '' : ' + ' + F.toDisplay(c[0])}   (even-degree lift)`, mul: true }
    : null;
  // index-name rendering and the paper-format rendering (the circuit's letters
  // are already the appendix scheme; headings appear only if a circuit carries
  // gate labels); the circuit's output row is renamed when a lift or scale follows
  const lines = renderGateChain(F, spec, keys);
  const linesPaper = renderGateChain(F, spec, keys, { names: 'letters', group: true });
  for (const ls of [lines, linesPaper]) {
    ls[ls.length - 1].lhs = lifted ? coreName : scaleStep ? 'P̃' : 'P';
    if (liftStep) ls.push({ ...liftStep, lhs: scaleStep ? 'P̃' : 'P' });
  }
  const how = m <= 2
    ? `degree-${n} chain`
    : lifted
    ? `fixed char-2 circuit of degree ${m} lifted to degree ${n} (P = x · P_${m} + c0)`
    : 'fixed char-2 circuit';
  const result = makeResult({
    field: F, n, lines,
    mults: st.mults + (lifted ? 1 : 0) + extraMult,
    adds: st.adds + (lifted ? 1 : 0),
    height: st.height + (lifted ? 1 : 0),
    scaleStep,
    note: `${how}, ${DECODER_NOTE[spec.family] ?? spec.family} decoder; ` +
          `decoded over ${F.name}; verified by exact re-expansion`,
  });
  result.baseDegree = m;
  result.liftStep = liftStep;
  result.mathText = chainToText(result);
  result.linesPaper = scaleStep ? [...linesPaper, scaleStep] : linesPaper;
  result.mathTextOriginal = chainToText({ lines: result.linesPaper });
  // C is emitted for GF(2^32), GF(2^64) (the paper's field) and GF(2^128) with
  // their standard moduli; other fields keep the math view (result.cMissing then
  // carries the reason).  The header names the INPUT polynomial (coeffs), not
  // the monic-scaled p the circuit was decoded from.
  try { result.cText = char2C(F, spec, keys, { scaleBy: scaleStep ? lc : null, lift: lifted ? c[0] : null, poly: polyToString(coeffs, { char2: true }) }); }
  catch (e) { result.cText = null; result.cMissing = e.message; result.note += ` — no C rendering: ${e.message}`; }
  // computational graph IR from the rendered lines (letter wire names; the lift
  // and scale rows become the last '*' nodes; headings carry the groups)
  try { result.graph = buildGraphFromLines(result.lines); }
  catch (e) { result.graph = null; }
  return result;
}
