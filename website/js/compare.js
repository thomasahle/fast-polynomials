// Run the classical methods on the same input; each row carries its full
// chain (mathematical) and generated C.
import { compileHorner } from './methods/horner.js';
import { compileEstrin } from './methods/estrin.js';
import { compileRW } from './methods/rw.js';
import { chainToText, factorize } from './chain.js';
import { methodChainC } from './cgen.js';
import { compileKnuthEve, verifyLinesComplex } from './methods/motzkin.js';
import { compilePan1978Real } from './methods/pan1978real.js';
import { compileKnuthEveComplex } from './methods/knutheve-complex.js';
import { compilePan1978 } from './methods/pan1978.js';
import { compileBelaga } from './methods/belaga.js';
import { buildGraphFromLines } from './graph.js';
import { hasComplexToken, complexToken } from './tokens.js';
import { FIELDS, ratToDouble } from './field.js';

const graphOf = lines => { try { return buildGraphFromLines(lines); } catch (e) { return null; } };
/** Whether the registry renders C for a mode; the legacy spellings ('p',
 *  'gf2k') are not registry ids and always have C. */
const fieldHasC = mode => FIELDS.find(f => f.id === mode)?.cCode ?? true;

const METHODS = [
  ['Horner', compileHorner],
  ['Estrin', compileEstrin],
  ['Rabin–Winograd', compileRW],
];

/** mode: a field id from js/field.js FIELDS ('Q', 'R', 'p61', 'p89', 'p127',
 *  'gf32', 'gf64', 'gf128'); the legacy 'p' (= p89) and 'gf2k' (F.k decides)
 *  are still accepted by the C emitter. */
export function buildComparisons(coeffs, F, mode, opts = {}) {
  return [...buildClassical(coeffs, F, mode, opts), ...buildNumeric(coeffs, F, mode, opts)];
}

/** The numeric methods run in their own worker (they can take seconds at high
 *  degree — Pan's real-root preprocessing above all); over the other fields
 *  they are rejected at once, so no second worker is needed there.
 *  Over ℚ / ℝ the rows are Knuth–Eve (real roots) and Pan's real schemes; over
 *  ℂ Knuth–Eve with complex roots, Pan's complex scheme of 1978 and Belaga's
 *  scheme (numericMethodsFor); the other fields list ℚ's two, rejected. */
export const NUMERIC_METHODS = ['Knuth\u2013Eve', 'Pan'];
const NUMERIC_METHODS_C = [...NUMERIC_METHODS, 'Belaga'];
export const numericMethodsFor = mode => (mode === 'C' ? NUMERIC_METHODS_C : NUMERIC_METHODS);
export const needsNumericWorker = mode => mode === 'Q' || mode === 'R' || mode === 'C';
/** Rows standing in for the numeric methods until their worker replies. */
export const pendingNumericRows = (mode = 'Q') =>
  numericMethodsFor(mode).map(name => ({ name, ok: false, pending: true, note: 'computing the numerical preprocessing\u2026' }));

/** Horner, Estrin and Rabin–Winograd: exact, instant. */
export function buildClassical(coeffs, F, mode, { poly = null } = {}) {
  const rows = [];
  const numericField = !!(F.real || F.complex);   // ℝ, ℂ: preprocessing with doubles is not exact
  const hasC = fieldHasC(mode);
  for (const [name, fn] of METHODS) {
    try {
      const r = fn(coeffs, F);
      let cText = null, cTextFraction = null;
      const copts = { name, mults: r.mults, preprocessing: r.preprocessing, poly };   // the emitter cites the method's reference
      if (hasC) {
        try { cText = methodChainC(r.lines, mode, F, { ...copts, cstyle: 'float' }); }
        catch (e) { /* math view still available */ }
      }
      if (mode === 'Q' && cText) {
        try { cTextFraction = methodChainC(r.lines, mode, F, { ...copts, cstyle: 'fraction' }); }
        catch (e) { /* float variant still available */ }
      }
      rows.push({
        name, ok: true, mults: r.mults, adds: r.adds, height: r.height,
        preprocessing: numericField && r.preprocessing !== 'none' ? 'numeric' : r.preprocessing,
        exact: numericField ? r.preprocessing === 'none' : r.exact,
        mathText: chainToText({ lines: factorize(r.lines) }), mathTextOriginal: chainToText(r), cText, cTextFraction,
        graph: graphOf(r.lines), note: r.note ?? '',
      });
    } catch (e) {
      rows.push({ name, ok: false, note: e.message });
    }
  }
  return rows;
}

/** Knuth–Eve and Pan (and Belaga over ℂ): numerical preprocessing, characteristic 0 only. */
export function buildNumeric(coeffs, F, mode, { poly = null, only = null } = {}) {
  const rows = [];
  // Every field lists the same methods, so the comparison table keeps
  // its shape.  These algebraic/numeric preprocessors run in characteristic
  // zero only and are reported (not silently dropped) elsewhere.  Unlike the
  // classical monic scheme, Pan's coefficient maps accept the original
  // leading coefficient and therefore need no final scaling multiplication;
  // over ℂ Knuth–Eve emits its own scale line (preserveLeading), while
  // Belaga's monic scheme is scaled here.  Pan over ℂ (compilePanC) routes an
  // all-real input through the real schemes first.
  const numeric = F.complex ? [
    { name: 'Knuth\u2013Eve', fn: compileKnuthEveComplex, preserveLeading: true },
    { name: 'Pan', fn: compilePanC, preserveLeading: true },
    { name: 'Belaga', fn: compileBelaga },
  ] : [
    { name: 'Knuth\u2013Eve', fn: compileKnuthEve },
    { name: 'Pan', fn: compilePan1978Real, preserveLeading: true, need: 'needs numerical real-algebraic preprocessing' },
  ];
  for (const { name, fn, preserveLeading = false, need = 'needs real or complex roots' } of numeric) {
    if (only !== null && name !== only) continue;
    if (needsNumericWorker(mode)) rows.push(numericRow(name, fn, coeffs, F, mode, { preserveLeading, poly }));
    else rows.push({ name, ok: false, note: `${need}: characteristic 0 (\u211a, \u211d, \u2102) only, not ${F.name}` });
  }
  return rows;
}

/** Pan over \u2102: an input whose coefficients are all real tries Pan's real
 *  schemes first (with their conditioning rescales they are more robust than
 *  the complex homotopy on e.g. Taylor / Hermite targets, where the complex
 *  scheme fails to track a branch) and falls back to the complex scheme; the
 *  degree guard keeps the complex scheme's "start at degree 11" message. */
function compilePanC(fl) {
  const n = fl.length - 1;
  if (n >= 11 && fl.every(z => z.im === 0)) {
    try { return compilePan1978Real(fl.map(z => z.re)); } catch (e) { /* fall through to the complex scheme */ }
  }
  return compilePan1978(fl);
}

// A field element as the numeric methods take it: a double over ℚ / ℝ, an
// { re, im } pair of doubles over ℂ (a GaussRat, or a Rat for a real input).
const toDoubles = (r, complex) => {
  if (typeof r === 'number') return complex ? { re: r, im: 0 } : r;
  if (r && r.re !== undefined && r.im !== undefined)       // GaussRat
    return { re: ratToDouble(r.re.n, r.re.d), im: ratToDouble(r.im.n, r.im.d) };
  const v = Number(r.n) / Number(r.d);
  return complex ? { re: v, im: 0 } : v;
};
const finiteDouble = v => (typeof v === 'number' ? Number.isFinite(v) : Number.isFinite(v.re) && Number.isFinite(v.im));
const isOneC = v => (typeof v === 'number' ? v === 1 : v.re === 1 && v.im === 0);
const divC = (a, b) => {
  const d = b.re * b.re + b.im * b.im;
  return { re: (a.re * b.re + a.im * b.im) / d, im: (a.im * b.re - a.re * b.im) / d };
};

// Methods whose preprocessing is numerical: run on floating coefficients.
// The classical schemes are scaled to monic and get one final multiplication;
// Pan's non-monic coefficient map receives the original coefficients instead.
function numericRow(name, compile, coeffs, F, mode = 'Q', { preserveLeading = false, poly = null } = {}) {
  try {
    const cx = !!F.complex;
    let fl = coeffs.map(r => toDoubles(r, cx));
    if (!fl.every(finiteDouble)) throw new Error('coefficients too large for float preprocessing');
    const n = fl.length - 1;
    const lc = fl[n];
    const scaled = n > 0 && !preserveLeading && !isOneC(lc);
    if (scaled) fl = cx ? fl.map(v => divC(v, lc)) : fl.map(v => v / lc);
    const r = compile(fl);
    if (scaled) {
      r.lines[r.lines.length - 1].lhs = 'P\u0303';
      r.lines.push({ lhs: 'P', rhs: `${cx ? complexToken(lc.re, lc.im) : lc} * P\u0303`, mul: true });
      r.mults += 1;
      r.height += 1;                        // the scale line multiplies P\u0303, the former output: one level deeper
      // ℂ: the reported error is that of the displayed chain, scale line included
      if (cx) r.maxRelError = verifyLinesComplex(r.lines, coeffs.map(c => toDoubles(c, true)));
    }
    // a chain with complex constants has C only over ℂ (double complex)
    const complex = r.lines.some(l => hasComplexToken(l.rhs));
    let cText = null;
    if ((!complex || cx) && fieldHasC(mode)) {
      try { cText = methodChainC(r.lines, mode, F, { name, mults: r.mults, preprocessing: 'numeric', poly }); }
      catch (e) { /* math view still available */ }
    }
    return {
      name, ok: true, mults: r.mults, adds: r.adds, height: r.height,
      preprocessing: r.preprocessingLabel ?? (r.preprocessing === 'complex' ? 'complex roots' : 'real roots (numeric)'),
      exact: false,
      mathText: chainToText({ lines: factorize(r.lines) }),
      mathTextOriginal: chainToText(r), cText, cTextFraction: cText,
      graph: graphOf(r.lines),
      ...(r.radixExponent === undefined ? {} : {
        radixShifts: r.radixShifts ?? 0, radixExponent: r.radixExponent,
        inputRadixExponent: r.inputRadixExponent,
        radixAdditionCost: r.radixAdditionCost,
      }),
      note: `${r.note ?? ''} max rel. error ${r.maxRelError.toExponential(1)}`.trim(),
    };
  } catch (e) {
    return { name, ok: false, note: e.message };
  }
}
