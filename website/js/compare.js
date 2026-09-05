// Run the classical methods on the same input; each row carries its full
// chain (mathematical) and generated C.
import { compileHorner } from './methods/horner.js';
import { compileEstrin } from './methods/estrin.js';
import { compileRW } from './methods/rw.js';
import { chainToText, factorize } from './chain.js';
import { methodChainC } from './cgen.js';
import { compileKnuthEve } from './methods/motzkin.js';
import { compilePan1978Real } from './methods/pan1978real.js';
import { buildGraphFromLines } from './graph.js';

const graphOf = lines => { try { return buildGraphFromLines(lines); } catch (e) { return null; } };

const METHODS = [
  ['Horner', compileHorner],
  ['Estrin', compileEstrin],
  ['Rabin–Winograd', compileRW],
];

/** mode: a field id from js/field.js FIELDS ('Q', 'R', 'p61', 'p89', 'p127',
 *  'gf32', 'gf64', 'gf128'); the legacy 'p' (= p89) and 'gf2k' (F.k decides)
 *  are still accepted by the C emitter. */
export function buildComparisons(coeffs, F, mode, { poly = null } = {}) {
  const rows = [];
  const numericField = !!F.real;         // ℝ: preprocessing with doubles is not exact
  for (const [name, fn] of METHODS) {
    try {
      const r = fn(coeffs, F);
      let cText = null, cTextFraction = null;
      const copts = { name, mults: r.mults, preprocessing: r.preprocessing, poly };
      try { cText = methodChainC(r.lines, mode, F, { ...copts, cstyle: 'float' }); }
      catch (e) { /* math view still available */ }
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
  // Every field lists the same methods, so the comparison table keeps
  // its shape.  These algebraic/numeric preprocessors run in characteristic
  // zero only and are reported (not silently dropped) elsewhere.  Unlike the
  // classical monic scheme, Pan's coefficient map accepts the original
  // leading coefficient and therefore needs no final scaling multiplication.
  const numeric = [
    { name: 'Knuth\u2013Eve', fn: compileKnuthEve },
    { name: 'Pan', fn: compilePan1978Real, preserveLeading: true, need: 'needs numerical real-algebraic preprocessing' },
  ];
  for (const { name, fn, preserveLeading = false, need = 'needs real or complex roots' } of numeric) {
    if (mode === 'Q' || mode === 'R') rows.push(numericRow(name, fn, coeffs, F, mode, { preserveLeading, poly }));
    else rows.push({ name, ok: false, note: `${need}: characteristic 0 (\u211a, \u211d) only, not ${F.name}` });
  }
  return rows;
}

// Methods whose preprocessing is numerical: run on floating coefficients.
// The classical schemes are scaled to monic and get one final multiplication;
// Pan's non-monic coefficient map receives the original coefficients instead.
function numericRow(name, compile, coeffs, F, mode = 'Q', { preserveLeading = false, poly = null } = {}) {
  try {
    let fl = coeffs.map(r => (typeof r === 'number' ? r : Number(r.n) / Number(r.d)));
    if (!fl.every(Number.isFinite)) throw new Error('coefficients too large for float preprocessing');
    const n = fl.length - 1;
    const lc = fl[n];
    const scaled = n > 0 && !preserveLeading && lc !== 1;
    if (scaled) fl = fl.map(v => v / lc);
    const r = compile(fl);
    if (scaled) {
      r.lines[r.lines.length - 1].lhs = 'P\u0303';
      r.lines.push({ lhs: 'P', rhs: `${lc} * P\u0303`, mul: true });
      r.mults += 1;
    }
    const complex = r.lines.some(l => /\di\)/.test(l.rhs));
    let cText = null;
    if (!complex) {
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
