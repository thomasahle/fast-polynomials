// Compilation worker: keeps unbounded exact-rational preprocessing off the UI thread.
//
// Message: { id, lane: 'char2' | 'char0', src, fieldMode }
//   fieldMode is a field id from js/field.js FIELDS:
//     char0 lane: 'Q' (exact rationals), 'R' (the same exact preprocessing with
//                 the constants shown and emitted as doubles, ≈ numeric),
//                 'p61' | 'p89' | 'p127' (Mersenne primes 2^k − 1)
//     char2 lane: 'gf32' | 'gf64' | 'gf128'
//   Legacy spellings still resolve: 'p' → 'p89'; a null fieldMode → 'gf64'
//   (char2) or 'Q' (char0).
// Reply: { id, ok: true, result } | { id, ok: false, message }
//
// handleMessage(data) is exported so the node smoke test can drive the same
// code path without a browser; the result is plain JSON (structured-clone
// safe: strings, numbers, booleans, null, arrays, plain objects only).
import { parsePoly } from './polyparse.js';
import { resolveField } from './field.js';
import { compileChar2 } from './compile2.js';
import { compileChar0 } from './compile0.js';
import { chainToText } from './chain.js';
import { buildComparisons } from './compare.js';
import { renderGraphSVG, graphToText } from './graphview.js';

/** Graph IR → the three graph payloads (IR, SVG string, text listing); null-safe. */
export function graphViews(graph) {
  if (!graph) return { graph: null, graphSvg: null, graphText: null };
  let graphSvg = null, graphText = null;
  try { graphSvg = renderGraphSVG(graph); } catch (e) { /* IR still shipped */ }
  try { graphText = graphToText(graph); } catch (e) { /* optional */ }
  return { graph, graphSvg, graphText };
}

/** Comparison rows: render each row's graph IR (rows without a chain get null views). */
const withGraphViews = rows => rows.map(c => ({ ...c, ...graphViews(c.graph ?? null) }));

/** Run one compile request; returns the result object (throws on hard failure). */
export async function handleMessage({ lane, src, fieldMode }) {
  const fd = resolveField(lane, fieldMode);
  const F = fd.make();
  const fieldInfo = { fieldId: fd.id, fieldName: fd.name, status: fd.status, exact: fd.exact, cCode: fd.cCode };
  let r, cmpCoeffs;
  const cmpMode = fd.id;
  // a parse failure names the field it was read in (the text may have been typed
  // for another one, e.g. a fractional Taylor polynomial switched to GF(2^k))
  const parse = () => {
    try { return parsePoly(src, { char2: fd.lane === 'char2' }); }
    catch (e) { throw new Error(`cannot read the polynomial over ${fd.name}: ${e?.message ?? e}`); }
  };
  if (fd.lane === 'char2') {
    const { coeffs } = parse();
    cmpCoeffs = coeffs.map(c => F.fromInt(c));
    r = compileChar2(cmpCoeffs, F);
  } else {
    const { coeffs } = parse();
    cmpCoeffs = coeffs.map(c => F.fromRat(c));      // exact Rats over ℚ and ℝ; residues over GF(p)
    try {
      r = await compileChar0(src, fd.id);
    } catch (err) {
      // our compiler unavailable/failed: still deliver the classical methods
      let comparisons = [];
      try { comparisons = withGraphViews(buildComparisons(cmpCoeffs, F, cmpMode)); } catch (e2) {}
      if (!comparisons.some(c => c.ok)) throw err;
      return {
        oursFailed: err?.message ?? String(err),
        mathText: null, mathTextOriginal: null, cText: null, cTextFraction: null,
        graph: null, graphSvg: null, graphText: null,
        mults: null, adds: null, height: null,
        ...fieldInfo, note: '', comparisons,
      };
    }
  }
  let comparisons = [];
  try { comparisons = withGraphViews(buildComparisons(cmpCoeffs, F, cmpMode)); } catch (err) { /* table optional */ }
  return {
    mathText: r.mathText ?? chainToText(r), mathTextOriginal: r.mathTextOriginal ?? null,
    cText: r.cText ?? null, cTextFraction: r.cTextFraction ?? null,
    ...graphViews(r.graph ?? null),
    mults: r.mults, hornerMults: r.hornerMults, adds: r.adds,
    height: r.height, ...fieldInfo, fieldName: r.field.name, note: r.note ?? '',
    maxRelError: r.maxRelError ?? null,
    comparisons,
  };
}

// Browser worker entry point (absent under node, where the smoke test imports handleMessage).
if (typeof globalThis.postMessage === 'function') {
  globalThis.onmessage = async e => {
    const { id } = e.data;
    try {
      const result = await handleMessage(e.data);
      postMessage({ id, ok: true, result });
    } catch (err) {
      postMessage({ id, ok: false, message: err?.message ?? String(err) });
    }
  };
}
