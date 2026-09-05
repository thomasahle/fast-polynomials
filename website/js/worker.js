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
import { parsePoly, polyToString } from './polyparse.js';
import { resolveField } from './field.js';
import { compileChar2 } from './compile2.js';
import { compileChar0 } from './compile0.js';
import { chainToText } from './chain.js';
import { buildComparisons, buildClassical, buildNumeric, needsNumericWorker, pendingNumericRows, NUMERIC_METHODS } from './compare.js';
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

/** Run one compile request; returns the result object (throws on hard failure).
 *  part: 'main' — our chain and the classical methods, with placeholder rows
 *        for the numeric methods when those run in their own worker;
 *        'numeric' — just the numeric methods' rows ({ comparisons }; `only`
 *        names one of them: the browser worker reports each as it finishes);
 *        omitted — everything in one result (tests, and any single-worker use). */
export async function handleMessage({ lane, src, fieldMode, part = null, only = null }) {
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
  let polyText = null;                            // the input, canonically printed, for the C headers
  const comparisonsFor = () => {
    const opts = { poly: polyText };
    if (part === 'main')
      return [...buildClassical(cmpCoeffs, F, cmpMode, opts),
              ...(needsNumericWorker(cmpMode) ? pendingNumericRows() : buildNumeric(cmpCoeffs, F, cmpMode, opts))];
    return buildComparisons(cmpCoeffs, F, cmpMode, opts);
  };
  if (part === 'numeric') {
    const { coeffs } = parse();
    polyText = polyToString(coeffs, { char2: fd.lane === 'char2' });
    cmpCoeffs = fd.lane === 'char2' ? coeffs.map(c => F.fromInt(c)) : coeffs.map(c => F.fromRat(c));
    return { comparisons: withGraphViews(buildNumeric(cmpCoeffs, F, cmpMode, { poly: polyText, only })) };
  }
  if (fd.lane === 'char2') {
    const { coeffs } = parse();
    polyText = polyToString(coeffs, { char2: true });
    cmpCoeffs = coeffs.map(c => F.fromInt(c));
    r = compileChar2(cmpCoeffs, F);
  } else {
    const { coeffs } = parse();
    polyText = polyToString(coeffs);
    cmpCoeffs = coeffs.map(c => F.fromRat(c));      // exact Rats over ℚ and ℝ; residues over GF(p)
    try {
      r = await compileChar0(src, fd.id);
    } catch (err) {
      // our compiler unavailable/failed: still deliver the classical methods
      let comparisons = [];
      try { comparisons = withGraphViews(comparisonsFor()); } catch (e2) {}
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
  try { comparisons = withGraphViews(comparisonsFor()); } catch (err) { /* table optional */ }
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
    const { id, part = null } = e.data;
    if (part === 'numeric') {
      // one reply per method, as soon as it is done (Knuth–Eve is quick; Pan may take a while)
      for (const only of NUMERIC_METHODS) {
        try {
          const result = await handleMessage({ ...e.data, only });
          postMessage({ id, part, ok: true, result });
        } catch (err) {
          postMessage({ id, part, ok: true, result: { comparisons: [{ name: only, ok: false, note: err?.message ?? String(err) }] } });
        }
      }
      return;
    }
    try {
      const result = await handleMessage(e.data);
      postMessage({ id, part, ok: true, result });
    } catch (err) {
      postMessage({ id, part, ok: false, message: err?.message ?? String(err) });
    }
  };
}
