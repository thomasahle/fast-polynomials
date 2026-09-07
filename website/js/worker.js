// Compilation worker: keeps unbounded exact-rational preprocessing off the UI thread.
//
// Message: { id, lane: 'char2' | 'char0', src, fieldMode }
//   fieldMode is a field id from js/field.js FIELDS:
//     char0 lane: 'Q' (exact rationals), 'R' (the same exact preprocessing with
//                 the constants shown and emitted as doubles, ≈ numeric),
//                 'C' (exact over the Gaussian rationals ℚ(i), constants shown
//                 as complex doubles, ≈ numeric),
//                 'p61' | 'p89' | 'p127' (Mersenne primes 2^k − 1)
//     char2 lane: 'gf32' | 'gf64' | 'gf128'
//   Legacy spellings still resolve: 'p' → 'p89'; a null fieldMode → 'gf64'
//   (char2) or 'Q' (char0).
// Reply: { id, ok: true, result } | { id, ok: false, message }
//
// Input validation (one readable page error each, before any compiler runs):
//   - the parser's own errors, prefixed "cannot read the polynomial over <field>: …"
//     (this also covers a GF(2^k) literal wider than k bits, a GF(p) denominator
//     that is 0 mod p, and exponents above polyparse.js MAX_PARSE_DEGREE)
//   - over GF(p) a leading coefficient that vanishes mod p lowers the degree
//   - a constant (degree 0) is rejected in every lane
//   - the char-0 lane rejects degrees above DEGREE_CEILING[field] (the char-2
//     lane's cap is compile2.js / char2.js MAX_DEGREE)
//
// handleMessage(data) is exported so the node smoke test can drive the same
// code path without a browser; the result is plain JSON (structured-clone
// safe: strings, numbers, booleans, null, arrays, plain objects only).
import { parsePoly, polyToString } from './polyparse.js';
import { DEGREE_CEILING } from './methodlist.js';
import { resolveField, echo } from './field.js';
import { compileChar2 } from './compile2.js';
import { compileChar0 } from './compile0.js';
import { chainToText } from './chain.js';
import { buildComparisons, buildClassical, buildNumeric, needsNumericWorker, pendingNumericRows, numericMethodsFor } from './compare.js';
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

/** Largest degree the char-0 lane accepts per field (the char-2 lane's cap is
 *  char2.js MAX_DEGREE).  Over ℚ/ℝ/ℂ the exact decoder's constants grow so fast
 *  that degree 39 already runs for minutes; over the Mersenne primes it is a
 *  second or two at 200 and growing quickly. */
// (defined in methodlist.js so the page thread can show the same numbers)
export { DEGREE_CEILING };

const MERSENNE_NAMES = 'GF(2^61−1), GF(2^89−1) and GF(2^127−1)';
/** The Mersenne fields are worth naming only for a degree they themselves accept,
 *  and near their own cap they take about a minute, not "seconds". */
function degreeCeilingMessage(fd, n) {
  const cap = DEGREE_CEILING[fd.id];
  const lower = 'split the polynomial, or lower the degree';
  return fd.char === 'p'
    ? `over ${fd.name} this page compiles degrees 1–${cap} (you entered degree ${n}): ` +
      `higher degrees would take minutes of exact preprocessing — ${lower}`
    : `over ${fd.name} this page compiles degrees 1–${cap} (you entered degree ${n}): ` +
      `exact preprocessing above degree ${cap} can take minutes — ` +
      (n <= DEGREE_CEILING.p61
        ? `the Mersenne-prime fields ${MERSENNE_NAMES} take this polynomial much further ` +
          `(degrees up to ${DEGREE_CEILING.p61}; about a minute near the cap)`
        : lower);
}

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
  let r;
  const cmpMode = fd.id;
  const char2 = fd.lane === 'char2';
  // Read the input and move it into the field.  A failure names the field it
  // was read in (the text may have been typed for another one, e.g. a
  // fractional Taylor polynomial switched to GF(2^k), or a GF(2^64) key kept
  // across a switch to GF(2^32)).  Returns
  //   coeffs     the parsed coefficients (Rat / GaussRat / BigInt bit patterns)
  //   cmpCoeffs  the same as field elements (residues over GF(p)), and both
  //              trimmed when a leading coefficient vanishes in the field
  //   polyText   the input, canonically printed, for the C headers
  //   srcText    the input for compileChar0 (which re-reads it): src itself
  //              unless the trim above changed the degree
  const parse = () => {
    try {
      let { coeffs } = parsePoly(src, { char2, complex: !!fd.complex });   // ℂ: every coefficient a GaussRat
      let cmpCoeffs;
      if (char2) {
        const wide = coeffs.find(c => c >= (1n << BigInt(fd.k)));
        if (wide !== undefined)
          throw new Error(`${fd.name} elements are at most ${fd.k} bits, but 0x${echo(wide.toString(16))} has ${wide.toString(2).length} ` +
            '— choose a wider field or shorten the constant');
        cmpCoeffs = coeffs.map(c => F.fromInt(c));
      } else {
        cmpCoeffs = coeffs.map(c => F.fromRat(c));   // exact Rats over ℚ and ℝ, GaussRats over ℂ; residues over GF(p)
      }
      // GF(p): a leading coefficient that is a multiple of p is 0 in the field —
      // drop it (and any below it) so the degree is the polynomial's true degree
      let d = cmpCoeffs.length - 1;
      while (d > 0 && F.isZero(cmpCoeffs[d])) d--;
      const trimmed = d < cmpCoeffs.length - 1;
      if (trimmed) { coeffs = coeffs.slice(0, d + 1); cmpCoeffs = cmpCoeffs.slice(0, d + 1); }
      const polyText = polyToString(coeffs, { char2 });
      return { coeffs, cmpCoeffs, degree: d, polyText, srcText: trimmed ? polyText : src };
    } catch (e) { throw new Error(`cannot read the polynomial over ${fd.name}: ${e?.message ?? e}`); }
  };
  const { cmpCoeffs, degree: n, polyText, srcText } = parse();
  // a constant has nothing to compile (and the classical rows would show raw
  // arithmetic failures for it); the same page error in every lane
  if (n < 1) throw new Error('a constant needs no multiplications — enter a polynomial of degree ≥ 1');
  if (!char2 && n > (DEGREE_CEILING[fd.id] ?? Infinity)) throw new Error(degreeCeilingMessage(fd, n));
  const comparisonsFor = () => {
    const opts = { poly: polyText };
    if (part === 'main')
      return [...buildClassical(cmpCoeffs, F, cmpMode, opts),
              ...(needsNumericWorker(cmpMode) ? pendingNumericRows(cmpMode) : buildNumeric(cmpCoeffs, F, cmpMode, opts))];
    return buildComparisons(cmpCoeffs, F, cmpMode, opts);
  };
  if (part === 'numeric')
    return { comparisons: withGraphViews(buildNumeric(cmpCoeffs, F, cmpMode, { poly: polyText, only })) };
  if (char2) {
    r = compileChar2(cmpCoeffs, F);
  } else {
    try {
      r = await compileChar0(srcText, fd.id);
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
    ...(r.cMissing ? { cMissing: r.cMissing } : {}),
    comparisons,
  };
}

/** The numeric part: one reply per method, as soon as it is done (Knuth–Eve is
 *  quick; Pan may take a while).  `post` receives { id, part, ok: true, result }
 *  once per method of numericMethodsFor(field) — a method that throws yields
 *  its failed row instead — or a single { id, part, ok: false, message } when
 *  the field itself cannot be resolved (the worker's only reply then).
 *  Exported so the node smoke test can drive the browser loop. */
export async function replyNumeric(data, post) {
  const { id, part = 'numeric' } = data;
  let methods;
  try { methods = numericMethodsFor(resolveField(data.lane, data.fieldMode).id); }
  catch (err) { post({ id, part, ok: false, message: err?.message ?? String(err) }); return; }
  for (const only of methods) {
    try {
      const result = await handleMessage({ ...data, only });
      post({ id, part, ok: true, result });
    } catch (err) {
      post({ id, part, ok: true, result: { comparisons: [{ name: only, ok: false, note: err?.message ?? String(err) }] } });
    }
  }
}

// Browser worker entry point (absent under node, where the smoke test imports handleMessage).
if (typeof globalThis.postMessage === 'function') {
  globalThis.onmessage = async e => {
    const { id, part = null } = e.data;
    if (part === 'numeric') return replyNumeric(e.data, m => postMessage(m));
    try {
      const result = await handleMessage(e.data);
      postMessage({ id, part, ok: true, result });
    } catch (err) {
      postMessage({ id, part, ok: false, message: err?.message ?? String(err) });
    }
  };
}
