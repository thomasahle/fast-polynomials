// The names of the comparison methods and the per-field degree caps — the only
// facts about the compiler the page thread needs before a worker replies.
// Dependency-free on purpose: js/ui.js and js/uistate.js import it directly, so
// the page never loads js/methods/*, js/graph.js or js/char2.js (the compilers
// run in the workers); js/compare.js and js/char2.js re-export everything here
// so their existing importers keep working.
//
// The classical rows (Horner, Estrin, Rabin–Winograd) run in the main worker
// with the paper's chain; the numeric rows (Knuth–Eve, Pan; plus Belaga over ℂ)
// run in their own worker over ℚ / ℝ / ℂ, since their root-finding
// preprocessing can take seconds at high degree.  Over every other field they
// are listed and rejected at once (the table keeps its shape), so no second
// worker is needed there.  compare.js's implementation tables are keyed by
// these names, so a method cannot exist in one place and not the other.

/** The exact classical methods, in table order. */
export const CLASSICAL_METHODS = ['Horner', 'Estrin', 'Rabin–Winograd'];

/** The numeric methods over ℚ / ℝ (and the ones every other field lists as rejected). */
export const NUMERIC_METHODS = ['Knuth–Eve', 'Pan'];
/** Over ℂ Belaga's scheme joins them. */
export const NUMERIC_METHODS_C = [...NUMERIC_METHODS, 'Belaga'];

/** Numeric method names for a field id ('C' adds Belaga). */
export const numericMethodsFor = mode => (mode === 'C' ? NUMERIC_METHODS_C : NUMERIC_METHODS);

/** Fields whose numeric rows actually run — in the second worker. */
export const needsNumericWorker = mode => mode === 'Q' || mode === 'R' || mode === 'C';

/** Rows standing in for the numeric methods until their worker replies. */
export const pendingNumericRows = (mode = 'Q') =>
  numericMethodsFor(mode).map(name => ({ name, ok: false, pending: true, note: 'computing the numerical preprocessing…' }));

/** Every method a result over `mode` can show, 'ours' first (the comparison
 *  table's order): the classical rows, then the numeric ones where they run. */
export const methodNamesFor = mode =>
  ['ours', ...CLASSICAL_METHODS, ...(needsNumericWorker(mode) ? numericMethodsFor(mode) : [])];

/** The largest degree the characteristic-2 lane compiles (js/char2.js
 *  SUPPORTED_DEGREES is 1..MAX_DEGREE; 27 is the paper's open frontier).  Also
 *  the degree beyond which exact preprocessing over ℚ / ℝ / ℂ turns slow. */
export const MAX_DEGREE = 26;

/** The largest degree the char-0 lane accepts per field: exact preprocessing over
 *  ℚ / ℝ / ℂ takes minutes beyond 38; the Mersenne fields stay fast much further. */
/** A measured double-rounding error above this is flagged (table cell, C header remark, notes). */
export const REL_ERROR_WARN = 1e-6;

export const DEGREE_CEILING = { Q: 38, R: 38, C: 38, p61: 255, p89: 255, p127: 255 };
