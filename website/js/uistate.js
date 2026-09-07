// Pure UI state for the page: one state object, a reducer, and the selectors
// every piece of the UI is derived from.  No DOM, no worker — ui.js owns the
// side effects (posting to / terminating the worker) and renders whatever the
// selectors say, so the controls can never disagree with each other.
//
//   state = { mode, src, exDegree, exKey, exSeed, exMonic, busy, jobId, error, result,
//             prevResult, lateNumeric, cancelled, method, view, form, cstyle, numfmt }
//     mode      a field id from the js/field.js registry ('Q', 'R', 'C', 'p61', 'p89',
//               'p127', 'gf32', 'gf64', 'gf128'): which field the input is read in
//     src       textarea contents
//     exDegree  degree the example chips generate at (clamped per field when used)
//     exKey     key of the generated example the textarea currently holds, or null
//               once the user edits the text (the degree stepper only regenerates
//               while exKey still matches the current contents)
//     exSeed    reseed counter of the 'random key' chip (every click draws a fresh key;
//               the same seed reproduces the same key, so Share links round-trip)
//     exMonic   whether generated examples are normalized to leading coefficient 1
//     busy      a compile job is in flight (ui.js shows a Cancel button meanwhile)
//     jobId     id of the newest job; replies carrying any other id are stale
//     error     message string | null — a failed compile keeps the last result
//               mounted under the error (ui.js dims it), so the page never collapses
//               while a draft is being typed
//     result    the worker's result object | null (null hides the output)
//     prevResult the result shown before the current one, kept only while the
//               current one still has numeric rows pending: the selected method's
//               previous chain stays mounted (dimmed) until its worker replies
//               (staleRow); null once every row is in
//     lateNumeric numeric-method rows that arrived before their job's main reply
//     cancelled the last job was cancelled: whatever output is mounted is not the
//               chain of the current input (ui.js dims it and says so) until the
//               next job starts
//     method    'ours' | a comparison row name (which chain the output shows)
//     view      'math' | 'c' | 'graph'
//     form      'factor' | 'original'  math view: factored gate list or the method's own form
//     cstyle    'float' | 'fraction'   C view over ℚ: constant rendering
//     numfmt    'exact' | 'decimal'    math view: constants as produced, or readable
//                                      (≈6 significant digits over ℚ/ℝ/ℂ, hex over GF(2^k));
//                                      display only — counts stay on the exact text
//
// Actions (reduce(state, action) → state; unknown/no-op actions return `state` itself):
//   { type: 'setMode', mode }        clears output + error and immediately starts a job
//                                    for the current source in the new mode (superseding
//                                    any running job); no job when the source is blank
//   { type: 'setSrc', src }          also clears exKey (ui.js debounces the recompile)
//   { type: 'compile' }              starts job jobId+1 (clears output + error);
//                                    no-op when the source is blank
//   { type: 'example', key }         regenerates that example at exDegree + compiles
//                                    (a reseeding chip such as 'random' bumps exSeed first)
//   { type: 'setExDegree', delta | degree }   steps/sets the example degree (clamped per
//                                    field); when the textarea still holds the generated
//                                    example, regenerates it at the new degree + compiles
//   { type: 'setExMonic', value? }   sets/toggles monic example generation; regenerates
//                                    only when the textarea still holds an example
//   { type: 'cancel' }               busy → false and the job id is retired (jobId + 1); the
//                                    abandoned job's replies (main and per-method numeric) are
//                                    then stale by id, and ui.js's job effect terminates the workers;
//                                    the kept result is flagged `cancelled` (stale) and any of its
//                                    numeric rows still pending are settled as not computed (their
//                                    worker went with the superseded job)
//   { type: 'restore', hash, compact }   rebuilds the state from a URL hash (a hashchange after
//                                    boot): stateFromHash over the layout's boot state, the job
//                                    id retired past the current one, and a job started when
//                                    the source is non-blank
//   { type: 'reply', id, ok, result | message }   worker reply (ignored unless id === jobId and busy);
//                                    a failed main reply keeps the last result, sets `error` and
//                                    retires the job id (its numeric replies are then stale)
//   { type: 'workerError', message } as a failed reply
//   { type: 'setMethod', method }    ignored unless that method has an ok chain in `result`
//   { type: 'setView', view }
//   { type: 'setForm', form } / { type: 'setCstyle', cstyle } / { type: 'setNumfmt', numfmt }
//   { type: 'setSubOption', key }    routed to the strip showing that key
import { Rat } from './rat.js';
import { REAL_SRC, MAX_PARSE_DEGREE } from './polyparse.js';
import { DEGREE_CEILING } from './methodlist.js';
import { GaussRat } from './gauss.js';
import { countOps, formatConstants } from './chain.js';
import { FIELDS, FIELD_GROUPS, gfLiteral } from './field.js';
import { referenceFor } from './references.js';
// the method names and degree caps come from the dependency-free methodlist.js,
// so the page thread never loads the compilers (they run in the workers)
import { numericMethodsFor, needsNumericWorker, methodNamesFor, MAX_DEGREE } from './methodlist.js';

export const VIEWS = ['math', 'c', 'graph'];
export const FORMS = ['factor', 'original'];
export const CSTYLES = ['float', 'fraction'];
export const NUMFMTS = ['exact', 'decimal'];

// ---- field registry --------------------------------------------------------
// The field chooser is rendered from js/field.js FIELDS: one entry per field,
// grouped by FIELD_GROUPS (in that order).  A field's `id` is the value
// state.mode holds; its `worker` descriptor is what compileMessage sends.  A
// registry entry without a worker descriptor would be listed but disabled
// ("coming soon"); today every entry compiles.
export { FIELDS, FIELD_GROUPS };

/** Worker message fields per mode ({ lane, fieldMode }), from the registry. */
export const MODE_MSG = Object.fromEntries(FIELDS.filter(f => f.worker).map(f => [f.id, f.worker]));

/** The selectable field ids (registry order), i.e. the fields the pipeline compiles for. */
export const MODES = FIELDS.filter(f => f.worker).map(f => f.id);

/** Mode ids of earlier Share links, still accepted by stateFromHash. */
export const LEGACY_MODES = { char0: 'Q', mersenne: 'p89', char2: 'gf64' };

const fieldOf = mode => FIELDS.find(f => f.id === mode) ?? null;
/** The char-0 fields whose chain constants are doubles (ℝ) or complex doubles (ℂ):
 *  exact preprocessing, ≈ numeric rendering. */
const inexactChar0 = f => !!f && f.char === 0 && f.exact === false;
const PAPER_FIELDS = ['p89', 'gf64'];

/** Tooltip of a registry field in the chooser. */
export function fieldTitle(f) {
  const kind = f.id === 'Q' ? 'exact rationals (BigInt arithmetic)'
    : f.id === 'R' ? 'the same exact rational preprocessing as ℚ, with the chain constants shown and emitted as doubles (reported as ≈ numeric)'
    : f.complex ? 'the same exact preprocessing over the Gaussian rationals ℚ(i), with the chain constants shown as complex doubles (reported as ≈ numeric)'
    : f.char === 'p' ? `Mersenne prime field, ${f.bits}-bit residues`
    : `carry-less binary field, ${f.bits}-bit`;
  return `${f.name}: ${kind}${PAPER_FIELDS.includes(f.id) ? ", as in the paper's experiments" : ''}`;
}

/**
 * The field chooser, one entry per group (empty groups omitted):
 *   [{ id, label, title, fields: [{ id, label, labelHtml, name, title, enabled, on }] }]
 * Exactly one field is `on` (state.mode); fields without a worker descriptor
 * are disabled with the title 'coming soon'.  `label` uses Unicode superscripts
 * (GF(2⁶⁴)) and `name` the ^k spelling (GF(2^64)); ui.js typesets either.
 */
export function fieldChooser(state) {
  return FIELD_GROUPS.map(g => ({
    id: g.id, label: g.label, title: g.title ?? '',
    fields: FIELDS.filter(f => f.group === g.id).map(f => {
      const enabled = !!f.worker;
      return { id: f.id, label: f.label, labelHtml: f.labelHtml, name: f.name, enabled, on: f.id === state.mode,
        title: enabled ? fieldTitle(f) : 'coming soon' };
    }),
  })).filter(g => g.fields.length > 0);
}

// ---- input highlighting ----------------------------------------------------
// tokenizePoly(src) → [{ type, text }] with type 'num' (integers, fractions,
// decimals, hex, and the ℂ literals i / 2i / 1/2i / (a+bi) of js/polyparse.js),
// 'var' (x, x^k), 'op', 'space' or 'text' (anything else, left plain); the
// texts concatenate back to src.  Pure: ui.js paints the tokens behind the
// transparent textarea.
// Sticky regexes matched at the current position (no lookahead window: a
// complex literal with two 17-digit parts is longer than 40 characters).
const POLY_REAL = REAL_SRC;   // the parser's own number grammar, so the highlighter cannot drift from it
const POLY_NUM_RE = new RegExp(
  `(?:\\(-?(?:${POLY_REAL}[+-])?${POLY_REAL}?i\\)` +    // (1+2i), (1/2-3/4i), (2-i), (-i)
  `|\\(-?${POLY_REAL}\\)\\*?i` +                         // (1/2)i, (-1/2)*i
  `|${POLY_REAL}?i|${POLY_REAL})`, 'y');                  // 2i, i, 3, 1/2, 0.25e-3, 0x1f (hex is REAL_SRC's, lowercase 0x only — as the parser reads it)
const POLY_VAR_RE = /[xX](?:\^\d+)?/y;
const POLY_OP_RE = /[+\-*/^]/y;
const POLY_SPACE_RE = /\s+/y;

export function tokenizePoly(src) {
  const toks = [];
  let i = 0;
  const push = (type, text) => {
    const last = toks[toks.length - 1];
    if (last && last.type === type && (type === 'space' || type === 'text')) last.text += text;
    else toks.push({ type, text });
    i += text.length;
  };
  const at = re => { re.lastIndex = i; return re.exec(src); };
  while (i < src.length) {
    let m;
    if ((m = at(POLY_NUM_RE))) push('num', m[0]);
    else if ((m = at(POLY_VAR_RE))) push('var', m[0]);
    else if ((m = at(POLY_OP_RE))) push('op', m[0]);
    else if ((m = at(POLY_SPACE_RE))) push('space', m[0]);
    else push('text', src[i]);
  }
  return toks;
}

// ---- example generators ----------------------------------------------------
// The example chips are pure generators: examplesFor(mode, degree, seed) returns
// [{ key, label, labelTex?, title, src, reseed? }] with the polynomial regenerated
// at the chosen degree (clamped per field). Characteristic 0 (ℚ, ℝ): Taylor
// polynomials whose labels are typeset by KaTeX; ℂ: the e^{ix} series with
// Gaussian coefficients i^k/k!, x^n − 1, e^x and He_n. Hashing fields
// (Mersenne primes, GF(2^k)): a uniformly random key polynomial (a fresh draw per
// click: `reseed`), a sparse and a dense small-coefficient polynomial, and one
// fixed full-width key that is the same on every visit.

/** Degrees the binary-field stepper walks: every degree the char-2 lane
 *  compiles, 1..26 (js/char2.js SUPPORTED_DEGREES — odd degrees by their
 *  circuits, even ones by the x-lift of the degree below; 27 is the open frontier). */
export const CHAR2_EXAMPLE_DEGREES = Array.from({ length: MAX_DEGREE }, (_, i) => i + 1);

/** Per-field degree limits for the example generators, set where the monic
 *  Taylor chips' exact preprocessing is still a short wait (measured with the
 *  real compiler): over ℂ e^{ix} takes ~1.5 s at degree 20 but 3.4–3.8 s on an
 *  idle machine (6–8 s under load) at 22, so ℂ stops at 20; over ℚ e^x takes
 *  ~22 s at degree 23, so ℚ / ℝ stop at 22 — and ℝ / ℂ lose accuracy beyond
 *  that anyway.  Mersenne fields are instant at any size; char 2 compiles
 *  every degree up to 26. */
export const CHAR0_EXAMPLE_MAX = { Q: 22, R: 22, C: 20 };
export function degreeRange(mode) {
  const f = fieldOf(mode);
  if (!f) return null;
  if (f.char === 2) return { set: CHAR2_EXAMPLE_DEGREES };
  return f.char === 'p' ? { min: 3, max: 63 } : { min: 3, max: CHAR0_EXAMPLE_MAX[f.id] ?? 22 };
}

/** Snap a requested degree into the field's range (char 2: up to the next supported degree). */
export function clampDegree(mode, d) {
  const r = degreeRange(mode);
  if (!r || !Number.isFinite(d)) return d;
  d = Math.round(d);
  if (r.set) return r.set.find(v => d <= v) ?? r.set[r.set.length - 1];
  return Math.min(r.max, Math.max(r.min, d));
}

/** The degree the stepper moves to from `d` (dir ±1); clamps at the ends. */
export function stepDegree(mode, d, dir) {
  const r = degreeRange(mode), cur = clampDegree(mode, d);
  if (!r) return cur;
  if (r.set) {
    const i = Math.min(r.set.length - 1, Math.max(0, r.set.indexOf(cur) + (dir > 0 ? 1 : -1)));
    return r.set[i];
  }
  return clampDegree(mode, cur + (dir > 0 ? 1 : -1));
}

/** Terms, highest degree first, → the textarea's source syntax:
 *  [{ d, neg, coef }] with coef the unsigned coefficient text ('' for an elided 1). */
function termsToSrc(terms) {
  const parts = [];
  for (const { d, neg, coef } of terms) {
    const t = coef + (d === 0 ? '' : d === 1 ? 'x' : `x^${d}`);
    parts.push(parts.length === 0 ? (neg ? '-' : '') + t : ` ${neg ? '-' : '+'} ${t}`);
  }
  return parts.join('') || '0';
}

/** Rat coefficient array (index = degree) → the textarea's source syntax. */
function ratPolyToSrc(coeffs) {
  const terms = [];
  for (let d = coeffs.length - 1; d >= 0; d--) {
    const c = coeffs[d];
    if (c.isZero()) continue;
    const neg = c.isNeg(), m = neg ? c.neg() : c;
    terms.push({ d, neg, coef: m.isOne() && d > 0 ? '' : m.toString() });
  }
  return termsToSrc(terms);
}

/** Gaussian-rational (or Rat) coefficient array → source syntax: real
 *  coefficients as over ℚ, non-real ones as (a+bi) — js/polyparse.js's complex
 *  literal, which GaussRat.toString prints (the sign of the leading part is
 *  hoisted: '- (0+1/6i)x^3', '+ (1-2i)x'). */
function gaussPolyToSrc(coeffs) {
  const terms = [];
  for (let d = coeffs.length - 1; d >= 0; d--) {
    const c = GaussRat.of(coeffs[d]);
    if (c.isZero()) continue;
    const neg = c.re.isNeg() || (c.re.isZero() && c.im.isNeg()), m = neg ? c.neg() : c;
    terms.push({ d, neg, coef: m.isOne() && d > 0 ? '' : m.toString() });
  }
  return termsToSrc(terms);
}

/** BigInt coefficient array (index = degree; negatives allowed in char 0) → source
 *  syntax; with `hex`, values above 15 are written 0x… (the parser's convention). */
function bigPolyToSrc(coeffs, { hex = false } = {}) {
  const parts = [];
  for (let d = coeffs.length - 1; d >= 0; d--) {
    const c = coeffs[d];
    if (c === 0n) continue;
    const neg = c < 0n, m = neg ? -c : c;
    const xs = d === 0 ? '' : d === 1 ? 'x' : `x^${d}`;
    const cs = m === 1n && d > 0 ? '' : hex ? gfLiteral(m) : m.toString();
    const sep = cs.startsWith('0x') && xs ? ' ' : '';    // "0xa x^5", not "0xax^5"
    parts.push(parts.length === 0 ? (neg ? '-' : '') + cs + sep + xs : ` ${neg ? '-' : '+'} ${cs}${sep}${xs}`);
  }
  return parts.join('') || '0';
}

/** Taylor coefficients 0..n of the named char-0 series, as exact Rats. */
function seriesCoeffs(key, n) {
  const c = [];
  if (key === 'exp') {                       // 1/k!
    let f = Rat.ONE;
    for (let k = 0; k <= n; k++) { if (k > 0) f = f.div(new Rat(BigInt(k))); c.push(f); }
  } else if (key === 'ln') {                 // (-1)^{k+1}/k, no constant term
    c.push(Rat.ZERO);
    for (let k = 1; k <= n; k++) c.push(new Rat(k % 2 ? 1n : -1n, BigInt(k)));
  } else {                                   // sqrt: binomial(1/2, k)
    let b = Rat.ONE;
    for (let k = 0; k <= n; k++) { if (k > 0) b = b.mul(new Rat(BigInt(3 - 2 * k), BigInt(2 * k))); c.push(b); }
  }
  return c;
}

/** Taylor coefficients 0..n of e^{ix}: i^k/k! as Gaussian rationals (the ℂ chip). */
function expISeriesCoeffs(n) { return expZSeriesCoeffs(GaussRat.I, n); }

/** Taylor coefficients of e^{zx}: z^k / k! (Gaussian rationals for a Gaussian z). */
function expZSeriesCoeffs(z, n) {
  const c = [];
  let f = GaussRat.ONE;
  for (let k = 0; k <= n; k++) { if (k > 0) f = f.mul(z).div(new Rat(BigInt(k))); c.push(f); }
  return c;
}

/** (x + i)^n expanded: binomial(n, k) · i^(n−k) — Gaussian integers, monic, one root at −i. */
function binomialICoeffs(n) {
  const c = [];
  let binom = 1n;
  for (let k = 0; k <= n; k++) {
    if (k > 0) binom = binom * BigInt(n - k + 1) / BigInt(k);
    let p = GaussRat.ONE;
    for (let j = 0; j < n - k; j++) p = p.mul(GaussRat.I);
    c.push(p.mul(new Rat(binom)));
  }
  return c;
}

/** A random polynomial with small Gaussian-integer coefficients (parts in −9..9,
 *  never both zero), reseeded per click; monic when asked. */
function gaussianKeyCoeffs(n, seed, monic) {
  const next = rng('C', 'gauss', n, seed);
  const part = () => (next() % 19) - 9;
  const draw = () => { let a = part(), b = part(); while (a === 0 && b === 0) { a = part(); b = part(); } return new GaussRat(new Rat(BigInt(a)), new Rat(BigInt(b))); };
  const c = Array.from({ length: n + 1 }, draw);
  if (monic) c[n] = GaussRat.ONE;
  return c;
}

/** coeffs (degree < n) with a leading xⁿ added: monic without rescaling. */
function monicSeries(coeffs, n) {
  const out = coeffs.slice(0, n);
  while (out.length < n) out.push(Rat.ZERO);
  out.push(Rat.ONE);
  return out;
}

/** Deterministic 32-bit stream (splitmix-style mixer) seeded on a list of
 *  numbers / strings, so a chip regenerates the same polynomial for the same
 *  (field, kind, degree, seed). */
function rng(...seeds) {
  let s = 0x2545f491;
  const mix = v => { s = Math.imul(s ^ v, 0x9e3779b1) >>> 0; s = (s ^ (s >>> 13)) >>> 0; };
  for (const v of seeds) {
    if (typeof v === 'number') mix(v >>> 0);
    else for (const ch of String(v)) mix(ch.charCodeAt(0));
  }
  return () => {
    s = (s + 0x9e3779b9) >>> 0;
    let z = s;
    z = Math.imul(z ^ (z >>> 16), 0x21f0aaad);
    z = Math.imul(z ^ (z >>> 15), 0x735a2d97);
    return (z ^ (z >>> 15)) >>> 0;
  };
}

/** A uniformly random `bits`-bit BigInt from the stream. */
function randBits(next, bits) {
  let v = 0n;
  for (let b = 0; b < bits; b += 32) v = (v << 32n) | BigInt(next());
  return v & ((1n << BigInt(bits)) - 1n);
}

/** Small nonzero coefficient: ±[1, 20] in char 0, 1..29 (hex above 15) in char 2. */
function smallCoeff(next, f) {
  if (f.char === 2) return BigInt(1 + next() % 29);
  const m = BigInt(1 + next() % 20);
  return next() % 2 ? -m : m;
}

/** Key polynomial: every coefficient a uniformly random field element (full
 *  width), the leading one nonzero — the key of a (degree+1)-independent
 *  polynomial hash.  Seeded on the field, the degree and `seeds`. */
function keySrc(f, n, seeds, monic = false) {
  const next = rng(f.id, 'key', n, ...seeds);
  const draw = () => { const v = randBits(next, f.bits); return f.char === 'p' && v === f.prime ? 0n : v; };
  const cs = Array.from({ length: n + 1 }, draw);
  while (cs[n] === 0n) cs[n] = draw();
  if (monic) cs[n] = 1n;
  return bigPolyToSrc(cs, { hex: f.char === 2 });
}

/** Monic, only a few small lower-degree terms (≈ n/4 of them) plus a constant term. */
function sparseSrc(f, n) {
  const next = rng(String(f.char), 'sparse', n);
  const cs = Array(n + 1).fill(0n);
  cs[n] = 1n;
  cs[0] = smallCoeff(next, f);
  let placed = 0;
  const count = Math.min(n - 1, Math.max(1, Math.floor(n / 4)));
  while (placed < count) {
    const d = 1 + next() % (n - 1);
    if (cs[d] === 0n) { cs[d] = smallCoeff(next, f); placed++; }
  }
  return bigPolyToSrc(cs, { hex: f.char === 2 });
}

/** Monic, every coefficient a small nonzero value. */
function denseSrc(f, n) {
  const next = rng(String(f.char), 'dense', n);
  const cs = Array(n + 1).fill(0n);
  cs[n] = 1n;
  for (let d = n - 1; d >= 0; d--) cs[d] = smallCoeff(next, f);
  return bigPolyToSrc(cs, { hex: f.char === 2 });
}

/** The example chips for a mode, generated at `degree` (clamped) and, for the
 *  reseeding chips, at `seed`: [{ key, label, labelTex?, title, src, reseed? }]. */
export function examplesFor(mode, degree, seed = 0, monic = false) {
  const f = fieldOf(mode);
  if (!f) return [];
  const n = clampDegree(mode, degree);
  // monic: the degree-(n−1) Taylor polynomial plus xⁿ (the series' own
  // coefficients stay recognisable; rescaling to a monic leading term would not)
  const seriesSrc = key => ratPolyToSrc(monic ? monicSeries(seriesCoeffs(key, n - 1), n) : seriesCoeffs(key, n));
  const seriesTitle = fn => monic
    ? `degree-${n - 1} Taylor polynomial of ${fn} plus x^${n} (monic)`
    : `Taylor polynomial of ${fn}, degree ${n}`;
  const hermite = { key: 'hermite', label: `He_${n}`, labelTex: `\\mathrm{He}_{${n}}`,
    title: `the probabilists' Hermite polynomial He_${n} (monic with integer coefficients at every degree)`,
    src: ratPolyToSrc(hermiteCoeffs(n)) };
  // ℂ: every chip has genuinely complex coefficients — the Taylor series of
  // e^{ix} (i^k/k!) and e^{(1+i)x} ((1+i)^k/k!), the expanded binomial (x+i)^n,
  // and a reseeding random polynomial over the Gaussian integers
  if (f.complex) {
    const gaussSeries = z => gaussPolyToSrc(monic ? monicSeries(expZSeriesCoeffs(z, n - 1), n) : expZSeriesCoeffs(z, n));
    return [
      { key: 'expi', label: 'e^{ix}', labelTex: 'e^{ix}', title: `${seriesTitle('eⁱˣ')} — coefficients iᵏ/k!`, src: gaussSeries(GaussRat.I) },
      { key: 'binomi', label: `(x+i)^${n}`, labelTex: `(x+i)^{${n}}`,
        title: `(x + i)^${n} expanded — Gaussian-integer coefficients binomial(${n}, k)·i^(${n}−k), monic, a single root at −i`,
        src: gaussPolyToSrc(binomialICoeffs(n)) },
      { key: 'exp1i', label: 'e^{(1+i)x}', labelTex: 'e^{(1+i)x}', title: `${seriesTitle('e^{(1+i)x}')} — coefficients (1+i)ᵏ/k!`,
        src: gaussSeries(new GaussRat(Rat.ONE, Rat.ONE)) },
      { key: 'gauss', label: 'random ℤ[i]', labelTex: '\\text{random }\\mathbb{Z}[i]', reseed: true,
        title: `${monic ? 'monic ' : ''}random degree-${n} polynomial with small Gaussian-integer coefficients — click again for a fresh one`,
        src: gaussPolyToSrc(gaussianKeyCoeffs(n, seed, monic)) },
    ];
  }
  if (f.char === 0) return [
    { key: 'exp',  label: 'e^x', labelTex: 'e^x', title: seriesTitle('eˣ'), src: seriesSrc('exp') },
    { key: 'ln',   label: 'ln(1+x)', labelTex: '\\ln(1+x)', title: seriesTitle('ln(1+x)'), src: seriesSrc('ln') },
    { key: 'sqrt', label: '√(1+x)', labelTex: '\\sqrt{1+x}', title: seriesTitle('√(1+x)'), src: seriesSrc('sqrt') },
    hermite,
  ];
  const k = n + 1;
  return [
    { key: 'random', label: 'random key', reseed: true,
      title: monic
        ? `monic random degree-${n} polynomial over ${f.name} — click again for fresh lower coefficients`
        : `${k}-independent hashing: a uniformly random key polynomial over ${f.name} ` +
          `(all ${k} coefficients full-width) — click again for a fresh key`,
      src: keySrc(f, n, ['random', seed], monic) },
    { key: 'sparse', label: 'sparse', title: 'monic, only a few small nonzero coefficients',
      src: sparseSrc(f, n) },
    { key: 'dense',  label: 'dense', title: 'monic, every coefficient a small nonzero value',
      src: denseSrc(f, n) },
    { key: 'fixed',  label: 'fixed key',
      title: `a fixed, reproducible ${monic ? 'monic ' : 'full-width key '}polynomial over ${f.name} (the same on every visit)`,
      src: keySrc(f, n, ['fixed'], monic) },
  ];
}

/** Probabilists' Hermite polynomial He_n: He_0 = 1, He_1 = x, He_{n+1} = x·He_n − n·He_{n−1}
 *  (monic, integer coefficients; the desktop's opening example at degree 7). */
function hermiteCoeffs(n) {
  let prev = [1n], cur = [0n, 1n];
  if (n === 0) return prev.map(c => new Rat(c));
  for (let k = 1; k < n; k++) {
    const next = Array(k + 2).fill(0n);
    cur.forEach((c, i) => { next[i + 1] += c; });
    prev.forEach((c, i) => { next[i] -= BigInt(k) * c; });
    [prev, cur] = [cur, next];
  }
  return cur.map(c => new Rat(c));
}

/** The example a mode opens with (the dense polynomial; the first chip in char 0). */
export function defaultExample(mode, degree, seed = 0, monic = false) {
  const exs = examplesFor(mode, degree, seed, monic);
  return exs.find(e => e.key === 'dense') ?? exs[0] ?? null;
}

// The desktop opens on ℚ with He_7: four multiplications against Horner's six,
// and preprocessed constants of at most seven digits (the Taylor chips at
// degree 7 have constants of a hundred digits).  Phones: initialStateFor.
const OPENING = examplesFor('Q', 7, 0, true).find(e => e.key === 'hermite');
export const initialState = Object.freeze({
  mode: 'Q',
  src: OPENING.src,
  exDegree: 7,
  exKey: OPENING.key,
  exSeed: 0,
  exMonic: true,
  busy: false,
  jobId: 0,
  error: null,
  result: null,
  prevResult: null,    // the result before this one, while this one still has numeric rows pending
  lateNumeric: null,   // numeric-method rows that arrived before their job's main reply (one reply per method)
  cancelled: false,    // the last job was cancelled: the mounted output is stale until the next job
  method: 'ours',
  view: 'math',
  form: 'factor',
  cstyle: 'float',
  numfmt: 'exact',
});

/** Boot state per layout.  Phones (`compact`) open on ℚ with the e^x chip at
 *  COMPACT_DEGREE, monic (the degree-4 Taylor polynomial plus x^5): a chain
 *  with small constants that fits a narrow screen; there is no degree stepper
 *  there.  Desktop keeps initialState. */
export const COMPACT_MODE = 'Q';
export const COMPACT_DEGREE = 5;
export function initialStateFor({ compact = false } = {}) {
  if (!compact) return initialState;
  const ex = defaultExample(COMPACT_MODE, COMPACT_DEGREE, initialState.exSeed, true);
  return Object.freeze({ ...initialState, mode: COMPACT_MODE, exDegree: COMPACT_DEGREE, exMonic: true, src: ex.src, exKey: ex.key });
}

// ---- reducer ---------------------------------------------------------------

// Starting a job keeps the last result visible (stale-while-revalidate): the
// output stays mounted and the reply swaps its content in place.  Any numeric
// rows waiting in lateNumeric belong to the job being retired (ui.js terminates
// its workers on the id change), so they are dropped: merged into the new job's
// result they would show the previous polynomial's — or field's — chain.
const startJob = s => ({ ...s, busy: true, jobId: s.jobId + 1, error: null, lateNumeric: null, cancelled: false });

/** Method shown first for a fresh result: ours, or the first ok comparison when ours failed. */
export const defaultMethod = result =>
  result?.oursFailed ? (result.comparisons?.find(r => r.ok)?.name ?? 'ours') : 'ours';

/** Does `result` carry a displayable chain for `method` — or one still
 *  computing in the numeric worker (selectable: the pane then shows a spinner)? */
export function methodAvailable(result, method) {
  if (!result) return false;
  if (method === 'ours') return !result.oursFailed;
  return !!result.comparisons?.some(r => r.name === method && (r.ok || r.pending));
}

/** `result` with the numeric methods' rows filled in from their worker. */
const withNumeric = (result, rows) => ({
  ...result,
  comparisons: (result.comparisons ?? []).map(c => rows.find(r => r.name === c.name) ?? c),
});

/** Is any numeric row of `result` still waiting for its worker? */
export const hasPending = result => !!result?.comparisons?.some(r => r.pending);

/** `result` with its pending numeric rows settled as not computed (`note` says
 *  why): used when a job is retired without a replacement result — Cancel, a
 *  failed compile — since the rows' worker was terminated when that job started
 *  and no reply can fill them any more (a spinner would run forever). */
const settlePending = (result, note) => (!hasPending(result) ? result : {
  ...result,
  comparisons: result.comparisons.map(c => (c.pending ? { name: c.name, ok: false, pending: false, note } : c)),
});

/** Idle without a replacement result: the last result kept mounted with its
 *  orphaned numeric rows settled, no stale fallback, the selected method
 *  re-checked against the settled rows, and the job id retired. */
const retireJob = (state, note, extra) => {
  const result = settlePending(state.result, note);
  return { ...state, busy: false, jobId: state.jobId + 1, lateNumeric: null, prevResult: null, result,
    method: state.result ? (methodAvailable(result, state.method) ? state.method : defaultMethod(result)) : state.method,
    ...extra };
};

/** A failed compile (or a lost worker): idle under the error, the last result
 *  kept mounted, and the job id retired so the job's other replies — the
 *  numeric rows of the polynomial that failed to compile — cannot land on it. */
const failJob = (state, message) =>
  retireJob(state, 'not computed — the input was recompiled before its numerical preprocessing finished', { error: message });

/** Does the textarea still hold the generated example named by exKey (at the
 *  current degree and seed)?  Only then does the degree stepper regenerate it. */
export const exampleHeld = s => !!s.exKey &&
  examplesFor(s.mode, s.exDegree, s.exSeed, s.exMonic).some(e => e.key === s.exKey && e.src === s.src);

export function reduce(state, action) {
  switch (action.type) {
    case 'setMode': {
      if (!MODE_MSG[action.mode]) return state;
      if (action.mode === state.mode) return state;
      // the method tab and view choices are sticky across mode switches; the reply
      // falls back only if the new result lacks the chosen method
      let s = { ...state, mode: action.mode, busy: false, error: null };
      // a held example follows the field: the same chip in the new field when it
      // has one, else the field's default example (custom text is kept as typed,
      // e.g. an integer polynomial moved between fields)
      if (exampleHeld(state)) {
        const exs = examplesFor(s.mode, s.exDegree, s.exSeed, s.exMonic);
        const ex = exs.find(e => e.key === state.exKey) ?? defaultExample(s.mode, s.exDegree, s.exSeed, s.exMonic);
        if (ex) s = { ...s, src: ex.src, exKey: ex.key, exDegree: clampDegree(s.mode, s.exDegree) };
      }
      // recompile in the new mode, keeping the old output visible meanwhile;
      // with nothing to compile there is nothing to show either — and a job
      // that was running is retired (the id change lets ui.js terminate its workers)
      return s.src.trim() ? startJob(s)
        : { ...s, result: null, prevResult: null, lateNumeric: null, cancelled: false,
            jobId: state.busy ? state.jobId + 1 : state.jobId };
    }
    case 'setSrc':
      if (state.src === action.src) return state;
      // an emptied input has nothing to be wrong about: drop a stale parse error
      // (and a cancel notice — there is nothing left to run again)
      return { ...state, src: action.src, exKey: null, ...(action.src.trim() ? {} : { error: null, cancelled: false }) };
    case 'compile':
      return state.src.trim() ? startJob(state) : state;
    case 'example': {
      const ex0 = examplesFor(state.mode, state.exDegree, state.exSeed, state.exMonic).find(e => e.key === action.key);
      if (!ex0) return state;
      // a reseeding chip (random key) draws a fresh polynomial on every click
      const exSeed = ex0.reseed ? state.exSeed + 1 : state.exSeed;
      const ex = exSeed === state.exSeed ? ex0
        : examplesFor(state.mode, state.exDegree, exSeed, state.exMonic).find(e => e.key === action.key);
      return startJob({ ...state, src: ex.src, exKey: ex.key, exSeed });
    }
    case 'setExDegree': {
      const cur = clampDegree(state.mode, state.exDegree);
      const next = action.delta ? stepDegree(state.mode, cur, action.delta)
                                : clampDegree(state.mode, action.degree);
      if (!Number.isInteger(next) || next === cur) return state;
      const s = { ...state, exDegree: next };
      // only when the textarea still holds the generated example does stepping
      // regenerate it at the new degree (and recompile); otherwise it is a setting
      if (!exampleHeld(state)) return s;
      const ex = examplesFor(state.mode, next, state.exSeed, state.exMonic).find(e => e.key === state.exKey);
      return ex ? startJob({ ...s, src: ex.src }) : s;
    }
    case 'setExMonic': {
      const exMonic = action.value === undefined ? !state.exMonic : !!action.value;
      if (exMonic === state.exMonic) return state;
      const held = exampleHeld(state);
      const s = { ...state, exMonic };
      if (!held) return s;
      const ex = examplesFor(state.mode, state.exDegree, state.exSeed, exMonic)
        .find(e => e.key === state.exKey);
      return ex ? startJob({ ...s, src: ex.src }) : s;
    }
    case 'cancel':
      // retiring the id makes every late reply of the cancelled job stale, so a
      // per-method numeric reply cannot be merged into the previous job's result;
      // the kept result no longer answers the input (ui.js dims it: `cancelled`)
      return state.busy
        ? retireJob(state, 'not computed — the compilation was cancelled before its numerical preprocessing finished', { cancelled: true })
        : state;
    case 'restore': {
      // a hashchange after boot: the same state the page would boot with on that
      // hash, under a job id past the current one (a running job's replies are
      // then stale), compiling at once when there is something to compile
      const fresh = { ...stateFromHash(initialStateFor({ compact: !!action.compact }), action.hash), jobId: state.jobId };
      return fresh.src.trim() ? startJob(fresh) : { ...fresh, jobId: state.jobId + 1 };
    }
    case 'reply': {
      if (action.id !== state.jobId) return state;                  // stale
      if (action.part === 'numeric') {
        // the numeric methods' rows from their own worker fill the placeholders
        // of this job's result; arriving first, they wait for the main reply
        const rows = action.ok ? action.result.comparisons
          : numericMethodsFor(state.mode).map(name => ({ name, ok: false, note: action.message ?? 'numerical preprocessing failed' }));
        if (state.busy) return { ...state, lateNumeric: [...(state.lateNumeric ?? []), ...rows] };
        if (!state.result) return state;
        const result = withNumeric(state.result, rows);
        // a method selected while pending that turned out unavailable is deselected
        // (the chip row, the table and the pane would otherwise disagree)
        return { ...state, result, prevResult: hasPending(result) ? state.prevResult : null,
          method: methodAvailable(result, state.method) ? state.method : defaultMethod(result) };
      }
      if (!state.busy) return state;                                // cancelled
      if (!action.ok) return failJob(state, action.message ?? 'compilation failed');
      const result = state.lateNumeric ? withNumeric(action.result, state.lateNumeric) : action.result;
      // while numeric rows are still pending the previous result stays around, so
      // a selected numeric method keeps showing its last chain (dimmed) meanwhile —
      // the newest result whose rows actually landed: a previous result whose own
      // numeric rows never arrived (its worker went with a superseding job) has no
      // chain to fall back on, so the one before it is carried forward
      return { ...state, busy: false, error: null, result, lateNumeric: null,
        prevResult: hasPending(result) ? (hasPending(state.result) && state.prevResult ? state.prevResult : state.result) : null,
        method: methodAvailable(result, state.method) ? state.method : defaultMethod(result) };
    }
    case 'workerError':
      return failJob(state, action.message ?? 'worker failed');
    case 'setMethod':
      if (action.method === state.method || !methodAvailable(state.result, action.method)) return state;
      return { ...state, method: action.method };
    case 'setView':
      if (!VIEWS.includes(action.view) || action.view === state.view) return state;
      return { ...state, view: action.view };
    case 'setForm':
      if (!FORMS.includes(action.form) || action.form === state.form) return state;
      return { ...state, form: action.form };
    case 'setCstyle':
      if (!CSTYLES.includes(action.cstyle) || action.cstyle === state.cstyle) return state;
      return { ...state, cstyle: action.cstyle };
    case 'setNumfmt':
      if (!NUMFMTS.includes(action.numfmt) || action.numfmt === state.numfmt) return state;
      return { ...state, numfmt: action.numfmt };
    case 'setSubOption': {                      // routed to the strip that shows the key
      const strip = subOptionStrips(state).find(st => st.options.some(o => o.key === action.key && o.enabled));
      if (!strip) return state;
      return strip.kind === 'form' ? reduce(state, { type: 'setForm', form: action.key })
        : strip.kind === 'constants' ? reduce(state, { type: 'setCstyle', cstyle: action.key })
        : reduce(state, { type: 'setNumfmt', numfmt: action.key });
    }
    default:
      return state;
  }
}

// ---- selectors -------------------------------------------------------------

export const showOutput = state => state.result !== null;

/** Degrees beyond which the exact char-0 preprocessing turns slow (minutes at
 *  27–28 and 31, tens of seconds at 40): the same cap the char-2 lane has. */
export const SLOW_DEGREE = MAX_DEGREE;

/** A cheap estimate of the degree of typed input: the largest exponent written
 *  as x^k / x**k (a bare x counts as 1); null when no x appears.  Always a
 *  finite integer: an exponent too long to be a safe integer counts as one past
 *  MAX_PARSE_DEGREE (above every cap, like the parser's own rejection). */
export function estimatedDegree(src) {
  let d = null;
  for (const m of String(src ?? '').matchAll(/[xX](?:\s*(?:\^|\*\*)\s*(\d+))?/g)) {
    const k = m[1] === undefined ? 1 : Number(m[1]);
    d = Math.max(d ?? 0, Number.isSafeInteger(k) ? k : MAX_PARSE_DEGREE + 1);
  }
  return d;
}

/** A one-line warning to show under the input before compiling, or null:
 *  typed (non-chip) text over ℚ / ℝ / ℂ whose degree lies in the slow band
 *  above SLOW_DEGREE and up to the field's DEGREE_CEILING — where the exact
 *  preprocessing really runs for minutes.  Degrees above the ceiling are
 *  refused at once (the error line says so; a hint promising a long compile
 *  would contradict it), and the chips stop at 20–22, so a held example never
 *  triggers it. */
export function inputHint(state) {
  const f = fieldOf(state.mode);
  if (!f || f.char !== 0) return null;
  if (state.exKey && exampleHeld(state)) return null;
  const d = estimatedDegree(state.src);
  if (d === null || !Number.isFinite(d) || d <= SLOW_DEGREE) return null;
  const cap = DEGREE_CEILING[state.mode];
  if (cap && d > cap) return null;
  return `degree ${d} over ${f.name}: exact preprocessing can take minutes at this degree` +
         `${cap ? ` (degrees above ${cap} are not compiled)` : ''}; the Mersenne-prime fields take this polynomial ` +
         'much further (degrees up to 255; about a minute near the cap)';
}

/** The degree the chooser displays / the chips generate at (state.exDegree clamped for the mode). */
export const exampleDegree = state => clampDegree(state.mode, state.exDegree);

/** The worker message for the current job (posted by ui.js when a job starts). */
export const compileMessage = state => ({ id: state.jobId, src: state.src, ...MODE_MSG[state.mode] });
/** One message per worker: the main part always; the numeric part over ℚ / ℝ. */
export const compileMessages = state => [
  { ...compileMessage(state), part: 'main' },
  ...(needsNumericWorker(state.mode) ? [{ ...compileMessage(state), part: 'numeric' }] : []),
];

/** The selected comparison row (null when 'ours' is selected or there is no result). */
export function comparisonRow(state) {
  if (!state.result || state.method === 'ours') return null;
  return state.result.comparisons?.find(r => r.name === state.method && r.ok) ?? null;
}

/** The selected method's row while its numeric worker is still computing. */
export function pendingRow(state) {
  if (!state.result || state.method === 'ours') return null;
  return state.result.comparisons?.find(r => r.name === state.method && r.pending) ?? null;
}

/** While the selected method is still computing: its row from the previous
 *  result, so the last chain stays mounted (ui.js dims it, as it dims the
 *  output during a job) instead of collapsing to a spinner.  Null when there
 *  is nothing to fall back on (the first selection) — the pane is then pending. */
export function staleRow(state) {
  if (!pendingRow(state) || !state.prevResult) return null;
  // never across a field switch: an ℝ chain under the ℂ label (and in a ℂ download) is no fallback
  if ((state.prevResult.fieldId ?? null) !== (state.result.fieldId ?? null)) return null;
  return state.prevResult.comparisons?.find(r => r.name === state.method && r.ok) ?? null;
}

/** Is the mounted output not (yet) the chain of the current input?  While a
 *  job runs, while a parse error stands over it, after a Cancel, and while the
 *  selected numeric method is still computing and shows its previous chain
 *  (staleRow).  ui.js dims every view of the result — the pane, the method
 *  chips, the comparison table, the phone stats line — on it. */
export const isStale = state =>
  state.busy || state.error !== null || !!state.cancelled || staleRow(state) !== null;

/** The comparison row the output shows: the selected one, or its stale
 *  predecessor while it computes (null when ours is shown or nothing is). */
const shownRow = state => comparisonRow(state) ?? staleRow(state);

/** The object whose chain the output shows: a comparison row (or its stale
 *  predecessor) or the result itself; null while the selected method is
 *  still computing and has no predecessor. */
export function selectedRow(state) {
  if (!state.result) return null;
  return shownRow(state) ?? (pendingRow(state) ? null : state.result);
}

/**
 * Operation counts of a row as displayed: countOps on its rendered text
 * (scalar multiplications counted, integer multiples charged as additions);
 * a row whose rendering shows no operation at all (no rendering, or a
 * constant) keeps its own counts.  Null when the row has no counts.
 *   → { mults, scalar, adds } with mults excluding the scalar ones
 */
export function rowOps(row, text = row?.mathText) {
  if (!row || row.mults === null || row.mults === undefined) return null;
  const o = text ? countOps(text) : null;
  if (!o || o.mults + o.adds + o.scalar === 0) return { mults: row.mults, adds: row.adds, scalar: 0 };
  // Pan's real scheme contains one multiplication by 2^N, charged in the
  // paper as a radix-point shift rather than as M.  Depending on notation the
  // textual parser sees either a scalar product or N doublings; remove that
  // displayed cost while retaining the shift as separate metadata.
  if (row.radixShifts) {
    if (o.scalar >= row.radixShifts)
      return { ...o, scalar: o.scalar - row.radixShifts, radix: row.radixShifts };
    const radixAdds = row.radixAdditionCost ?? row.radixExponent ?? 0;
    return { ...o, adds: Math.max(0, o.adds - radixAdds), radix: row.radixShifts };
  }
  return o;
}
const withCount = (name, row) => { const o = rowOps(row); return o === null ? name : `${name} (${o.mults + o.scalar})`; };

/** Method chips: [{ key, label, enabled, title, on }] — names with their total
 *  multiplication count (counted on the factored rendering, like the table). */
export function methodTabs(state) {
  const r = state.result;
  if (!r) return [];
  const tabs = [{
    key: 'ours', label: r.oursFailed ? 'This paper' : withCount('This paper', r),
    enabled: !r.oursFailed, pending: false, title: r.oursFailed ? String(r.oursFailed) : '',
  }];
  for (const c of r.comparisons ?? [])
    tabs.push({ key: c.name, label: c.ok ? withCount(c.name, c) : c.name, enabled: !!c.ok || !!c.pending,
      pending: !!c.pending, title: c.ok ? '' : String(c.note ?? '') });
  return tabs.map(t => ({ ...t, on: t.key === state.method }));
}

/**
 * The comparison table under the output pane, one row per method in worker
 * order (This paper, Horner, Estrin, Rabin–Winograd, Knuth–Eve, Pan; Belaga over ℂ):
 *   [{ key, name, ok, on, mults, scalar, adds, height, exact, exactNote, maxRelError, note }]
 * Counts come from rowOps on each method's factored rendering (mults = the
 * total, scalar = how many of them are by a constant); a method that did not
 * run has ok: false, null counts and its reason in `note`; a method that ran
 * carries its own note (the worker's description of what it did) there, so
 * the UI can list the notes under the table.  A row that is not exact
 * (≈ numeric) says why in `exactNote` — over ℝ / ℂ the preprocessing itself is
 * exact and only the chain constants are rounded to (complex) doubles, with the
 * measured rounding error ("max rel. error 3.6e+26") when the worker measured
 * it; the root-finding methods name what they solved numerically — null
 * otherwise.  `maxRelError` is that figure as a number (Infinity when the
 * chain constants exceed the double range), null when none was measured.
 */
export function comparisonTable(state) {
  const r = state.result;
  if (!r) return [];
  const entries = [{ key: 'ours', name: 'This paper', ok: !r.oursFailed, exact: r.exact ?? true,
                     note: r.oursFailed ? String(r.oursFailed) : displayNote(r.note), row: r }];
  for (const c of r.comparisons ?? [])
    entries.push({ key: c.name, name: c.name, ok: !!c.ok, pending: !!c.pending, exact: !!c.exact, note: displayNote(c.note), row: c });
  return entries.map(({ row, ...e }) => {
    const o = e.ok ? rowOps(row) : null;
    return { ...e, pending: !!e.pending, on: e.key === state.method, ref: referenceFor(e.name),
      mults: o ? o.mults + o.scalar : null, scalar: o ? o.scalar : 0,
      adds: o ? o.adds : null, height: e.ok ? row.height ?? null : null, exact: e.ok ? e.exact : null,
      exactNote: e.ok && !e.exact ? numericNote(row, fieldOf(r.fieldId ?? state.mode)) : null,
      maxRelError: e.ok && !e.exact ? rowMaxRelError(row) : null };
  });
}

// The workers' notes state that each chain was verified (re-expansion, sample
// points).  Those checks are internal — the chains are correct by construction
// and the page never shows a verification claim — so the clause is cut before
// a note reaches a view: "; verified by …", ", verified by …" up to the next
// clause break, and the sentence tails "… and the printed chain (was) (independently) verified …".
const VERIFY_CLAUSE = /(?:[;,]\s*(?:and\s+)?|\s+and\s+|^)(?:the printed chain )?(?:was )?(?:independently )?verified\b(?:(?!max rel\. error)[^;.—])*\.?/g;
/** A worker's note as the table shows it ('' for none): without its verification
 *  clause, and without the trailing "max rel. error …" figure of the numeric
 *  methods (the table carries it as `maxRelError` / in `exactNote`). */
export const displayNote = note => String(note ?? '')
  .replace(VERIFY_CLAUSE, '').replace(/\s*max rel\. error \S+\s*$/, '')
  .replace(/\s*—/g, ' —').replace(/\s+([;,]|\.(?!\.))/g, '$1').replace(/ {2,}/g, ' ').trim();   // a literal "..." keeps its space

/** The measured rounding error of a numeric row: the worker's number (ours over
 *  ℝ / ℂ: result.maxRelError, Infinity when the constants overflow), else the
 *  figure the numeric methods write into their note; null when none. */
function rowMaxRelError(row) {
  if (typeof row.maxRelError === 'number') return Number.isNaN(row.maxRelError) ? null : row.maxRelError;
  const m = /max rel\. error (\S+)/.exec(row.note ?? '');
  const v = m ? Number(m[1]) : NaN;
  return Number.isNaN(v) ? null : v;
}

/** Why a row is ≈ numeric: the ℝ / ℂ rendering of an exact chain (ours, and the
 *  classical methods whose preprocessing is exact or absent) rounds the constants
 *  to doubles / complex doubles — with the measured rounding error when the
 *  worker has one (only the paper's chain is measured), or the overflow wording
 *  when the constants exceed the double range; Knuth–Eve, Pan and Belaga carry
 *  their own preprocessing kind + measured error. */
function numericNote(row, f = null) {
  const pre = row.preprocessing;
  if (!pre || pre === 'none' || pre === 'rational' || pre === 'numeric') {
    const dbl = f?.complex ? 'complex doubles' : 'doubles';
    const head = f?.complex ? 'exact Gaussian-rational preprocessing' : 'exact rational preprocessing';
    const err = rowMaxRelError(row);
    if (err === null) return `${head}; chain constants rounded to ${dbl}`;
    if (!Number.isFinite(err))
      return `${head}; the chain constants exceed the double range, so no ${f?.complex ? 'complex-double' : 'double-precision'} chain exists`;
    return `${head}; chain constants rounded to ${dbl}, max rel. error ${err.toExponential(1)}`;
  }
  const err = /max rel\. error \S+/.exec(row.note ?? '');   // the rest of the note is the method's description
  return err ? `${pre}, ${err[0]}` : pre;
}

/** Stat tiles for the selected row, counted on the form actually shown:
 *  [{ label, value }] (empty when the row has no counts). */
export function stats(state) {
  const src = selectedRow(state);
  if (!src) return [];
  const ops = rowOps(src, effectiveForm(state) === 'original' ? src.mathTextOriginal : src.mathText);
  if (ops === null) return [];
  const row = shownRow(state);
  return [
    { label: 'multiplications', value: ops.scalar ? `${ops.mults + ops.scalar} (${ops.scalar} scalar)` : ops.mults },
    { label: 'additions', value: ops.adds },
    { label: 'mult. depth', value: src.height },
    ...(ops.radix ? [{ label: 'radix shifts', value: ops.radix }] : []),
    { label: 'field', value: state.result.fieldName },
    { label: 'exact', value: (row ? row.exact : state.result.exact ?? true) ? 'yes' : '≈ numeric' },
  ];
}

/** Form actually shown: 'original' falls back to the factored list for rows without an original rendering. */
export function effectiveForm(state) {
  const src = selectedRow(state);
  return state.form === 'original' && src?.mathTextOriginal ? 'original' : 'factor';
}

/** Constant style actually used in the C view: fractions only over ℚ, and only for rows that have them. */
export function effectiveCstyle(state) {
  const src = selectedRow(state);
  return state.mode === 'Q' && state.cstyle === 'fraction' && src?.cTextFraction ? 'fraction' : 'float';
}

/** The exact C source selected by the method and constant-style controls.
 *  Both the visible pane and the downloadable bundle use this selector, so
 *  they cannot silently choose different variants. */
export function selectedCSource(state) {
  const row = selectedRow(state);
  if (!row) return null;
  const style = effectiveCstyle(state);
  const code = style === 'fraction' ? row.cTextFraction : row.cText;
  if (!code) return null;
  return { code, style, label: shownRow(state)?.name ?? 'This paper' };
}

/** The exact math text of the selected row in the effective form ('' without one). */
function exactMathText(state) {
  const src = selectedRow(state);
  if (!src) return '';
  return (effectiveForm(state) === 'original' ? src.mathTextOriginal : src.mathText) ?? '';
}

/** Readable constant style of a field: decimals in characteristic 0, hex bit
 *  patterns in binary fields; Mersenne residues are decimal already (null). */
const readableStyle = f => (f?.char === 0 ? 'decimal' : f?.char === 2 ? 'hex' : null);

/** The readable rendering of the shown math text, or null when the field has
 *  none or it would not differ from the exact text: { style, text }. */
function readableRendering(state) {
  const style = readableStyle(fieldOf(state.mode));
  if (!style) return null;
  const text = exactMathText(state), out = formatConstants(text, style);
  return out === text ? null : { style, text: out };
}

/** Constant format actually shown in the math view ('exact' unless the readable one applies). */
export function effectiveNumfmt(state) {
  return state.numfmt === 'decimal' && state.view === 'math' && selectedRow(state) && readableRendering(state) ? 'decimal' : 'exact';
}

/** The state the output panes render from.  On phones the constants strip is
 *  hidden, and numeric rows — everything over ℝ / ℂ, and the numerically
 *  preprocessed methods (Knuth–Eve, Pan) over ℚ — show their constants to six
 *  significant digits (the readable rendering); exact fractions are left alone. */
export function presentedState(state, { compact = false } = {}) {
  if (!compact || state.numfmt === 'decimal' || !state.result) return state;
  const row = shownRow(state);
  const numeric = inexactChar0(fieldOf(state.mode)) || (row ? row.exact === false : state.result.exact === false);
  return numeric ? { ...state, numfmt: 'decimal' } : state;
}

/**
 * The sub-option strips on the right of the view bar (empty without a result):
 *   [{ kind: 'form' | 'numfmt' | 'constants', label, options: [{ key, label, on, enabled, title }] }]
 * math view: form (factor / original) and numfmt (exact / decimal|hex);
 * C view over ℚ: constants (float / fraction).  Option keys are unique across strips.
 */
export function subOptionStrips(state) {
  const src = selectedRow(state);
  if (!src) return [];
  if (state.view === 'math') {
    const hasOriginal = !!src.mathTextOriginal;
    const eff = effectiveForm(state);
    const f = fieldOf(state.mode), style = readableStyle(f);
    const readable = readableRendering(state);
    const effN = effectiveNumfmt(state);
    const dbl = inexactChar0(f);          // ℝ / ℂ: the constants are (complex) doubles already
    return [
      { kind: 'form', label: 'form:',
        options: [
          { key: 'factor', label: 'factor', on: eff === 'factor', enabled: true, title: 'one product per line' },
          { key: 'original', label: 'original', on: eff === 'original', enabled: hasOriginal,
            title: hasOriginal ? 'the method\'s own form: the paper\'s gadget presentation, Horner\'s nested form, Estrin\'s tree, …'
                               : 'no original form for this row' },
        ] },
      { kind: 'numfmt', label: 'constants:',
        options: [
          { key: 'exact', label: dbl ? 'full' : 'exact', on: effN === 'exact', enabled: true,
            title: dbl ? `the ${f.complex ? 'complex-double' : 'double-precision'} constants in full (shortest round-trip decimals)`
                       : 'the constants exactly as the preprocessing produced them' },
          { key: 'decimal', label: style === 'hex' ? 'hex' : 'decimal', on: effN === 'decimal', enabled: !!readable,
            title: !style ? 'Mersenne-field constants are decimal residues already'
              : !readable ? 'nothing to reformat in this rendering'
              : style === 'hex' ? 'every constant as a hexadecimal bit pattern (display only)'
              : 'about six significant digits, scientific notation when needed (display only — the chain stays exact)' },
        ] },
    ];
  }
  if (state.view === 'c' && state.mode === 'Q') {
    const hasFrac = !!src.cTextFraction;
    const eff = effectiveCstyle(state);
    return [{
      kind: 'constants', label: 'constants:',
      options: [
        { key: 'float', label: 'float', on: eff === 'float', enabled: true,
          title: 'decimal double literals (shortest round-trip)' },
        { key: 'fraction', label: 'fraction', on: eff === 'fraction', enabled: hasFrac,
          title: hasFrac ? 'exact (double)NUM/DEN — correctly rounded when both fit in 53 bits'
                         : 'no exact-fraction rendering for this method' },
      ],
    }];
  }
  return [];
}

/** The first sub-option strip (the form strip in the math view, the C constants strip over ℚ), or null. */
export const availableSubOptions = state => subOptionStrips(state)[0] ?? null;

/**
 * What the pane below the view bar shows, or null without a result:
 *   { kind: 'math', text }                       chain text (readable constants applied when chosen)
 *   { kind: 'c', code }                          C source (ui.js highlights it)
 *   { kind: 'c-missing', note, text }            no C for this field / chain: note line + math text
 *                                                (the worker's reason, result.cMissing, when it gave one)
 *   { kind: 'graph', svg }                       SVG string from the worker
 *   { kind: 'graph-missing', note }
 *   { kind: 'pending', note }                    the selected method is still computing and has no
 *                                                previous chain to keep showing (staleRow)
 */
/** Why a row has no C rendering: the worker's `cMissing` (compile2.js and
 *  compile0.js both set it; the "— no C rendering: …" tail of the note is the
 *  fallback for payloads without the field), or null. */
const cMissingOf = row =>
  (typeof row.cMissing === 'string' && row.cMissing.trim()) ? row.cMissing.trim()
  : (/—\s*no C rendering:\s*(.+?)\s*$/.exec(row.note ?? '')?.[1] ?? null);

export function paneContent(state) {
  const src = selectedRow(state);
  if (!src) {
    const waiting = pendingRow(state);
    if (waiting) return { kind: 'pending', note: `${waiting.name} is still computing its numerical preprocessing\u2026` };
    return null;
  }
  if (state.view === 'math') {
    const readable = state.numfmt === 'decimal' ? readableRendering(state) : null;
    return { kind: 'math', text: readable ? readable.text : exactMathText(state) };
  }
  if (state.view === 'c') {
    const selected = selectedCSource(state);
    if (selected) return { kind: 'c', code: selected.code };
    const f = fieldOf(state.result.fieldId ?? state.mode);
    const fieldHasC = state.result.cCode ?? f?.cCode ?? true;
    // the worker says why a chain has no C (constants beyond the double range);
    // a registry field without a C emitter has none for any row
    const reason = cMissingOf(src);
    const note = !fieldHasC ? '/* no C rendering for this field yet */'
      : reason ? `/* no C for this chain: ${reason} */`
      : '/* no C rendering for this method */';
    return { kind: 'c-missing', text: src.mathText ?? '', note };
  }
  if (src.graphSvg) return { kind: 'graph', svg: src.graphSvg,
    dash: src.graphSvg.includes('stroke-dasharray'),   // any subtracted input?
    kx: /\d×/.test(src.graphSvg) };                    // any integer-multiple edge label?
  return { kind: 'graph-missing', note: 'no graph for this method' };
}

// ---- URL-hash sharing ------------------------------------------------------

/** The state as the Share button's URL hash:
 *  #ex=<chip>|src=..&mode=..&method=..&view=..&form=..&cstyle=..&numfmt=..&deg=..[&seed=..][&monic=0]
 *  A held example chip is shared by its key (`ex=`, with deg / seed / monic
 *  regenerating it — a full-width key polynomial would be 1.5 kB of src=);
 *  typed text travels verbatim in src=. */
export const hashFromState = s =>
  (exampleHeld(s) ? `#ex=${encodeURIComponent(s.exKey)}` : `#src=${encodeURIComponent(s.src)}`) +
  `&mode=${s.mode}&method=${encodeURIComponent(s.method)}` +
  `&view=${s.view}&form=${s.form}&cstyle=${s.cstyle}&numfmt=${s.numfmt}&deg=${clampDegree(s.mode, s.exDegree)}` +
  (s.exSeed ? `&seed=${s.exSeed}` : '') + (s.exMonic ? '' : '&monic=0');

/**
 * Seed a boot state from location.hash (pure; ui.js passes it to useReducer's
 * init, and the 'restore' action to a hashchange).  Unknown / invalid params
 * keep `base`'s values: a method the field cannot show falls back to 'ours'
 * (a hyphen typed for the en dash of 'Rabin–Winograd' / 'Knuth–Eve' is
 * accepted); `ex=` names a chip (an unknown key falls to the field's default
 * example); `src=` carries typed text (and the src= links of earlier Shares);
 * a hash with neither seeds the requested mode's default example at the
 * requested degree, so a mode-only link still compiles something.  Never
 * starts a job — the normal first-load auto-compile runs on the returned state.
 */
export function stateFromHash(base, hash) {
  if (typeof hash !== 'string' || !hash.replace(/^#/, '')) return base;
  const p = new URLSearchParams(hash.replace(/^#/, ''));
  const s = { ...base };
  const mode = LEGACY_MODES[p.get('mode')] ?? p.get('mode');
  if (MODES.includes(mode)) s.mode = mode;
  const deg = p.get('deg');   // Number(null) would be 0, so require the param
  if (deg !== null && deg.trim() !== '' && Number.isInteger(Number(deg)))
    s.exDegree = clampDegree(s.mode, Number(deg));
  const seed = p.get('seed');
  if (seed !== null && /^\d{1,9}$/.test(seed.trim())) s.exSeed = Number(seed);
  const monic = p.get('monic');
  if (monic === '0' || monic === '1') s.exMonic = monic === '1';
  const exKey = p.get('ex'), src = p.get('src');
  if (exKey && exKey.trim()) {
    const exs = examplesFor(s.mode, s.exDegree, s.exSeed, s.exMonic);
    const ex = exs.find(e => e.key === exKey.trim()) ?? defaultExample(s.mode, s.exDegree, s.exSeed, s.exMonic);
    if (ex) { s.src = ex.src; s.exKey = ex.key; }
  } else if (src && src.trim()) { s.src = src; s.exKey = null; }
  else if (s.mode !== base.mode || s.exDegree !== base.exDegree || s.exMonic !== base.exMonic)
    s.src = defaultExample(s.mode, s.exDegree, s.exSeed, s.exMonic).src;
  // recognize an untouched generated example so the degree stepper keeps working
  const ex = examplesFor(s.mode, s.exDegree, s.exSeed, s.exMonic).find(e => e.src === s.src);
  s.exKey = ex ? ex.key : (exampleHeld(s) ? s.exKey : null);
  const method = (p.get('method') ?? '').trim().replace(/-/g, '–');   // 'Rabin-Winograd' → 'Rabin–Winograd'
  if (methodNamesFor(s.mode).includes(method)) s.method = method;
  else if (method) s.method = 'ours';                 // a method the field cannot show
  if (VIEWS.includes(p.get('view'))) s.view = p.get('view');
  if (FORMS.includes(p.get('form'))) s.form = p.get('form');
  if (CSTYLES.includes(p.get('cstyle'))) s.cstyle = p.get('cstyle');
  if (NUMFMTS.includes(p.get('numfmt'))) s.numfmt = p.get('numfmt');
  return s;
}
