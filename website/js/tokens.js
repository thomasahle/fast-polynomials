// The constant-token grammar of rendered chain text — the single definition
// every consumer (chain.js counters/formatters, cgen.js parser, graph.js,
// mathview.js, compare.js and the test evaluators) matches against.
//
//   real     -?ddd[.ddd][e±dd][/ddd]      12, -3/2, 0.25, 1.5e-7, 65342529/16384
//   hex      -?0x…                        binary-field constants
//   complex  (re±imi)                     ONE atomic token: the real part is always
//            present, the imaginary part always carries digits (never a bare i),
//            no spaces, decimal doubles only — (0+2i), (-2+1i), (1.5-0.25i),
//            (1e-7+3.2e+5i).  A real value is never printed in this form; it
//            stays a plain real token.  Producers: complexToken below, fmtC in
//            methods/motzkin.js, GaussRat.toDisplay in gauss.js (through
//            ratToDoubleString, so it also covers parts beyond the double
//            range) and formatConstToken in chain.js (which re-rounds an
//            existing token through COMPLEX_PARTS).
const DEC = String.raw`\d+(?:\.\d+)?(?:[eE][+-]?\d+)?`;

/** Source fragments (no anchors, no capturing groups) for composing regexes. */
export const REAL_SRC = String.raw`-?${DEC}(?:\/\d+)?`;
export const HEX_SRC = String.raw`-?0x[0-9a-fA-F]+`;
export const COMPLEX_SRC = String.raw`\(-?${DEC}[+-]${DEC}i\)`;

/** Whole-token tests. */
export const REAL_TOKEN = new RegExp(`^${REAL_SRC}$`);
export const HEX_TOKEN = new RegExp(`^${HEX_SRC}$`);
export const COMPLEX_TOKEN = new RegExp(`^${COMPLEX_SRC}$`);
/** Any constant token: real, hex or complex. */
export const NUM_TOKEN = new RegExp(`^(?:${HEX_SRC}|${REAL_SRC}|${COMPLEX_SRC})$`);

/** The parts of a complex token: [, re, sign, im] (im without its sign). */
export const COMPLEX_PARTS = new RegExp(String.raw`^\((-?${DEC})([+-])(${DEC})i\)$`);

/** Does a chain text (or one right-hand side) contain a complex constant? */
export function hasComplexToken(text) {
  return new RegExp(COMPLEX_SRC).test(String(text ?? ''));
}

/** The complex literal starting exactly at s[i], or null. */
const COMPLEX_AT = new RegExp(COMPLEX_SRC, 'y');
export function complexTokenAt(s, i) {
  COMPLEX_AT.lastIndex = i;
  const m = COMPLEX_AT.exec(s);
  return m ? m[0] : null;
}

/** A complex token -> { re, im } doubles, or null when `tok` is not one. */
export function parseComplexToken(tok) {
  const m = COMPLEX_PARTS.exec(String(tok));
  if (!m) return null;
  return { re: Number(m[1]), im: Number(m[3]) * (m[2] === '-' ? -1 : 1) };
}

/** The value of a real or complex token as { re, im } doubles (fractions
 *  divided in doubles), or null for anything else (wires, hex, k·w). */
export function numTokenValue(tok) {
  const t = String(tok);
  const c = parseComplexToken(t);
  if (c) return c;
  if (!REAL_TOKEN.test(t)) return null;
  const [a, b] = t.split('/');
  return { re: b ? Number(a) / Number(b) : Number(a), im: 0 };
}

/** A double to `digits` significant digits in its shortest round-trip form. */
export function fmtDouble(v, digits = 17) {
  if (Object.is(v, -0)) v = 0;
  return String(Number(v.toPrecision(digits)));
}

/** The canonical constant token of a complex double: a plain real token when
 *  the imaginary part is zero, otherwise (re±imi) — the form fmtC prints. */
export function complexToken(re, im, digits = 17) {
  if (im === 0 || Object.is(im, -0)) return fmtDouble(re, digits);
  return `(${fmtDouble(re, digits)}${im < 0 ? '-' : '+'}${fmtDouble(Math.abs(im), digits)}i)`;
}
