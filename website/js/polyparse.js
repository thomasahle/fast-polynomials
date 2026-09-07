// Parse a user-typed polynomial into a coefficient array (index = degree).
// Grammar (whitespace-insensitive, except that a number may not contain any;
// the variable is x or X):
//   poly  := term (('+'|'-'|'−') term)*   with an optional leading sign; a sign
//            directly after a sign folds in (x^3 + -1 reads as x^3 − 1)
//   term  := coef | coef mul? var | var (mul coef)? | term '/' int   (a term divided by an integer)
//   coef  := int ('/' int)? | decimal ('e' int)?   (char 0)  |  int | hex     (char 2)
//            optionally in parentheses: (1/6)x^3, (-1/2)x
//            over ℂ ({ complex: true }) also  real? 'i',  '(' real ')' '*'? 'i'  and
//            '(' real ('+'|'-') real? 'i' ')':  i, 2i, 2.5i, 1/2i, (1/2)i, (-1/2)i, (1/2)*i,
//            (1+2i), (2-i), (1/2-3/4i), (1+2i)x^2, 2i*x, i x^3
//   var   := x | x '^' int | x '**' int | x with Unicode superscripts (x², x¹²)
//   mul   := '*' | '·' | '×'
// so x^3/6, 3x^2/2, x/2, 2*x, x*2, 1/6 x^3, (1/6)x^3, x**3, x³ and a Unicode
// minus all read.  Exponents above MAX_PARSE_DEGREE are rejected before the
// coefficient array is allocated.  Returns { coeffs: (Rat|GaussRat|bigint)[], degree } — bigint
// lane for char 2 (values are field elements encoded as BigInt bit patterns),
// GaussRat for EVERY coefficient over ℂ.  Decimal and exponent forms (0.25,
// 1.5e-3) are read exactly into Rat in characteristic 0.
import { Rat } from './rat.js';
import { GaussRat } from './gauss.js';
import { gfLiteral, echo } from './field.js';
import { MAX_DEGREE, DEGREE_CEILING } from './methodlist.js';   // the caps the message quotes (no imports of its own)

const SUP = { '⁰': '0', '¹': '1', '²': '2', '³': '3', '⁴': '4', '⁵': '5', '⁶': '6', '⁷': '7', '⁸': '8', '⁹': '9' };

/** Largest exponent the parser accepts. Every compiler on the site stops far
 *  below it (26 in characteristic 2, 38 over ℚ/ℝ/ℂ, 255 over the Mersenne-prime
 *  fields — methodlist.js MAX_DEGREE and DEGREE_CEILING), so the cap costs
 *  nothing; it exists so that a typo like x^1000000000 is rejected with a
 *  message instead of allocating a billion-entry coefficient array. */
export const MAX_PARSE_DEGREE = 10000;

/** Unicode superscript exponents as carets: x² → x^2. */
const supers = src => String(src).replace(/[⁰¹²³⁴⁵⁶⁷⁸⁹]+/g, run => '^' + [...run].map(c => SUP[c]).join(''));

/** Spelling variants → the canonical grammar (superscripts, **, ·, ×, −). */
function normalize(src) {
  // Whitespace inside a number would concatenate its digits silently ("2 3x" → 23x).
  // Probe a superscript-normalized copy so "x² 3" is caught like "x^2 3", and let a hex
  // digit end the left number so "0x1f 2x" cannot swallow the next one.  (Both classes
  // are single characters: an alternation here backtracks quadratically on long runs.)
  const probe = supers(src);
  const gap = /([\da-fA-F])\s+([\d.]+)/.exec(probe);
  if (gap) {
    let b = gap.index;                                    // quote the whole literal ("0x1f 2", not "f 2")
    while (b > 0 && (/[0-9a-fA-F]/.test(probe[b - 1]) || ((probe[b - 1] === 'x' || probe[b - 1] === 'X') && probe[b - 2] === '0'))) b--;
    const left = echo(probe.slice(b, gap.index + 1)), right = echo(gap[2]);
    throw new Error(`whitespace inside a number ("${left} ${right}"): did you mean ${left}·${right} or ${left} + ${right}?`);
  }
  return supers(src).replace(/\s+/g, '')
    .replace(/\*\*/g, '^').replace(/[·×⋅]/g, '*').replace(/[−–]/g, '-').replace(/⁄/g, '/');
}

/** True when the hex-digit run ending just before index j is a 0x… literal, so
 *  the e/E that ends it is a hex digit and not a mantissa's exponent marker.
 *  Walks backwards (a slice + regex here would be quadratic on a long term). */
function endsHexLiteral(s, start, j) {
  let k = j;
  while (k > start && /[0-9a-fA-F]/.test(s[k - 1])) k--;
  return k >= start + 2 && (s[k - 1] === 'x' || s[k - 1] === 'X') && s[k - 2] === '0';
}

export function parsePoly(src, { char2 = false, complex = false } = {}) {
  const s = normalize(src);
  if (!s) throw new Error('empty input');
  // split into signed terms at top level (signs inside parentheses or right
  // after a mantissa's exponent marker, as in 2e-3, belong to the term)
  const terms = [];
  let i = 0, sign = 1, depth = 0;
  if (s[i] === '+') i++;
  else if (s[i] === '-') { sign = -1; i++; }
  let start = i;
  for (; i <= s.length; i++) {
    const c = s[i];
    if (c === '(') { depth++; continue; }
    if (c === ')') { depth--; continue; }
    if (depth > 0 && i < s.length) continue;
    // a mantissa's exponent marker (2e-3), in every characteristic: over GF(2^k)
    // the literal is rejected later with the "decimal" message rather than split
    // into a term "2e" and blamed on a stray variable.  A hex literal ending in
    // e/E (0x1e + 1) is a constant, not a mantissa, so the sign stays a sign.
    const inExponent = (c === '+' || c === '-') && i >= start + 2 &&
      /[eE]/.test(s[i - 1]) && /\d/.test(s[i - 2]) && /\d/.test(s[i + 1] ?? '') &&
      !endsHexLiteral(s, start, i);
    if (inExponent) continue;
    if (c === '+' || c === '-' || i === s.length) {
      if (i === start) {
        if (i === s.length) throw new Error('the polynomial ends with a sign');
        // a sign directly after a sign (x^3 + -1, as string-joined coefficient
        // lists produce): fold it into the term's sign
        if (c === '-') sign = -sign;
        start = i + 1;
        continue;
      }
      // a minus right after the caret is a negative exponent (x^-1); a caret with
      // nothing after it ("x^", "x^ + 1") is a half-typed term, named as one
      if (c === '-' && s[i - 1] === '^')
        throw new Error(`"${echo(s.slice(start, i + 1))}": exponents must be non-negative integers`);
      terms.push({ text: s.slice(start, i), sign });
      sign = c === '-' ? -1 : 1;
      start = i + 1;
    }
  }
  if (depth !== 0) throw new Error('unbalanced parentheses');
  const monos = terms.map(t => parseTerm(t.text, t.sign, char2, complex));
  let degree = 0;                                   // (no spread: a 100k-term input would overflow the call stack)
  for (const m of monos) if (m.deg > degree) degree = m.deg;
  const zero = char2 ? 0n : complex ? GaussRat.ZERO : Rat.ZERO;
  const coeffs = Array.from({ length: degree + 1 }, () => zero);
  for (const m of monos) {
    coeffs[m.deg] = char2 ? (coeffs[m.deg] ^ m.coef) : coeffs[m.deg].add(m.coef);
  }
  // trim (all-cancelled leading terms)
  let d = degree;
  const isZero = v => char2 ? v === 0n : v.isZero();
  while (d > 0 && isZero(coeffs[d])) d--;
  coeffs.length = d + 1;
  return { coeffs, degree: d };
}

// a real coefficient literal: 3, 1/6, -0.5, 2e-3, 0x1f  (the digit branches are
// exclusive after the first run, so a long digit run cannot backtrack quadratically)
export const REAL_SRC = String.raw`(?:0x[0-9a-fA-F]+|\d+(?:\/\d+|\.\d*(?:[eE][+-]?\d+)?|[eE][+-]?\d+)?|\.\d+(?:[eE][+-]?\d+)?)`;
const REAL = REAL_SRC;
// a complex one (the imaginary unit is i; a bare i is 1i): i, 2i, 1/2i, 1+2i, 2-i, 1/2-3/4i
const CPX = String.raw`(?:${REAL}[+-])?${REAL}?i`;
// a coefficient literal, optionally parenthesized: 3, 1/6, (1/6), (-0.5), 2e-3, 0x1f, 2i, (1+2i),
// and a parenthesized real part before the unit: (1/2)i, (-1/2)i, (1/2)*i  (no capture groups)
const NUM = String.raw`(?:\(-?${REAL}\)\*?i|\(?-?(?:${CPX}|${REAL})\)?)`;
const COMPLEX_LIT_RE = new RegExp(`^(?:(-?${REAL})([+-]))?(-?)(${REAL})?i$`);   // 1: re, 2: sign of im, 3: sign of a lone im, 4: |im|
const TERM_RE = new RegExp(
  `^(?:(${NUM}))?` +                       // 1: leading coefficient
  String.raw`\*?` +
  String.raw`(?:([xX])(?:\^(\d+))?)?` +    // 2, 3: variable and exponent
  `(?:\\*(${NUM}))?` +                     // 4: trailing coefficient (x*2)
  String.raw`(?:\/(\d+))?$`);              // 5: divisor of the whole term (x^3/6)

function parseTerm(text, sign, char2, complex) {
  const m = TERM_RE.exec(text);
  if (!m || (!m[1] && !m[2]) || (m[4] && !m[2])) throw new Error(termError(text));
  const [, c1, varStr, expStr, c2, divStr] = m;
  // the cap runs before the coefficient array is allocated (parsePoly sizes it by the degree)
  if (expStr && Number(expStr) > MAX_PARSE_DEGREE)
    throw new Error(`"x^${echo(expStr)}": this page compiles degrees up to ${MAX_DEGREE} in characteristic 2, ` +
      `${DEGREE_CEILING.Q} over ℚ/ℝ/ℂ and ${DEGREE_CEILING.p61} over the Mersenne-prime fields`);
  const deg = varStr ? (expStr ? parseInt(expStr, 10) : 1) : 0;
  const lits = [c1, c2].filter(Boolean).map(t => t.replace(/[()*]/g, ''));   // (1/2)*i -> 1/2i
  if (char2) {
    // a fraction / decimal / exponent literal is a characteristic-0 coefficient
    // (BigInt would reject it with an unreadable "Cannot convert … to a BigInt")
    for (const lit of lits) {
      if (lit.endsWith('i'))
        throw new Error(`binary-field coefficients are bit patterns (integers or 0x… hex), but "${lit}" is ` +
          'a complex number — choose ℂ for it, or rewrite the polynomial');
      if (!/^0x/i.test(lit) && /[\/.eE]/.test(lit))
        throw new Error(`binary-field coefficients are bit patterns (integers or 0x… hex), but "${lit}" is ` +
          `${lit.includes('/') ? 'a fraction' : 'a decimal'} — choose ℚ, ℝ or a Mersenne-prime field for it, or rewrite the polynomial`);
      if (lit.startsWith('-')) throw new Error('use + only in characteristic 2 (−1 = 1): a binary field has no negatives');
    }
    if (divStr) throw new Error(`"${text}": a binary field has no division by ${divStr} — choose ℚ, ℝ or a Mersenne-prime field`);
    if (sign < 0) throw new Error('use + only in characteristic 2 (−1 = 1): a binary field has no negatives');
    if (lits.length > 1) throw new Error(termError(text));
    return { coef: lits.length ? BigInt(lits[0]) : 1n, deg };   // hex or decimal bit pattern
  }
  if (!complex) {
    for (const lit of lits) if (lit.endsWith('i'))
      throw new Error(`"${lit}" is a complex number — choose ℂ for it, or rewrite the polynomial`);
  }
  let coef = complex ? GaussRat.ONE : Rat.ONE;
  for (const lit of lits) coef = coef.mul(complex ? literalToGauss(lit) : literalToRat(lit));
  if (divStr) {
    if (/^0+$/.test(divStr)) throw new Error(`"${text}": division by zero`);
    coef = coef.div(new Rat(BigInt(divStr)));
  }
  if (sign < 0) coef = coef.neg();
  return { coef, deg };
}

/** A characteristic-0 coefficient literal (integer, fraction, decimal, exponent) as a Rat. */
function literalToRat(lit) {
  const neg = lit.startsWith('-');
  const body = neg ? lit.slice(1) : lit;
  let r;
  if (/^0x/i.test(body)) r = new Rat(BigInt(body));
  else if (body.includes('/')) {
    const [a, b] = body.split('/');
    if (/^0+$/.test(b)) throw new Error(`"${lit}": division by zero`);
    r = new Rat(BigInt(a), BigInt(b));
  } else if (/[.eE]/.test(body)) r = decimalToRat(body);
  else r = new Rat(BigInt(body));
  return neg ? r.neg() : r;
}

/** A complex coefficient literal (real ones included) as a GaussRat: i, 2i,
 *  -1/2i, 2.5e-3i, 1+2i, 2-i, 1/2-3/4i — and every literal literalToRat reads. */
function literalToGauss(lit) {
  if (!lit.endsWith('i')) return new GaussRat(literalToRat(lit));
  const m = COMPLEX_LIT_RE.exec(lit);
  if (!m) throw new Error(`cannot parse number "${lit}"`);
  const re = m[1] ? literalToRat(m[1]) : Rat.ZERO;
  const im = m[4] ? literalToRat(m[4]) : Rat.ONE;
  return new GaussRat(re, (m[2] || m[3]) === '-' ? im.neg() : im);
}

function termError(text) {
  // any letter but x / X (the variable) and i / I (the imaginary unit, never a stray variable)
  const other = /[A-HJ-WYZa-hj-wyz]/.exec(text.replace(/0x[0-9a-fA-F]+|\d[eE][+-]?\d/g, ''));
  if (other) return `cannot parse term "${text}": the variable must be x (found "${other[0]}")`;
  if (/[()]/.test(text)) return `cannot parse term "${text}": parentheses may only wrap a coefficient, e.g. (1/6)x^3 or (1+2i)x`;
  if (/i/i.test(text)) return `cannot parse term "${text}": i is the imaginary unit — write complex coefficients as 2i, (1+2i) or (1/2-3/4i)`;
  return `cannot parse term "${text}"`;
}

/** Exact rational value of a decimal literal such as 1.25, .5 or 2.5e-3. */
export function decimalToRat(str) {
  const m = /^(\d*)(?:\.(\d*))?(?:[eE]([+-]?\d+))?$/.exec(str);
  if (!m || (!m[1] && !m[2])) throw new Error(`cannot parse number "${str}"`);
  const ip = m[1] || '0', fp = m[2] || '', ex = m[3] ? parseInt(m[3], 10) : 0;
  const shift = ex - fp.length;
  const digits = BigInt(ip + fp);
  return shift >= 0 ? new Rat(digits * 10n ** BigInt(shift)) : new Rat(digits, 10n ** BigInt(-shift));
}

/** Render a coefficient array back to a display string (the input grammar:
 *  exact fractions; a GaussRat coefficient prints itself — a non-real one as
 *  (a+bi) with exact Rat parts, e.g. (1/2-3/4i)·x^2, a real one exactly as
 *  over ℚ — so ℂ needs no option here). */
export function polyToString(coeffs, { char2 = false } = {}) {
  const parts = [];
  for (let d = coeffs.length - 1; d >= 0; d--) {
    const c = coeffs[d];
    const isZero = char2 ? c === 0n : c.isZero();
    if (isZero) continue;
    const isOne = char2 ? c === 1n : c.isOne();
    const xs = d === 0 ? '' : d === 1 ? 'x' : `x^${d}`;
    let cs;
    if (char2) cs = isOne && d > 0 ? '' : gfLiteral(c);
    else if (isOne && d > 0) cs = '';
    else if (!char2 && d > 0 && c.eq(new Rat(-1n))) cs = '-';
    else cs = c.toString();
    parts.push((cs && xs && cs !== '-' ? cs + '·' : cs) + xs);
  }
  if (!parts.length) return '0';
  // "+ -3/2·x" → "− 3/2·x"; a parenthesized complex coefficient "(-1+2i)" never matches
  return parts.join(' + ').replace(/\+ -/g, '− ');
}
