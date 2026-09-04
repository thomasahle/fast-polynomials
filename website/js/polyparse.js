// Parse a user-typed polynomial into a coefficient array (index = degree).
// Grammar (whitespace-insensitive):
//   poly  := term (('+'|'-') term)*   with optional leading sign
//   term  := coef? ('*'? var ('^' int)?)? | coef
//   coef  := int ('/' int)? | decimal ('e' int)?   (char 0)  |  int | hex     (char 2)
//   var   := 'x' | 'X'
// Returns { coeffs: (Rat|bigint)[], degree } — bigint lane for char 2
// (values are field elements encoded as BigInt bit patterns). Decimal and
// exponent forms (0.25, 1.5e-3) are read exactly into Rat in characteristic 0.
import { Rat } from './rat.js';

export function parsePoly(src, { char2 = false } = {}) {
  const s = src.replace(/\s+/g, '');
  if (!s) throw new Error('empty input');
  // tokenize into signed terms at top level
  const terms = [];
  let i = 0, sign = 1;
  if (s[i] === '+' ) i++;
  else if (s[i] === '-') { sign = -1; i++; }
  let start = i;
  for (; i <= s.length; i++) {
    const c = s[i];
    // a sign right after a mantissa's exponent marker (2e-3) belongs to the number
    const inExponent = !char2 && (c === '+' || c === '-') && i >= start + 2 &&
      /[eE]/.test(s[i - 1]) && /\d/.test(s[i - 2]) && /\d/.test(s[i + 1] ?? '');
    if (inExponent) continue;
    if (c === '+' || c === '-' || i === s.length) {
      if (i === start) throw new Error(`empty term at position ${i}`);
      terms.push({ text: s.slice(start, i), sign });
      sign = c === '-' ? -1 : 1;
      start = i + 1;
    }
  }
  const monos = terms.map(t => parseTerm(t.text, t.sign, char2));
  const degree = Math.max(...monos.map(m => m.deg), 0);
  const zero = char2 ? 0n : Rat.ZERO;
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

function parseTerm(text, sign, char2) {
  const m = text.match(/^(?:(0x[0-9a-fA-F]+|\d+(?:\/\d+)?|(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?))?\*?(?:([xX])(?:\^(\d+))?)?$/);
  if (!m || (!m[1] && !m[2])) throw new Error(`cannot parse term "${text}"`);
  const [, coefStr, varStr, expStr] = m;
  const deg = varStr ? (expStr ? parseInt(expStr, 10) : 1) : 0;
  if (char2) {
    // a fraction / decimal / exponent literal is a characteristic-0 coefficient
    // (BigInt would reject it with an unreadable "Cannot convert … to a BigInt")
    if (coefStr && !/^0x/i.test(coefStr) && /[\/.eE]/.test(coefStr))
      throw new Error(`binary-field coefficients are bit patterns (integers or 0x… hex), but "${coefStr}" is ` +
        `${coefStr.includes('/') ? 'a fraction' : 'a decimal'} — choose ℚ, ℝ or a Mersenne-prime field for it, or rewrite the polynomial`);
    if (sign < 0) throw new Error('use + only in characteristic 2 (−1 = 1): a binary field has no negatives');
    return { coef: coefStr ? BigInt(coefStr) : 1n, deg };   // hex or decimal bit pattern
  }
  let coef;
  if (!coefStr) coef = Rat.ONE;
  else if (coefStr.includes('/')) {
    const [a, b] = coefStr.split('/');
    coef = new Rat(BigInt(a), BigInt(b));
  } else if (/[.eE]/.test(coefStr)) coef = decimalToRat(coefStr);
  else coef = new Rat(BigInt(coefStr));
  if (sign < 0) coef = coef.neg();
  return { coef, deg };
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

/** Render a coefficient array back to a display string. */
export function polyToString(coeffs, { char2 = false } = {}) {
  const parts = [];
  for (let d = coeffs.length - 1; d >= 0; d--) {
    const c = coeffs[d];
    const isZero = char2 ? c === 0n : c.isZero();
    if (isZero) continue;
    const isOne = char2 ? c === 1n : c.isOne();
    const xs = d === 0 ? '' : d === 1 ? 'x' : `x^${d}`;
    let cs;
    if (char2) cs = isOne && d > 0 ? '' : (c > 15n ? '0x' + c.toString(16) : c.toString());
    else if (isOne && d > 0) cs = '';
    else if (!char2 && d > 0 && c.eq(new Rat(-1n))) cs = '-';
    else cs = c.toString();
    parts.push((cs && xs ? cs + '·' : cs) + xs);
  }
  if (!parts.length) return '0';
  return parts.join(' + ').replace(/\+ -/g, '− ');
}
