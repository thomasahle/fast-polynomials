// Gaussian rationals ℚ(i): the exact elements of the ℂ field. Immutable value
// objects with the surface of js/rat.js's Rat (add/sub/mul/div/neg/inv/eq/…),
// but NOT a Rat subclass — the exact core (js/char0/core.js) pokes .n/.d of
// Rats, and a Gaussian rational has none.
//
// Printing: toString() is the exact input form ("3/2" when real, "(1/2+3/4i)"
// otherwise); toDisplay() is the canonical complex-double token of chain text
// (js/tokens.js: a real value prints exactly as ℝ prints — ratToDoubleString —
// and a non-real one as (re±imi): (0+2i), (-2+1i), (1.5-0.25i)).
import { Rat } from './rat.js';
import { ratToDoubleString } from './field.js';

const dbl = r => ratToDoubleString(r.n, r.d);
const abs = r => (r.isNeg() ? r.neg() : r);

export class GaussRat {
  /** @param {Rat|bigint|number} re @param {Rat|bigint|number} im */
  constructor(re, im = Rat.ZERO) {
    this.re = Rat.of(re);
    this.im = Rat.of(im);
    Object.freeze(this);
  }
  /** GaussRat | Rat | bigint | integer Number → GaussRat. */
  static of(x) {
    if (x instanceof GaussRat) return x;
    if (x instanceof Rat) return new GaussRat(x);
    if (typeof x === 'bigint' || (typeof x === 'number' && Number.isInteger(x))) return new GaussRat(Rat.of(x));
    throw new Error(`cannot make GaussRat from ${x}`);
  }
  static ZERO = new GaussRat(Rat.ZERO);
  static ONE = new GaussRat(Rat.ONE);
  static I = new GaussRat(Rat.ZERO, Rat.ONE);

  add(o) { o = GaussRat.of(o); return new GaussRat(this.re.add(o.re), this.im.add(o.im)); }
  sub(o) { o = GaussRat.of(o); return new GaussRat(this.re.sub(o.re), this.im.sub(o.im)); }
  mul(o) {
    o = GaussRat.of(o);
    return new GaussRat(this.re.mul(o.re).sub(this.im.mul(o.im)), this.re.mul(o.im).add(this.im.mul(o.re)));
  }
  div(o) { return this.mul(GaussRat.of(o).inv()); }
  neg() { return new GaussRat(this.re.neg(), this.im.neg()); }
  conj() { return new GaussRat(this.re, this.im.neg()); }
  /** |z|² = re² + im², a Rat. */
  norm() { return this.re.mul(this.re).add(this.im.mul(this.im)); }
  /** 1/z = conj(z) / |z|²; throws on zero. */
  inv() {
    if (this.isZero()) throw new Error('division by zero');
    const n = this.norm();
    return new GaussRat(this.re.div(n), this.im.neg().div(n));
  }
  eq(o) { o = GaussRat.of(o); return this.re.eq(o.re) && this.im.eq(o.im); }
  isZero() { return this.re.isZero() && this.im.isZero(); }
  isOne() { return this.re.isOne() && this.im.isZero(); }
  isReal() { return this.im.isZero(); }
  isInt() { return this.isReal() && this.re.isInt(); }
  /** Sign of the real part — only meaningful when isReal(). */
  isNeg() { return this.re.isNeg(); }
  /** Exact form: "3/2" when real, "(1/2+3/4i)" / "(1/2-3/4i)" otherwise. */
  toString() {
    if (this.isReal()) return this.re.toString();
    return `(${this.re}${this.im.isNeg() ? '-' : '+'}${abs(this.im)}i)`;
  }
  /** The canonical complex-double token (js/tokens.js COMPLEX_TOKEN), or the
   *  plain ℝ token when the value is real. */
  toDisplay() {
    if (this.isReal()) return dbl(this.re);
    return `(${dbl(this.re)}${this.im.isNeg() ? '-' : '+'}${dbl(abs(this.im))}i)`;
  }
}

/** ℂ as a js/field.js field: the exact arithmetic of ℚ(i) — preprocessing is
 *  exact — whose elements are displayed (and emitted in C) as complex doubles;
 *  mirrors R (real: false, complex: true). fromRat accepts a Rat or a GaussRat. */
export const Cx = {
  name: 'ℂ', char: 0, real: false, complex: true,
  zero: GaussRat.ZERO, one: GaussRat.ONE,
  add: (a, b) => GaussRat.of(a).add(b), sub: (a, b) => GaussRat.of(a).sub(b),
  mul: (a, b) => GaussRat.of(a).mul(b), div: (a, b) => GaussRat.of(a).div(b),
  neg: a => GaussRat.of(a).neg(), inv: a => GaussRat.of(a).inv(),
  eq: (a, b) => GaussRat.of(a).eq(b), isZero: a => GaussRat.of(a).isZero(), isOne: a => GaussRat.of(a).isOne(),
  fromInt: n => GaussRat.of(BigInt(n)), fromRat: r => GaussRat.of(r),
  toDisplay: a => GaussRat.of(a).toDisplay(),
};

/** The Gaussian-rational field in the duck-typed shape js/char0/core.js accepts
 *  (the interface of core.rationals(), a core Field with modulus null): coerce /
 *  from_int / zero() / one() / add / sub / neg / mul / inv / div / is_zero / eq,
 *  every operand coerced (the core mixes integer literals into field arithmetic). */
export function gaussCoreField() {
  const c = x => GaussRat.of(x);
  return {
    modulus: null,
    use_fractions: true,
    coerce: c,
    from_int: k => c(k),
    zero: () => GaussRat.ZERO,
    one: () => GaussRat.ONE,
    add: (a, b) => c(a).add(c(b)),
    sub: (a, b) => c(a).sub(c(b)),
    neg: a => c(a).neg(),
    mul: (a, b) => c(a).mul(c(b)),
    inv: a => c(a).inv(),
    div: (a, b) => c(a).mul(c(b).inv()),
    is_zero: a => c(a).isZero(),
    eq: (a, b) => c(a).eq(c(b)),
  };
}
