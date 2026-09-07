// Exact rational arithmetic on BigInt. Immutable value objects.
// Used by the char-0 lane; all decoding is exact (no floats anywhere).
//
// Performance notes (the exact decoder spends most of its time here — the
// Taylor chips at degree 20+ push the constants to 10-20k bits):
//   * gcd is Lehmer's algorithm (Knuth TAOCP 4.5.2, Algorithm L): the leading
//     50 bits of both operands are reduced with double-precision Euclid steps,
//     and the accumulated 2×2 cofactor matrix is applied to the full BigInts
//     once per ~50 bits removed. Euclid on doubles finishes operands of ≤ 52
//     bits. The result is exactly gcd(|a|, |b|) for every input. The bit
//     length that positions the heads is carried from round to round (one
//     shift + clz32, never a toString): recomputing it from a hex string each
//     round cost as much as the round itself.
//   * add / sub / mul reduce the way Knuth 4.5.1 does — gcds of the
//     denominators (or the cross gcds), never a gcd of the full products — and
//     integers / equal denominators skip the gcd entirely.  Every Rat is still
//     canonical (den > 0, gcd(num, den) = 1, zero as 0/1), so results are
//     identical to normalising the raw products.

const HEAD = 50;     // bits of head simulated in doubles; heads and cofactors stay below 2^51,
                     // so every sum, product and quotient below is exact in a double
const SMALL = 52;    // operands of at most this many bits: plain double-precision Euclid

/** Bit length of an integer 0 < v < 2^53. */
function bitlen53(v) {
  return v >= 4294967296 ? 64 - Math.clz32(Math.floor(v / 4294967296)) : 32 - Math.clz32(v);
}

/** Exact bit length of a BigInt x > 0 given an upper bound hi ≥ bitlen(x): one
 *  shift when hi is within 53 bits of the answer (the case between Lehmer
 *  rounds, where the previous length bounds the new one), a binary search of
 *  shifts otherwise. Never converts the BigInt to a string. */
function bitlenBelow(x, hi) {
  let k = hi - 53;
  if (k <= 0) return bitlen53(Number(x));
  const t = Number(x >> BigInt(k));                     // exact: x < 2^hi so t < 2^53
  if (t > 0) return k + bitlen53(t);
  let lo = 0;                                           // 2^lo ≤ x < 2^k
  while (k - lo > 53) { const mid = (lo + k) >> 1; if (x >> BigInt(mid)) lo = mid; else k = mid; }
  return lo + bitlen53(Number(x >> BigInt(lo)));
}

/** Exact bit length of a BigInt's magnitude: bitlen(0n) = 0, bitlen(-x) = bitlen(x).
 *  (A negative x must be folded here: x >> k saturates at -1n, so the doubling
 *  probe below would never terminate on one.) */
export function bitlen(x) {
  if (x <= 0n) { if (x === 0n) return 0; x = -x; }
  let hi = 64;
  while (x >> BigInt(hi)) hi *= 2;
  return bitlenBelow(x, hi);
}

/** gcd(|a|, |b|) as a non-negative BigInt (gcd(0, 0) = 0). */
export function bgcd(a, b) {
  if (a < 0n) a = -a;
  if (b < 0n) b = -b;
  if (a < b) { const t = a; a = b; b = t; }
  if (!b) return a;
  let nb = bitlen(a);            // bit length of a, maintained across rounds (a only shrinks)
  while (b) {
    if (nb <= SMALL) {
      let x = Number(a), y = Number(b);
      while (y) { const t = x % y; x = y; y = t; }
      return BigInt(x);
    }
    const sh = BigInt(nb - HEAD);
    let ah = Number(a >> sh), bh = Number(b >> sh);     // the heads, ah < 2^50, bh <= ah
    let A = 1, B = 0, C = 0, D = 1;                     // cofactors: (a, b) <- (A a + B b, C a + D b)
    for (;;) {                                          // Euclid on the heads while every
      if (bh + C === 0 || bh + D === 0) break;          // partial quotient is certain
      const q = Math.floor((ah + A) / (bh + C));
      if (q !== Math.floor((ah + B) / (bh + D))) break;
      let t = A - q * C; A = C; C = t;
      t = B - q * D; B = D; D = t;
      t = ah - q * bh; ah = bh; bh = t;
    }
    if (B === 0) {                                      // no certain step: one full-precision step
      const t = a % b; a = b; b = t;
    } else {
      const t = BigInt(A) * a + BigInt(B) * b;
      b = BigInt(C) * a + BigInt(D) * b;
      a = t;
    }
    if (b) nb = bitlenBelow(a, nb);                     // the new a is the old b or smaller: nb still bounds it
  }
  return a;
}

const REDUCED = Symbol('reduced');   // constructor tag: (num, den) already canonical

export class Rat {
  /** @param {bigint} num @param {bigint} den (den > 0 after normalize) */
  constructor(num, den = 1n, tag) {
    if (tag === REDUCED) {
      this.n = num; this.d = den;
    } else {
      if (den === 0n) throw new Error('division by zero');
      if (den < 0n) { num = -num; den = -den; }
      if (den === 1n) { this.n = num; this.d = 1n; }
      else if (num === 0n) { this.n = 0n; this.d = 1n; }
      else {
        const g = bgcd(num, den);
        this.n = g === 1n ? num : num / g;
        this.d = g === 1n ? den : den / g;
      }
    }
    Object.freeze(this);
  }
  static of(x) {
    if (x instanceof Rat) return x;
    if (typeof x === 'bigint') return new Rat(x);
    if (typeof x === 'number' && Number.isInteger(x)) return new Rat(BigInt(x));
    throw new Error(`cannot make Rat from ${x}`);
  }
  static ZERO = new Rat(0n);
  static ONE = new Rat(1n);
  add(o) { return addSigned(this, Rat.of(o), 1n); }
  sub(o) { return addSigned(this, Rat.of(o), -1n); }
  mul(o) {
    o = Rat.of(o);
    if (this.n === 0n || o.n === 0n) return Rat.ZERO;
    if (this.d === 1n && o.d === 1n) return new Rat(this.n * o.n, 1n, REDUCED);
    // a/b · c/d = (a/g1)(c/g2) / ((b/g2)(d/g1)) with g1 = gcd(a, d), g2 = gcd(c, b): already reduced
    const g1 = o.d === 1n ? 1n : bgcd(this.n, o.d);
    const g2 = this.d === 1n ? 1n : bgcd(o.n, this.d);
    const an = g1 === 1n ? this.n : this.n / g1, cn = g2 === 1n ? o.n : o.n / g2;
    const bd = g2 === 1n ? this.d : this.d / g2, dd = g1 === 1n ? o.d : o.d / g1;
    return new Rat(an * cn, bd * dd, REDUCED);
  }
  div(o) { return this.mul(Rat.of(o).inv()); }
  neg() { return this.n === 0n ? this : new Rat(-this.n, this.d, REDUCED); }
  inv() {
    if (this.n === 0n) throw new Error('division by zero');
    return this.n < 0n ? new Rat(-this.d, -this.n, REDUCED) : new Rat(this.d, this.n, REDUCED);
  }
  isZero() { return this.n === 0n; }
  isOne() { return this.n === 1n && this.d === 1n; }
  isInt() { return this.d === 1n; }
  isNeg() { return this.n < 0n; }
  eq(o) { o = Rat.of(o); return this.n === o.n && this.d === o.d; }
  toString() { return this.d === 1n ? `${this.n}` : `${this.n}/${this.d}`; }
  /** LaTeX-ish pretty form used by the chain renderer. */
  toDisplay() { return this.toString(); }
}

/** x + s·y for canonical Rats x, y and s = ±1n (Knuth 4.5.1). */
function addSigned(x, y, s) {
  if (y.n === 0n) return x;
  if (x.n === 0n) return s === 1n ? y : y.neg();
  if (x.d === y.d) {                                   // integers, or a shared denominator
    if (x.d === 1n) return new Rat(x.n + s * y.n, 1n, REDUCED);
    return new Rat(x.n + s * y.n, x.d);                // the sum may share a factor with d
  }
  const g = bgcd(x.d, y.d);
  if (g === 1n) {                                      // coprime denominators: a d + c b over b d is reduced
    const num = x.n * y.d + s * y.n * x.d;
    return num === 0n ? Rat.ZERO : new Rat(num, x.d * y.d, REDUCED);
  }
  const d1 = x.d / g, d2 = y.d / g;                    // gcd(t, d1 d2 g) = gcd(t, g)
  const t = x.n * d2 + s * y.n * d1;
  if (t === 0n) return Rat.ZERO;
  const g2 = bgcd(t, g);
  return g2 === 1n ? new Rat(t, d1 * y.d, REDUCED) : new Rat(t / g2, d1 * (y.d / g2), REDUCED);
}
