// Exact rational arithmetic on BigInt. Immutable value objects.
// Used by the char-0 lane; all decoding is exact (no floats anywhere).

function bgcd(a, b) {
  a = a < 0n ? -a : a; b = b < 0n ? -b : b;
  while (b) { [a, b] = [b, a % b]; }
  return a;
}

export class Rat {
  /** @param {bigint} num @param {bigint} den (den > 0 after normalize) */
  constructor(num, den = 1n) {
    if (den === 0n) throw new Error('division by zero');
    if (den < 0n) { num = -num; den = -den; }
    const g = bgcd(num, den);
    this.n = g ? num / g : 0n;
    this.d = g ? den / g : 1n;
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
  add(o) { o = Rat.of(o); return new Rat(this.n * o.d + o.n * this.d, this.d * o.d); }
  sub(o) { o = Rat.of(o); return new Rat(this.n * o.d - o.n * this.d, this.d * o.d); }
  mul(o) { o = Rat.of(o); return new Rat(this.n * o.n, this.d * o.d); }
  div(o) { o = Rat.of(o); return new Rat(this.n * o.d, this.d * o.n); }
  neg() { return new Rat(-this.n, this.d); }
  inv() { return new Rat(this.d, this.n); }
  isZero() { return this.n === 0n; }
  isOne() { return this.n === 1n && this.d === 1n; }
  isInt() { return this.d === 1n; }
  isNeg() { return this.n < 0n; }
  eq(o) { o = Rat.of(o); return this.n === o.n && this.d === o.d; }
  toString() { return this.d === 1n ? `${this.n}` : `${this.n}/${this.d}`; }
  /** LaTeX-ish pretty form used by the chain renderer. */
  toDisplay() { return this.toString(); }
}
