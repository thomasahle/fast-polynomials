// rat.test.js — js/rat.js against a naive reference: the Lehmer gcd (bgcd)
// must equal BigInt Euclid on every input, and every Rat operation must equal
// the canonical form of the raw-product formula (num/den reduced by the full
// gcd), since add/sub/mul reduce through Knuth's denominator gcds instead.
// Deterministic (seeded) random pairs: 10^5 gcd pairs from 0 to 30k bits with
// negative, zero, equal, divisor, shared-factor and Fibonacci (worst-case
// Euclid) cases, plus 2·10^4 random Rat operation checks.
import { Rat, bgcd, bitlen } from '../js/rat.js';

let fails = 0, checks = 0;
const check = (ok, msg) => { checks++; if (!ok) { fails++; if (fails <= 20) console.log(`FAIL: ${msg}`); } };

// --- reference implementations -------------------------------------------
function euclid(a, b) {
  a = a < 0n ? -a : a; b = b < 0n ? -b : b;
  while (b) { const t = a % b; a = b; b = t; }
  return a;
}
function canon(num, den) {                 // the original constructor's normalisation
  if (den < 0n) { num = -num; den = -den; }
  const g = euclid(num, den);
  return [g ? num / g : 0n, g ? den / g : 1n];
}
const same = (r, [n, d]) => r.n === n && r.d === d;
const isCanonical = r => r.d > 0n && euclid(r.n, r.d) === 1n && (r.n !== 0n || r.d === 1n);

// --- deterministic RNG -----------------------------------------------------
let seed = 0x9e3779b9;
function rnd32() { seed = (Math.imul(seed ^ (seed >>> 15), 0x2c1b3c6d) ^ (seed >>> 12)) >>> 0; seed = (seed + 0x7f4a7c15) >>> 0; return seed; }
function rndBig(bits) {                    // uniform in [0, 2^bits)
  if (bits <= 0) return 0n;
  let x = 0n, left = bits;
  while (left > 0) { const k = Math.min(32, left); x = (x << BigInt(k)) | BigInt(rnd32() >>> (32 - k)); left -= k; }
  return x;
}
const rndSigned = bits => (rnd32() & 1 ? -1n : 1n) * rndBig(bits);
// bit sizes: mostly small and medium, a tail up to 30k bits
function rndBits() {
  const u = rnd32() / 2 ** 32;
  if (u < 0.30) return rnd32() % 64;                  // ≤ 63 bits: the double-Euclid path and its boundary
  if (u < 0.60) return 40 + rnd32() % 200;            // around the head size (one or two Lehmer rounds)
  if (u < 0.90) return 200 + rnd32() % 2000;
  if (u < 0.997) return 2000 + rnd32() % 8000;
  return 10000 + rnd32() % 20001;                     // up to 30k bits
}

// --- bitlen vs toString(2).length: every width to 300, then random and the
// power-of-two boundaries (2^k − 1, 2^k, 2^k + 1) at widths up to 30k ---------
for (let k = 1; k <= 300; k++) {
  for (const x of [(1n << BigInt(k)) - 1n, 1n << BigInt(k), (1n << BigInt(k)) + 1n, (1n << BigInt(k)) | rndBig(k)])
    check(bitlen(x) === x.toString(2).length, `bitlen(2^${k}±…) = ${bitlen(x)} ≠ ${x.toString(2).length}`);
}
for (let i = 0; i < 2000; i++) {
  const k = 1 + rnd32() % 30000;
  const x = i % 3 === 0 ? 1n << BigInt(k) : i % 3 === 1 ? (1n << BigInt(k)) - 1n : (1n << BigInt(k)) | rndBig(k);
  check(bitlen(x) === x.toString(2).length, `bitlen at width ${k}: ${bitlen(x)} ≠ ${x.toString(2).length}`);
}
// the exported helper takes the magnitude: a negative BigInt saturates under >>, which
// used to spin the probe up to BigInt(Infinity) and throw an unrelated RangeError
check(bitlen(0n) === 0, `bitlen(0n) = ${bitlen(0n)} ≠ 0`);
for (const k of [1, 5, 63, 64, 200, 5000]) {
  const x = (1n << BigInt(k)) | 1n;
  check(bitlen(-x) === bitlen(x) && bitlen(-x) === x.toString(2).length, `bitlen(-2^${k}−1) = ${bitlen(-x)} ≠ ${bitlen(x)}`);
}

// --- bgcd vs Euclid ----------------------------------------------------------
const gcdPairs = [];
for (let i = 0; i < 100000; i++) {
  const kind = i % 10, bits = rndBits();
  let a = rndSigned(bits), b;
  switch (kind) {
    case 0: b = 0n; break;                                              // gcd(a, 0) = |a|
    case 1: b = a; break;                                               // equal values
    case 2: b = -a; break;
    case 3: { const q = rndSigned(1 + rnd32() % 100); b = a * q; break; } // one divides the other
    case 4: { const g = rndBig(1 + rnd32() % Math.max(1, bits)); a = a * g; b = rndSigned(bits) * g; break; } // shared factor
    case 5: { const k = Math.min(bits, 1 + rnd32() % 32); b = rndSigned(k); break; }   // very unbalanced sizes
    case 6: { let x = 1n, y = 1n; const steps = 2 + rnd32() % 2000; for (let s = 0; s < steps; s++) { const t = x + y; x = y; y = t; } a = y; b = x; break; } // Fibonacci
    default: b = rndSigned(rndBits());
  }
  gcdPairs.push([a, b]);
}
gcdPairs.push([0n, 0n], [0n, 5n], [-7n, 0n], [1n, 1n], [-1n, 1n], [(1n << 53n) - 1n, (1n << 52n) + 1n],
  [(1n << 100n) - 1n, (1n << 50n) - 1n], [1n << 1000n, 1n << 999n], [(1n << 30000n) - 1n, (1n << 29999n) + 1n]);
let maxBits = 0;
for (const [a, b] of gcdPairs) {
  const g = bgcd(a, b), ref = euclid(a, b);
  check(g === ref, `bgcd(${String(a).slice(0, 30)}…, ${String(b).slice(0, 30)}…) = ${String(g).slice(0, 30)} ≠ ${String(ref).slice(0, 30)}`);
  maxBits = Math.max(maxBits, (a < 0n ? -a : a).toString(2).length);
}
check(maxBits >= 30000, `largest operand ${maxBits} bits (expected ≥ 30000)`);
console.log(`bgcd: ${gcdPairs.length} pairs against Euclid, largest ${maxBits} bits`);

// --- Rat operations vs raw-product canonical form -----------------------------
function rndRat() {
  const u = rnd32() % 8;
  if (u === 0) return Rat.ZERO;
  if (u === 1) return new Rat(rndSigned(1 + rnd32() % 200));                       // integer
  const bits = 1 + rnd32() % (u < 5 ? 64 : 1500);
  const d = rndBig(bits) + 1n;
  if (u === 2) return new Rat(rndSigned(bits), d);
  const g = rndBig(1 + rnd32() % bits) + 1n;                                       // shared factors on purpose
  return new Rat(rndSigned(bits) * g, d * g);
}
const rats = Array.from({ length: 400 }, rndRat);
for (const r of rats) check(isCanonical(r), `constructor canonical ${r}`);
for (let i = 0; i < 20000; i++) {
  const x = rats[rnd32() % rats.length], y = (i % 5 === 0) ? x : rats[rnd32() % rats.length];
  const sum = x.add(y), dif = x.sub(y), prod = x.mul(y);
  check(same(sum, canon(x.n * y.d + y.n * x.d, x.d * y.d)), `add ${x} + ${y} = ${sum}`);
  check(same(dif, canon(x.n * y.d - y.n * x.d, x.d * y.d)), `sub ${x} - ${y} = ${dif}`);
  check(same(prod, canon(x.n * y.n, x.d * y.d)), `mul ${x} * ${y} = ${prod}`);
  check(Object.isFrozen(sum) && Object.isFrozen(prod), 'results frozen');
  if (y.n !== 0n) {
    const quo = x.div(y);
    check(same(quo, canon(x.n * y.d, x.d * y.n)), `div ${x} / ${y} = ${quo}`);
    check(same(y.inv(), canon(y.d, y.n)), `inv ${y}`);
    check(quo.mul(y).eq(x), `(x/y)·y = x for ${x}, ${y}`);
  } else {
    let threw = false; try { x.div(y); } catch (e) { threw = /division by zero/.test(e.message); }
    check(threw, 'div by zero throws');
  }
  check(same(x.neg(), canon(-x.n, x.d)), `neg ${x}`);
  check(sum.sub(y).eq(x), `(x+y)-y = x for ${x}, ${y}`);
  check(x.add(y).eq(y.add(x)) && x.mul(y).eq(y.mul(x)), 'commutative');
}
// integer / mixed-operand paths and the public surface
check(new Rat(6n, -4n).toString() === '-3/2', 'negative denominator normalised');
check(new Rat(0n, 7n).d === 1n && new Rat(0n, -7n).n === 0n, 'zero as 0/1');
check(new Rat(3n).add(4).eq(7n) && Rat.of(2).mul(new Rat(1n, 2n)).isOne(), 'mixed integer operands');
check(new Rat(1n, 6n).add(new Rat(1n, 3n)).toString() === '1/2', '1/6 + 1/3 = 1/2 (shared factor)');
check(new Rat(1n, 6n).add(new Rat(1n, 6n)).toString() === '1/3', '1/6 + 1/6 = 1/3 (equal denominators)');
check(new Rat(2n, 3n).sub(new Rat(2n, 3n)).eq(Rat.ZERO), 'x - x = 0');
check(new Rat(3n, 7n).mul(new Rat(14n, 9n)).toString() === '2/3', 'cross-cancelling multiply');
let threw = false; try { new Rat(1n, 0n); } catch (e) { threw = /division by zero/.test(e.message); }
check(threw, 'den 0 throws');
threw = false; try { Rat.ZERO.inv(); } catch (e) { threw = /division by zero/.test(e.message); }
check(threw, 'inv 0 throws');
check(Rat.ZERO.neg() === Rat.ZERO && Rat.ZERO.isZero() && Rat.ONE.isOne() && Rat.ONE.isInt(), 'constants');

console.log(`rat.test.js: ${checks} checks, ${fails} failures`);
if (fails) process.exit(1);
