// Field interface: { zero, one, add(a,b), sub(a,b), mul(a,b), div(a,b),
//   neg(a), inv(a), eq(a,b), isZero(a), fromInt(n), toDisplay(a), char }
// plus the registry FIELDS of every field the compiler supports (the UI builds
// its chooser from it; the worker resolves message ids through it).
import { Rat } from './rat.js';

export const Q = {
  name: 'ℚ', char: 0,
  zero: Rat.ZERO, one: Rat.ONE,
  add: (a, b) => a.add(b), sub: (a, b) => a.sub(b),
  mul: (a, b) => a.mul(b), div: (a, b) => a.div(b),
  neg: a => a.neg(), inv: a => a.inv(),
  eq: (a, b) => a.eq(b), isZero: a => a.isZero(), isOne: a => a.isOne(),
  fromInt: n => new Rat(BigInt(n)), fromRat: r => r,
  toDisplay: a => a.toString(),
};

// ---------- doubles ----------
const bitlen = v => (v === 0n ? 0 : v.toString(2).length);
/** Correctly rounded double nearest to n/d (BigInt, d != 0). Shared with cgen.js. */
export function ratToDouble(n, d) {
  n = BigInt(n); d = BigInt(d);
  if (d < 0n) { n = -n; d = -d; }
  if (d === 0n) throw new Error('division by zero');
  if (n === 0n) return 0;
  const neg = n < 0n; if (neg) n = -n;
  let k = 66 + bitlen(d) - bitlen(n); if (k < 0) k = 0;
  const num = n << BigInt(k);
  let q = num / d;
  const sticky = (num % d) !== 0n;
  let e = -k;
  const drop = bitlen(q) - 53;
  if (drop > 0) {
    const low = q & ((1n << BigInt(drop)) - 1n);
    const half = 1n << BigInt(drop - 1);
    q >>= BigInt(drop); e += drop;
    if (low > half || (low === half && (sticky || (q & 1n) === 1n))) q += 1n;
    if (q === (1n << 53n)) { q >>= 1n; e += 1; }
  }
  let v = Number(q), ee = e;
  while (ee > 0) { const s = Math.min(ee, 512); v *= 2 ** s; ee -= s; }
  while (ee < 0) { const s = Math.min(-ee, 512); v /= 2 ** s; ee += s; }
  return neg ? -v : v;
}

/** Shortest round-trip decimal of a finite double (JS Number → String: fixed
 *  notation for 1e-6 ≤ |x| < 1e21, scientific otherwise — 0.1, 1e-7, 1.5e+21). */
export function doubleString(x) {
  if (!Number.isFinite(x)) throw new Error(`non-finite constant ${x}`);
  return Object.is(x, -0) ? '0' : String(x);
}

/** n/d to `sig` significant digits in scientific notation, from the exact
 *  rational (used only where no double exists: |n/d| outside the double range). */
function bigSci(n, d, sig) {
  const neg = n < 0n; if (neg) n = -n;
  const pow10 = k => 10n ** BigInt(k);
  const ge = k => (k >= 0 ? n >= d * pow10(k) : n * pow10(-k) >= d);   // n/d ≥ 10^k ?
  let e = n.toString().length - d.toString().length;                    // within ±1 of the true exponent
  while (!ge(e)) e--;
  while (ge(e + 1)) e++;
  const s = sig - 1 - e;                                                // digits = round(n/d · 10^s)
  const num = s >= 0 ? n * pow10(s) : n, den = s >= 0 ? d : d * pow10(-s);
  let q = num / den; if (2n * (num % den) >= den) q += 1n;
  if (q === pow10(sig)) { q /= 10n; e += 1; }
  const ds = q.toString().replace(/0+$/, '');
  return `${neg ? '-' : ''}${ds.length > 1 ? ds[0] + '.' + ds.slice(1) : ds}e${e < 0 ? '-' : '+'}${Math.abs(e)}`;
}

/** The rational n/d displayed as a double: the shortest decimal that round-trips
 *  to the correctly rounded double (0.1, -1.5, 1e-7, 1.5e+21). Where no double
 *  exists (overflow, or underflow to 0 of a nonzero value) the exact value is
 *  written to 17 significant digits instead. */
export function ratToDoubleString(n, d) {
  n = BigInt(n); d = BigInt(d);
  if (d < 0n) { n = -n; d = -d; }
  if (d === 0n) throw new Error('division by zero');
  if (n === 0n) return '0';
  const x = ratToDouble(n, d);
  return Number.isFinite(x) && x !== 0 ? doubleString(x) : bigSci(n, d, 17);
}

/** ℝ (double): the exact rational arithmetic of ℚ — preprocessing is exact —
 *  whose elements are displayed (and emitted in C) as doubles. Only that
 *  rounding of the constants is approximate, hence the ≈ numeric status. */
export const R = {
  ...Q, name: 'ℝ', real: true,
  toDisplay: a => { const r = Rat.of(a); return ratToDoubleString(r.n, r.d); },
};

// Default irreducible moduli over F_2 (bit patterns incl. top bit), low weight.
const DEFAULT_MOD = {
  1: 0b11n, 2: 0b111n, 3: 0b1011n, 4: 0b10011n, 5: 0b100101n,
  6: 0b1000011n, 7: 0b10000011n, 8: 0b100011011n, // AES
  16: (1n << 16n) | 0b101011n,                    // x^16+x^5+x^3+x+1
  32: (1n << 32n) | 0b10001101n,                  // x^32+x^7+x^3+x^2+1
  64: (1n << 64n) | 0b11011n,                     // x^64+x^4+x^3+x+1
  128: (1n << 128n) | 0b10000111n,                // x^128+x^7+x^2+x+1
};

export const MERSENNE61 = (1n << 61n) - 1n;
export const MERSENNE89 = (1n << 89n) - 1n;
export const MERSENNE127 = (1n << 127n) - 1n;

/** Display name of GF(p): Mersenne primes as GF(2^k−1). */
export function primeName(p) {
  return ((p + 1n) & p) === 0n ? `GF(2^${(p + 1n).toString(2).length - 1}−1)` : `GF(${p})`;
}

export function Fp(p) {
  const norm = a => ((a % p) + p) % p;
  const powm = (a, e) => { let r = 1n, b = norm(a); while (e) { if (e & 1n) r = (r * b) % p; b = (b * b) % p; e >>= 1n; } return r; };
  const inv = a => { a = norm(a); if (a === 0n) throw new Error('inverse of 0'); return powm(a, p - 2n); };
  return {
    name: primeName(p), char: Number(p % 1000000n) /* display only */, p,
    zero: 0n, one: 1n,
    add: (a, b) => (a + b) % p, sub: (a, b) => norm(a - b),
    mul: (a, b) => (a * b) % p, div: (a, b) => (a * inv(b)) % p,
    neg: a => norm(-a), inv,
    eq: (a, b) => a === b, isZero: a => a === 0n, isOne: a => a === 1n,
    fromInt: n => norm(BigInt(n)),
    fromRat: r => (norm(r.n) * inv(norm(r.d))) % p,
    toDisplay: a => a.toString(),
  };
}

export function GF2k(k, mod = DEFAULT_MOD[k]) {
  if (!mod) throw new Error(`no default modulus for GF(2^${k}); supply one`);
  const clmul = (a, b) => {          // carryless multiply
    let r = 0n;
    while (b) { if (b & 1n) r ^= a; a <<= 1n; b >>= 1n; }
    return r;
  };
  // reduction by folding: x^k ≡ mlow (mod mod), so v = lo + hi·x^k ≡ lo + hi·mlow;
  // mlow is sparse for every default modulus, so each fold is a few shifts/xors
  const kk = BigInt(k), mask = (1n << kk) - 1n, mlow = mod ^ (1n << kk);
  const mlowShifts = [];
  for (let i = 0n, m = mlow; m; i++, m >>= 1n) if (m & 1n) mlowShifts.push(i);
  const reduce = v => {
    let hi = v >> kk;
    while (hi) {
      v &= mask;
      for (const s of mlowShifts) v ^= hi << s;
      hi = v >> kk;
    }
    return v;
  };
  const mul = (a, b) => reduce(clmul(a, b));
  const inv = a => {                 // extended Euclid in F_2[x]
    if (a === 0n) throw new Error('inverse of 0');
    let [r0, r1, s0, s1] = [mod, a, 0n, 1n];
    while (r1) {
      const shift = bitlen(r0) - bitlen(r1);
      if (shift < 0) { [r0, r1, s0, s1] = [r1, r0, s1, s0]; continue; }
      r0 ^= r1 << BigInt(shift); s0 ^= s1 << BigInt(shift);
    }
    if (r0 !== 1n) throw new Error('modulus not irreducible');
    return reduce(s0);
  };
  const sq = a => mul(a, a);
  const powf = (a, e) => { let r = 1n, b = a; e = BigInt(e);
    while (e) { if (e & 1n) r = mul(r, b); b = mul(b, b); e >>= 1n; } return r; };
  const rootPow2 = (a, t) => {           // unique 2^t-th root: square (k - t) times
    t = ((t % k) + k) % k;
    if (t === 0) return a;
    let r = a; for (let i = 0; i < k - t; i++) r = sq(r); return r;
  };
  return {
    name: `GF(2^${k})`, char: 2, k, mod, sq, pow: powf, rootPow2,
    zero: 0n, one: 1n,
    add: (a, b) => a ^ b, sub: (a, b) => a ^ b,
    mul, div: (a, b) => mul(a, inv(b)),
    neg: a => a, inv,
    eq: (a, b) => a === b, isZero: a => a === 0n, isOne: a => a === 1n,
    fromInt: n => reduce(BigInt(n)),
    toDisplay: a => (a > 15n ? '0x' + a.toString(16) : a.toString()),
  };
}

// ---------- registry ----------
const SUP = { 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
const sup = n => String(n).split('').map(d => SUP[d]).join('');

/** Groups offered by the field chooser, in display order: exact preprocessing
 *  (ℚ, and ℝ — the same exact chain with its constants rounded to doubles), the
 *  Mersenne-prime fields of polynomial hashing, and the carry-less binary fields.
 *  `title` is the caption's hover text. */
export const FIELD_GROUPS = [
  { id: 'exact',    label: 'exact',
    title: 'exact rational preprocessing: ℚ keeps the constants as fractions, ℝ shows and emits them as doubles' },
  { id: 'mersenne', label: 'Mersenne primes',
    title: 'prime fields GF(2^k − 1) with fast modular reduction, as in polynomial hashing' },
  { id: 'binary',   label: 'binary fields',
    title: 'carry-less binary fields GF(2^k), as in carry-less (CLMUL) hashing' },
];

const mersenne = bits => ({
  id: `p${bits}`, group: 'mersenne', lane: 'char0', char: 'p', bits,
  prime: (1n << BigInt(bits)) - 1n,
  label: `2${sup(bits)}−1`, labelHtml: `2<sup>${bits}</sup>−1`, name: `GF(2^${bits}−1)`,
  status: 'exact', exact: true, cCode: true,
  make: () => Fp((1n << BigInt(bits)) - 1n),
});
const binary = k => ({
  id: `gf${k}`, group: 'binary', lane: 'char2', char: 2, bits: k, k,
  label: `GF(2${sup(k)})`, labelHtml: `GF(2<sup>${k}</sup>)`, name: `GF(2^${k})`,
  status: 'exact', exact: true, cCode: true,
  make: () => GF2k(k),
});

/**
 * Every field the compiler supports. Each descriptor:
 *   id        message id (worker `fieldMode`; also the cgen mode)
 *   label     chooser text (short; Unicode superscripts — the Mersenne group's caption
 *             supplies the GF(…) context: '2⁶¹−1'), labelHtml (with <sup>), name (as in results)
 *   group     key into FIELD_GROUPS;  lane 'char0' | 'char2' (which parser/compiler)
 *   char      0 (ℚ, ℝ), 2 (binary), or 'p' (prime field; see .prime and .bits)
 *   status    'exact' | '≈ numeric';  exact  boolean;  cCode  whether C is rendered
 *   worker    the message fields the UI sends;  make()  the js/field.js field object
 */
export const FIELDS = [
  { id: 'Q', group: 'exact', lane: 'char0', char: 0, bits: null, prime: null,
    label: 'ℚ', labelHtml: 'ℚ', name: 'ℚ', status: 'exact', exact: true, cCode: true, make: () => Q },
  // ℝ: preprocessing is exact (as ℚ); the constants are shown and emitted as doubles
  { id: 'R', group: 'exact', lane: 'char0', char: 0, bits: 53, prime: null,
    label: 'ℝ', labelHtml: 'ℝ', name: 'ℝ', status: '≈ numeric', exact: false, cCode: true, make: () => R },
  mersenne(61), mersenne(89), mersenne(127),
  binary(32), binary(64), binary(128),
].map(f => Object.freeze({ ...f, worker: Object.freeze({ lane: f.lane, fieldMode: f.id }) }));

export const FIELD_IDS = FIELDS.map(f => f.id);

/** Descriptor by id; throws on unknown ids. */
export function fieldById(id) {
  const f = FIELDS.find(f => f.id === id);
  if (!f) throw new Error(`unknown field '${id}' (known: ${FIELD_IDS.join(', ')})`);
  return f;
}

/**
 * Resolve a worker message's (lane, fieldMode) to a descriptor. Accepts the
 * registry ids and the legacy spellings: lane 'char2' with a null fieldMode
 * (GF(2^64)); lane 'char0' with 'p' (GF(2^89−1)) or a missing mode (ℚ).
 */
export function resolveField(lane, fieldMode) {
  if (fieldMode === 'p') fieldMode = 'p89';
  if (fieldMode == null || fieldMode === 'gf2k') fieldMode = lane === 'char2' ? 'gf64' : 'Q';
  const f = fieldById(fieldMode);
  if (lane && f.lane !== lane) throw new Error(`field '${f.id}' belongs to lane ${f.lane}, not ${lane}`);
  return f;
}
