// C-code emitters for compiled chains.
//
// The generated C mirrors the C++ that produced the paper's measurements:
//   tools/fast_poly.py            repr_cpp (GF(2^64)) / repr_mersenne_cpp (2^89-1)
//   tools/bench/framework/multiplication.h        lemire_modulo, fast_large_mult_mod,
//                                           extra_large_mult_add_mod
//   tools/bench/framework/multiplication_arm.h    ARM ports of the same helpers
//   tools/bench/framework/fast_hashing.h          lemul   (x86: clmul + Lemire table)
//   tools/bench/framework/fast_hashing_arm.h      slemul  (ARM: clmul + 3-PMULL fold)
// The other fields follow the same shapes: GF(2^32) and GF(2^128) with
// PCLMULQDQ / PMULL partial products and shift-xor folds through their standard
// moduli (GF(2^128) has a two-partial-product square kernel); 2^61-1 in
// 64-bit words with 128-bit products and lazy folds;
// 2^127-1 with 128-bit values (four 64x64 partial products, values kept in
// [0, p]); ℚ and ℝ as doubles (exact chain constants rounded).
// Conventions: a constants table at the top (a[] for GF(2^k) keys, alpha[]
// for characteristic 0), wires named with the appendix letters y, z, t, u, ...
// (tools/polychain.py _WIRE_LETTERS) and a trailing "// y = (x + a0) * (...)"
// comment per gate, aligned as in repr_cpp.
//
// Modes (= field ids of js/field.js FIELDS): 'Q' | 'R' | 'p61' | 'p89' | 'p127'
// for char0C / methodChainC; 'gf32' | 'gf64' | 'gf128' (or 'gf2k': F.k
// decides) for methodChainC; char2C takes the field object. The legacy 'p'
// means 'p89'.
import { Rat } from './rat.js';
import { ratToDouble, MERSENNE61, MERSENNE89, MERSENNE127 } from './field.js';

export { ratToDouble, MERSENNE89 };
/** License of the generated C (one line; the bundle's README repeats it). */
export const C_LICENSE = 'License: 0BSD (BSD Zero Clause) — use, modify and redistribute freely; no attribution required.';
/** Header of every generated C file. */
export const C_PROVENANCE = `/***
 Code generated from https://thomasahle.com/fast-polynomials/
 For details, see "Fast Evaluation of Polynomials with Rational Preprocessing"
 by Thomas Ahle and Jakob Knudsen.
 ${C_LICENSE}
*/`;

// ---------- naming ----------
const WIRE_LETTERS = ['y', 'z', 't', 'u', 'v', 'w', 's', 'r', 'q', 'p',
                      'o', 'm', 'j', 'h', 'g', 'f', 'e', 'd', 'c', 'b'];
/** Appendix-style name of the i-th multiplication output (tools/polychain.py). */
export function wireLetter(i) {
  return i < WIRE_LETTERS.length ? WIRE_LETTERS[i] : `g${i}`;
}
/** Turn a display wire name into a C identifier (P̃ -> Pt). */
export function cIdent(name) {
  return String(name).replace(/̃/g, 't').replace(/[^A-Za-z0-9_]/g, '_');
}

// ---------- number helpers ----------
const TWO53 = 1n << 53n;

/** Shortest round-trip C double literal for a finite double. */
export function doubleLiteral(x) {
  if (!Number.isFinite(x)) throw new Error(`constant ${x} is not representable as a double`);
  if (Object.is(x, -0)) x = 0;
  let s = String(x);
  if (/^-?\d+$/.test(s)) s += '.0';
  return s;
}

const toRat = c => Rat.of(typeof c === 'number' ? BigInt(c) : c);
const toBig = c => (typeof c === 'bigint' ? c : c instanceof Rat ? c.n : BigInt(c));

/** Q constant as C source: cstyle 'float' | 'fraction'. Returns {expr, note}. */
export function qConst(r0, cstyle = 'float') {
  const r = toRat(r0);
  if (cstyle === 'fraction') {
    if (r.d === 1n) return { expr: `${r.n}.0`, note: '' };
    const an = r.n < 0n ? -r.n : r.n;
    if (an < TWO53 && r.d < TWO53)
      return { expr: `(double)${r.n}/${r.d}`, note: '' };
    return { expr: doubleLiteral(ratToDouble(r.n, r.d)),
             note: `${r.n}/${r.d} exceeds 53 bits: rounded` };
  }
  return { expr: doubleLiteral(ratToDouble(r.n, r.d)), note: '' };
}

const hex32 = v => '0x' + toBig(v).toString(16).padStart(8, '0') + 'U';
const hex64 = v => '0x' + toBig(v).toString(16).padStart(16, '0') + 'ULL';
const u128 = v => {
  v = toBig(v);
  return `U128(0x${(v >> 64n).toString(16)}ULL, ${hex64(v & ((1n << 64n) - 1n))})`;
};

/** Right-align trailing `// ...` comments (repr_cpp style). */
function withComments(pairs /* [[code, comment|null], ...] */) {
  const w = Math.max(0, ...pairs.filter(p => p[1]).map(p => p[0].length));
  return pairs.map(([code, cm]) => (cm ? code.padEnd(w + 2) + '// ' + cm : code));
}

// strip one pair of enclosing parentheses when they wrap the whole expression
const unparen = e => {
  if (!e.startsWith('(') || !e.endsWith(')')) return e;
  let d = 0;
  for (let i = 0; i < e.length; i++) {
    if (e[i] === '(') d++; else if (e[i] === ')') d--;
    if (d === 0 && i < e.length - 1) return e;
  }
  return e.slice(1, -1);
};

// ---------- GF(2^k) ----------
const X86_CLMUL = '#if defined(__x86_64__) && defined(__PCLMUL__)';
const ARM_PMULL = '#elif defined(__aarch64__) && (defined(__ARM_FEATURE_AES) || defined(__ARM_FEATURE_CRYPTO))';

/** gf64_mul: x86 = lemul (clmul + Lemire's table reduction), ARM = slemul
 *  (clmul + 3-PMULL fold). No portable fallback: #error elsewhere. */
export function gf64Header() {
  return [
    '#include <stdint.h>',
    '',
    '/* GF(2^64) = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1); r = 27 = x^4+x^3+x+1 */',
    '#if defined(__x86_64__) && defined(__PCLMUL__) && defined(__SSSE3__)',
    '#include <immintrin.h>',
    '/* Lemire--Kaser, "Faster 64-bit universal hashing using carry-less',
    '   multiplications": one CLMUL plus a 16-byte lookup table. */',
    'static inline uint64_t gf64_mul(uint64_t a, uint64_t b) {',
    '    __m128i ab = _mm_clmulepi64_si128(_mm_cvtsi64_si128((long long)a),',
    '                                      _mm_cvtsi64_si128((long long)b), 0x00);',
    '    __m128i r = _mm_cvtsi64_si128(27);',
    '    __m128i xr = _mm_clmulepi64_si128(ab, r, 0x01);   /* ab[high] * r */',
    '    /* Constant 16-byte lookup instead of the second multiplication.  The',
    '       initializer is compile-time data: optimizing compilers hoist/load it. */',
    '    __m128i table = _mm_setr_epi8(0, 27, 54, 45, 108, 119, 90, 65, (char)216,',
    '                                  (char)195, (char)238, (char)245, (char)180,',
    '                                  (char)175, (char)130, (char)153);',
    '    __m128i zr = _mm_shuffle_epi8(table, _mm_srli_si128(xr, 8));',
    '    return (uint64_t)_mm_cvtsi128_si64(_mm_xor_si128(_mm_xor_si128(ab, xr), zr));',
    '}',
    ARM_PMULL,
    '#include <arm_neon.h>',
    '/* PMULL implementation from "Fast Evaluation of Polynomials with Rational',
    '   Preprocessing": multiply once, then fold twice through x^64 = r. */',
    'static inline uint64_t gf64_mul(uint64_t a, uint64_t b) {',
    '    const poly64_t r = (poly64_t)27;',
    '    uint64x2_t ab = vreinterpretq_u64_p128(vmull_p64((poly64_t)a, (poly64_t)b));',
    '    uint64x2_t xr = vreinterpretq_u64_p128(vmull_p64((poly64_t)vgetq_lane_u64(ab, 1), r));',
    '    uint64x2_t zr = vreinterpretq_u64_p128(vmull_p64((poly64_t)vgetq_lane_u64(xr, 1), r));',
    '    return vgetq_lane_u64(veorq_u64(veorq_u64(ab, xr), zr), 0);',
    '}',
    '#else',
    '#error "gf64_mul needs carry-less multiplication: x86 -mpclmul -mssse3, ARM -march=armv8-a+crypto"',
    '#endif',
  ].join('\n');
}

/** gf32_mul: one PCLMULQDQ / PMULL for the 64-bit product, then two shift-xor
 *  folds of the upper word through x^32 = x^7 + x^3 + x^2 + 1. */
export function gf32Header() {
  return [
    '#include <stdint.h>',
    '',
    '/* GF(2^32) = GF(2)[x] / (x^32 + x^7 + x^3 + x^2 + 1); r = 0x8d = x^7+x^3+x^2+1 */',
    X86_CLMUL,
    '#include <immintrin.h>',
    '/* 64-bit carry-less product of two 32-bit words (PCLMULQDQ) */',
    'static inline uint64_t clmul32(uint32_t a, uint32_t b) {',
    '    __m128i ab = _mm_clmulepi64_si128(_mm_cvtsi64_si128((long long)a),',
    '                                      _mm_cvtsi64_si128((long long)b), 0x00);',
    '    return (uint64_t)_mm_cvtsi128_si64(ab);',
    '}',
    ARM_PMULL,
    '#include <arm_neon.h>',
    '/* 64-bit carry-less product of two 32-bit words (PMULL) */',
    'static inline uint64_t clmul32(uint32_t a, uint32_t b) {',
    '    return vgetq_lane_u64(vreinterpretq_u64_p128(vmull_p64((poly64_t)a, (poly64_t)b)), 0);',
    '}',
    '#else',
    '#error "gf32_mul needs carry-less multiplication: x86 -mpclmul, ARM -march=armv8-a+crypto"',
    '#endif',
    '/* a*b in GF(2^32): the product\'s upper word is folded twice through x^32 = r */',
    '/* Unlike GF(2^64), the residual has seven bits; one 16-entry byte shuffle',
    '   cannot encode it.  The two sparse shift/XOR folds avoid extra tables. */',
    'static inline uint32_t gf32_mul(uint32_t a, uint32_t b) {',
    '    uint64_t ab = clmul32(a, b);                             /* degree <= 62 */',
    '    uint64_t hi = ab >> 32;',
    '    uint64_t xr = hi ^ (hi << 2) ^ (hi << 3) ^ (hi << 7);    /* hi * r, degree <= 38 */',
    '    uint64_t hi2 = xr >> 32;                                 /* at most 7 bits */',
    '    uint64_t zr = hi2 ^ (hi2 << 2) ^ (hi2 << 3) ^ (hi2 << 7);',
    '    return (uint32_t)(ab ^ xr ^ zr);',
    '}',
  ].join('\n');
}

/** gf128_mul: four PCLMULQDQ / PMULL partial products (schoolbook), the
 *  256-bit product's upper half folded through x^128 = x^7 + x^2 + x + 1. */
export function gf128Header(body = '') {
  const needSquare = body === '' || body.includes('gf128_square(');
  return [
    '#include <stdint.h>',
    '',
    '/* GF(2^128) = GF(2)[x] / (x^128 + x^7 + x^2 + x + 1); r = 0x87 = x^7+x^2+x+1 */',
    '#define U128(hi, lo) ((((__uint128_t)(hi)) << 64) | (__uint128_t)(lo))',
    X86_CLMUL,
    '#include <immintrin.h>',
    '/* 128-bit carry-less product of two 64-bit words (PCLMULQDQ) */',
    'static inline __uint128_t clmul64(uint64_t a, uint64_t b) {',
    '    __m128i ab = _mm_clmulepi64_si128(_mm_cvtsi64_si128((long long)a),',
    '                                      _mm_cvtsi64_si128((long long)b), 0x00);',
    '    return U128((uint64_t)_mm_cvtsi128_si64(_mm_srli_si128(ab, 8)), (uint64_t)_mm_cvtsi128_si64(ab));',
    '}',
    ARM_PMULL,
    '#include <arm_neon.h>',
    '/* 128-bit carry-less product of two 64-bit words (PMULL) */',
    'static inline __uint128_t clmul64(uint64_t a, uint64_t b) {',
    '    uint64x2_t ab = vreinterpretq_u64_p128(vmull_p64((poly64_t)a, (poly64_t)b));',
    '    return U128(vgetq_lane_u64(ab, 1), vgetq_lane_u64(ab, 0));',
    '}',
    '#else',
    '#error "gf128_mul needs carry-less multiplication: x86 -mpclmul, ARM -march=armv8-a+crypto"',
    '#endif',
    '/* Reduce hi*x^128+lo through x^128 = r. */',
    'static inline __uint128_t gf128_reduce(__uint128_t lo, __uint128_t hi) {',
    '    __uint128_t top = (hi >> 127) ^ (hi >> 126) ^ (hi >> 121); /* hi*r above bit 128 */',
    '    __uint128_t red = hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7);  /* hi*r mod x^128 */',
    '    red ^= top ^ (top << 1) ^ (top << 2) ^ (top << 7);         /* top*r, degree <= 13 */',
    '    return lo ^ red;',
    '}',
    ...(needSquare ? [
      '/* Squaring has no cross term in characteristic two, so it needs only two',
      '   64x64 carry-less products rather than the general product\'s four. */',
      'static inline __uint128_t gf128_square(__uint128_t a) {',
      '    uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64);',
      '    return gf128_reduce(clmul64(a0, a0), clmul64(a1, a1));',
      '}',
    ] : []),
    '/* a*b in GF(2^128): four 64x64 partial products.  A three-CLMUL Karatsuba',
    '   product saves one multiply but adds a dependent XOR/extract path; keep',
    '   that as a separately benchmarked kernel rather than assuming it wins. */',
    'static inline __uint128_t gf128_mul(__uint128_t a, __uint128_t b) {',
    '    uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64);',
    '    uint64_t b0 = (uint64_t)b, b1 = (uint64_t)(b >> 64);',
    '    __uint128_t lo = clmul64(a0, b0), hi = clmul64(a1, b1);',
    '    __uint128_t mid = clmul64(a0, b1) ^ clmul64(a1, b0);',
    '    lo ^= mid << 64;',
    '    hi ^= mid >> 64;                                           /* a*b = hi*x^128 + lo */',
    '    return gf128_reduce(lo, hi);',
    '}',
  ].join('\n');
}

// Shared emission is descriptor-driven; only these measured, width-specific
// product/reduction kernels differ. Adding a field is one descriptor plus its
// kernel, not a new Horner/Estrin/paper-chain emitter.
const GF_SPECS = {
  32: { mod: (1n << 32n) | 0b10001101n,
        T: 'uint32_t', mul: 'gf32_mul', header: gf32Header, lit: hex32, inline: v => '0x' + toBig(v).toString(16) + 'U',
        flags: 'x86  cc -O2 -mpclmul ... | ARM  cc -O2 -march=armv8-a+crypto ...' },
  64: { mod: (1n << 64n) | 0b11011n,
        T: 'uint64_t', mul: 'gf64_mul', header: gf64Header, lit: hex64, inline: v => '0x' + toBig(v).toString(16) + 'ULL',
        flags: 'x86  cc -O2 -mpclmul -mssse3 ... | ARM  cc -O2 -march=armv8-a+crypto ...' },
  128: { mod: (1n << 128n) | 0b10000111n,
         T: '__uint128_t', mul: 'gf128_mul', square: 'gf128_square', header: gf128Header, lit: u128, inline: u128,
         flags: 'x86  cc -O2 -mpclmul ... | ARM  cc -O2 -march=armv8-a+crypto ...' },
};
/** Emitter spec for a GF(2^k) field object; throws for unsupported k / moduli. */
function gfSpec(F) {
  const spec = GF_SPECS[F?.k];
  if (!spec) throw new Error(`C generation supports GF(2^32), GF(2^64) and GF(2^128) (got ${F?.name ?? F})`);
  if (F.mod !== spec.mod) throw new Error(`C generation for GF(2^${F.k}) needs the standard modulus`);
  return { ...spec, k: F.k };
}
/** Header for a GF(2^k) field (k = 32, 64, 128). */
export function gfHeader(F) {
  return gfSpec(F).header();
}

/** Self-contained C for a char-2 gate circuit with concrete keys (repr_cpp style).
 *  lift: the constant term c0 of the paper's even lift P = x · P_{n-1} + c0 (the
 *  circuit then computes the odd part P_{n-1}; c0 is emitted as the last key);
 *  scaleBy: the leading coefficient of a non-monic input (one more multiplication). */
export function char2C(F, spec, keys, { scaleBy = null, lift = null, name = 'eval_P' } = {}) {
  const G = gfSpec(F);
  const nk = spec.keys ?? keys.length;
  const lifted = lift !== null;
  const deg = spec.n + (lifted ? 1 : 0);              // degree of the evaluated polynomial
  const nkeys = nk + (lifted ? 1 : 0);                 // the lift constant is key a_{n-1}
  const mults = spec.gates.length + (lifted ? 1 : 0) + (scaleBy !== null ? 1 : 0);
  const cFactor = f => [...f.t, ...(f.k !== null ? [`a[${f.k}]`] : [])].join(' ^ ');
  const mFactor = f => {
    const parts = [...f.t, ...(f.k !== null ? [`a${f.k}`] : [])];
    return parts.length > 1 ? `(${parts.join(' + ')})` : parts[0];
  };
  const L = [C_PROVENANCE];
  const usesSquare = !!G.square && spec.gates.some(g => cFactor(g.l) === cFactor(g.r));
  L.push(`/* P(x) over GF(2^${G.k}): ${mults} multiplications` +
         ` (Horner: ${deg - 1}), ${nkeys} key${nkeys === 1 ? '' : 's'} a_0..a_${nkeys - 1}. */`);
  L.push('/* Kernel conventions follow "Fast Evaluation of Polynomials with Rational');
  L.push(`   Preprocessing". Compile: ${G.flags} */`);
  L.push(...G.header(usesSquare ? `${G.square}(` : 'no square').split('\n'));
  L.push('');
  L.push(`/* keys (the appendix's a_i${lifted ? `; a${nk} is the constant term of the even-degree lift` : ''}) */`);
  L.push(`static const ${G.T} a[${nkeys}] = {`);
  const table = Array.from({ length: nk }, (_, i) => [`    ${G.lit(keys[i])},`, `a${i}`]);
  if (lifted) table.push([`    ${G.lit(lift)},`, `a${nk} (even-degree lift)`]);
  L.push(...withComments(table));
  L.push('};');
  L.push('');
  L.push(`${G.T} ${name}(${G.T} x) {`);
  const body = [];
  for (const g of spec.gates) {
    const left = cFactor(g.l), right = cFactor(g.r);
    const product = G.square && left === right ? `${G.square}(${left})` : `${G.mul}(${left}, ${right})`;
    body.push([`    ${G.T} ${g.w} = ${product};`, `${g.w} = ${mFactor(g.l)} * ${mFactor(g.r)}`]);
  }
  const o = spec.out;
  const core = lifted ? `P_${spec.n}` : 'P';           // the odd part P_{n-1} when lifted
  body.push([`    ${G.T} ${core} = ${cFactor(o)};`,
             `${core} = ${[...o.t, ...(o.k !== null ? [`a${o.k}`] : [])].join(' + ')}`]);
  if (lifted)
    body.push([`    ${G.T} P = ${G.mul}(x, ${core}) ^ a[${nk}];`,
               `P = x * ${core} + a${nk}   (even-degree lift)`]);
  L.push(...withComments(body));
  if (scaleBy !== null)
    L.push(`    return ${G.mul}(P, ${G.lit(scaleBy)});  /* leading coefficient */`);
  else L.push('    return P;');
  L.push('}');
  return L.join('\n');
}

// ---------- Mersenne primes ----------
const MERSENNE_FOLD_NOTE = [
  '/* Common reduction principle: 2^b = 1 (mod 2^b-1), following the',
  '   branch-free Mersenne-prime treatment of Ahle, Knudsen & Thorup,',
  '   "The Power of Hashing with Mersenne Primes" (2020).  The safe lazy',
  '   range and limb schedule below remain specific to each word width. */',
];

/** 2^89-1 helpers, transcribed to C from tools/bench/framework/multiplication.h
 *  (identical in multiplication_arm.h). Lazy reduction: results are < 2p.
 *  Only the helpers actually referenced by `body` are emitted. */
export function mersenneHeader(body = '') {
  const need = fn => body === '' || body.includes(fn + '(');
  const L = [
    '#include <stdint.h>',
    '',
    ...MERSENNE_FOLD_NOTE,
    '/* p = 2^89 - 1.  Values are kept lazily reduced (< 2p) between gates,',
    '   as in "Fast Evaluation of Polynomials with Rational Preprocessing." */',
    '#define M89 ((((__uint128_t)1) << 89) - 1)',
    '#define U128(hi, lo) ((((__uint128_t)(hi)) << 64) | (__uint128_t)(lo))',
  ];
  if (need('fast_large_mult_mod_2')) L.push(
    '',
    '/* (a*x + b) mod p, approximately: assumes a, b < 2^c p (c < 7), returns < 2p. */',
    'static inline __uint128_t fast_large_mult_mod(__uint128_t a, __uint128_t b, uint64_t x) {',
    '    __uint128_t mul_low = (__uint128_t)(uint64_t)a * (__uint128_t)x;',
    '    __uint128_t mul_high = (__uint128_t)(uint64_t)(a >> 64) * (__uint128_t)x;',
    '    __uint128_t c = mul_low + (__uint128_t)(uint64_t)b;',
    '    __uint128_t d = mul_high + (b >> 64) + (c >> 64);',
    '    return ((d & (((uint64_t)1 << 25) - 1)) << 64) + (d >> 25) + (uint64_t)c;',
    '}',
    '/* a*x mod p (x a 64-bit word), returns < 2p. */',
    'static inline __uint128_t fast_large_mult_mod_2(__uint128_t a, uint64_t x) {',
    '    return fast_large_mult_mod(a, 0, x);',
    '}');
  if (need('extra_large_mult_mod')) L.push(
    '',
    '/* (a*b + d) mod p, approximately: assumes a, b < 2^c p with c < 7 and',
    '   returns a value < p + 4 + 2^c. */',
    '/* Tuned 64+25-bit a*b+d kernel for p = 2^89 - 1. */',
    'static inline __uint128_t extra_large_mult_add_mod(__uint128_t a, __uint128_t b, __uint128_t d) {',
    '    uint64_t a_lo = (uint64_t)a;',
    '    uint64_t b_lo = (uint64_t)b;',
    '    uint32_t a_hi = (uint32_t)(a >> 64);',
    '    uint32_t b_hi = (uint32_t)(b >> 64);',
    '    __uint128_t mul_low = (__uint128_t)a_lo * b_lo;',
    '    __uint128_t mul_mid0 = (__uint128_t)a_hi * b_lo;',
    '    __uint128_t mul_mid1 = (__uint128_t)a_lo * b_hi;',
    '    uint64_t mul_high = (uint64_t)a_hi * b_hi;',
    '',
    '    __uint128_t mid = mul_mid0 + mul_mid1 + (mul_low >> 64);',
    '    mul_high += (uint64_t)(mid >> 64);',
    '',
    '    uint64_t mask25 = ((uint64_t)1 << 25) - 1;',
    '',
    '    __uint128_t new_low = (uint64_t)mul_low;',
    '    new_low += (uint64_t)mid >> 25;',
    '    new_low += (__uint128_t)(mul_high & mask25) << 39;',
    '    new_low += d;',
    '',
    '    uint64_t new_high = (uint64_t)mid & mask25;',
    '    new_high += mul_high >> 25;',
    '    new_high += (uint64_t)(new_low >> 64);',
    '',
    '    __uint128_t total = (uint64_t)new_low;',
    '    total += (__uint128_t)(new_high & mask25) << 64;',
    '    total += new_high >> 25;',
    '    return total;',
    '}',
    'static inline __uint128_t extra_large_mult_mod(__uint128_t a, __uint128_t b) {',
    '    return extra_large_mult_add_mod(a, b, 0);',
    '}');
  if (need('reduce89')) L.push(
    '',
    '/* full reduction of any 128-bit value into [0, p) */',
    'static inline __uint128_t reduce89(__uint128_t a) {',
    '    a = (a & M89) + (a >> 89);',
    '    return a >= M89 ? a - M89 : a;',
    '}');
  return L.join('\n');
}

/** 2^61-1 helpers: 64-bit words, 128-bit products, lazy folds (2^61 = 1 mod p). */
export function mersenne61Header() {
  return [
    '#include <stdint.h>',
    '',
    ...MERSENNE_FOLD_NOTE,
    '/* p = 2^61 - 1.  Values are kept lazily reduced (below 2^61 + 8) between',
    '   gates: 2^61 = 1 (mod p), so folding the bits above bit 61 back in reduces',
    '   without a division.  Products use one 64x64 -> 128-bit multiply and two folds. */',
    '#define M61 (((uint64_t)1 << 61) - 1)',
    '/* any 64-bit value -> [0, 2^61 + 7] */',
    'static inline uint64_t fold61(uint64_t a) { return (a & M61) + (a >> 61); }',
    '/* a*b mod p for a, b < 2^62 + 16 (two lazily reduced values, or their sum); result < 2^61 + 6 */',
    'static inline uint64_t mul61(uint64_t a, uint64_t b) {',
    '    __uint128_t ab = (__uint128_t)a * b;',
    '    uint64_t r = (uint64_t)(ab & M61) + (uint64_t)(ab >> 61);',
    '    return fold61(r);',
    '}',
  ].join('\n');
}

/** 2^127-1 helpers: 128-bit values in [0, p], four 64x64 partial products. */
export function mersenne127Header(body = '') {
  const needSub = body === '' || body.includes('sub127(');
  return [
    '#include <stdint.h>',
    '',
    ...MERSENNE_FOLD_NOTE,
    '/* p = 2^127 - 1.  The general multiplier requires canonical operands, so',
    '   this kernel keeps values in [0, p] (p itself may stand for 0), folds each',
    '   addition via 2^127 = 1 (mod p). Products use four 64x64-bit partial',
    '   products (schoolbook) and are folded twice. */',
    '#define M127 ((((__uint128_t)1) << 127) - 1)',
    '#define U128(hi, lo) ((((__uint128_t)(hi)) << 64) | (__uint128_t)(lo))',
    '/* a <= 2p -> [0, p] */',
    'static inline __uint128_t fold127(__uint128_t a) { return (a & M127) + (a >> 127); }',
    '/* a, b <= p */',
    'static inline __uint128_t add127(__uint128_t a, __uint128_t b) { return fold127(a + b); }',
    ...(needSub ? ['static inline __uint128_t sub127(__uint128_t a, __uint128_t b) { return fold127(a + (M127 - b)); }'] : []),
    'static inline __uint128_t mul127(__uint128_t a, __uint128_t b) {',
    '    uint64_t a0 = (uint64_t)a, a1 = (uint64_t)(a >> 64);',
    '    uint64_t b0 = (uint64_t)b, b1 = (uint64_t)(b >> 64);',
    '    __uint128_t ll = (__uint128_t)a0 * b0, lh = (__uint128_t)a0 * b1;',
    '    __uint128_t hl = (__uint128_t)a1 * b0, hh = (__uint128_t)a1 * b1;',
    '    __uint128_t mid = lh + hl;                         /* no overflow: a1, b1 < 2^63 */',
    '    __uint128_t lo = ll + (mid << 64);',
    '    __uint128_t hi = hh + (mid >> 64) + (lo < ll);     /* a*b = hi*2^128 + lo */',
    '    /* 2^128 = 2 (mod p): fold to at most 2p, then into [0, p] */',
    '    return fold127(((hi << 1) | (lo >> 127)) + (lo & M127));',
    '}',
  ].join('\n');
}

// Op-sets for the prime fields. Every value is a triple [expr, bound, isBareX];
// `bound` counts "units" of the field's lazy range (see each header).
//   multiple(name, k, isX) -> [expr, bound]   k*name (k >= 1)
//   neg(expr, bound)       -> [expr, bound]
//   mul(a, b)              -> triple
//   fold(parts)            -> triple, parts = [{neg, v: [expr, bound]}]
//   clampOut(triple)       -> triple safe to store in T
//   entry / finish(out)    -> lines at function start / before `return out`
const LAZY_LIMIT = 63;   // 2^89-1: extra_large_mult_mod needs operands < 2^6 p
const PRIME_OPS = {
  p89: {
    prime: MERSENNE89, macro: 'M89', T: '__uint128_t', xT: 'uint64_t', lit: u128,
    banner: 'GF(p), p = 2^89 - 1',
    intro: ['/* Kernel conventions follow "Fast Evaluation of Polynomials with Rational',
            '   Preprocessing"; x is a 64-bit word as in the hashing experiments. */'],
    header: body => mersenneHeader(body),
    // x is a uint64_t parameter: an integer multiple must be widened first,
    // otherwise k*x wraps modulo 2^64 for x >= 2^63 (wires are already 128-bit).
    multiple: (nm, k, isX) => (k === 1 ? [nm, isX ? 1 : 2]
                                       : [isX ? `${k}*(__uint128_t)x` : `${k}*${nm}`, k * (isX ? 1 : 2)]),
    neg: (e, B) => [`(${B === 1 ? '' : B + '*'}M89 - ${e})`, B],
    mul: (a, b) => {
      const clamp = t => (t[1] > LAZY_LIMIT ? [`reduce89(${unparen(t[0])})`, 1, false] : [unparen(t[0]), t[1], t[2]]);
      a = clamp(a); b = clamp(b);
      if (b[2]) return [`fast_large_mult_mod_2(${a[0]}, x)`, 2, false];
      if (a[2]) return [`fast_large_mult_mod_2(${b[0]}, x)`, 2, false];
      return [`extra_large_mult_mod(${a[0]}, ${b[0]})`, 2, false];
    },
    fold(parts) {
      let B = 0; const out = [];
      for (const p of parts) { out.push(p.neg ? this.neg(p.v[0], p.v[1])[0] : p.v[0]); B += p.v[1]; }
      return [out.join(' + '), B, false];
    },
    clampOut: v => (v[1] > LAZY_LIMIT ? [`reduce89(${v[0]})`, 1, false] : v),
    wireBound: 2, xBound: 1, entry: [],
    finish: out => [`    ${out} = (${out} & M89) + (${out} >> 89);`, `    if (${out} >= M89) ${out} -= M89;`],
    scale: (out, c) => `    ${out} = extra_large_mult_mod(${out}, ${u128(c)});  /* leading coefficient */`,
  },
  p61: {
    prime: MERSENNE61, macro: 'M61', T: 'uint64_t', xT: 'uint64_t', lit: hex64,
    banner: 'GF(p), p = 2^61 - 1',
    intro: ['/* 64-bit words with lazy reduction (values stay below 2^61 + 8 between gates);',
            '   the input x is any 64-bit word, folded once on entry. */'],
    header: () => mersenne61Header(),
    // units: values < 2^61 + 8; sums of <= 7 units fit in 64 bits, products need <= 2 units per operand
    multiple: (nm, k) => (k === 1 ? [nm, 1] : k <= 7 ? [`${k}*${nm}`, k] : [`mul61(${nm}, ${k})`, 1]),
    neg: (e, B) => [`(${B + 1}*M61 - ${e})`, B + 1],
    mul: (a, b) => {
      const clamp = t => (t[1] > 2 ? [`fold61(${unparen(t[0])})`, 1, false] : [unparen(t[0]), t[1], t[2]]);
      a = clamp(a); b = clamp(b);
      return [`mul61(${a[0]}, ${b[0]})`, 1, false];
    },
    fold(parts) {
      let expr = null, B = 0;
      for (const p of parts) {
        let [e, b] = p.v;
        if (p.neg) [e, b] = this.neg(e, b);
        if (expr === null) { expr = e; B = b; continue; }
        if (B + b > 7) { expr = `fold61(${expr})`; B = 1; }
        expr = `${expr} + ${e}`; B += b;
      }
      return [expr, B, false];
    },
    clampOut: v => v,
    wireBound: 1, xBound: 1, entry: ['    x = fold61(x);'],
    finish: out => [`    ${out} = fold61(${out});`, `    if (${out} >= M61) ${out} -= M61;`],
    scale: (out, c) => `    ${out} = mul61(fold61(${out}), ${hex64(c)});  /* leading coefficient */`,
  },
  p127: {
    prime: MERSENNE127, macro: 'M127', T: '__uint128_t', xT: '__uint128_t', lit: u128,
    banner: 'GF(p), p = 2^127 - 1',
    intro: ['/* 128-bit values kept in [0, p]; every addition folds once (add127 / sub127),',
            '   products are four 64x64 partial products (mul127); x is any 128-bit word. */'],
    header: body => mersenne127Header(body),
    multiple: (nm, k) => (k === 1 ? [nm, 1] : k === 2 ? [`add127(${nm}, ${nm})`, 1]
                          : k === 3 ? [`add127(add127(${nm}, ${nm}), ${nm})`, 1] : [`mul127(${nm}, ${k})`, 1]),
    neg: e => [`(M127 - ${e})`, 1],
    mul: (a, b) => [`mul127(${unparen(a[0])}, ${unparen(b[0])})`, 1, false],
    fold(parts) {
      let expr = null;
      for (const p of parts) {
        const e = unparen(p.v[0]);
        if (expr === null) { expr = p.neg ? this.neg(e)[0] : e; continue; }
        expr = `${p.neg ? 'sub127' : 'add127'}(${unparen(expr)}, ${e})`;
      }
      return [expr, 1, false];
    },
    clampOut: v => v,
    wireBound: 1, xBound: 1, entry: ['    x = fold127(fold127(x));'],
    finish: out => [`    if (${out} >= M127) ${out} -= M127;`],
    scale: (out, c) => `    ${out} = mul127(${out}, ${u128(c)});  /* leading coefficient */`,
  },
};
const primeOps = mode => {
  const ops = PRIME_OPS[mode === 'p' ? 'p89' : mode];
  if (!ops) throw new Error(`unknown Mersenne mode ${mode}`);
  return ops;
};
/** Mode id for a prime (2^61-1, 2^89-1, 2^127-1) or null. */
export function mersenneMode(p) {
  for (const [id, ops] of Object.entries(PRIME_OPS)) if (ops.prime === p) return id;
  return null;
}

// ---------- affine-form chains (char 0) ----------
const entriesOf = t => (t instanceof Map ? [...t.entries()] : Object.entries(t).map(([a, b]) => [Number(a), b]))
  .filter(([, k]) => k !== 0).sort((a, b) => a[0] - b[0]);
const isZeroConst = c => (c instanceof Rat ? c.isZero() : (typeof c === 'number' ? c === 0 : toBig(c) === 0n));

const DOUBLE_NOTE = [
  '/* Estrin layers leave independent multiply-adds visible to the compiler.',
  '   Compile with gcc/clang -O3 -march=native (MSVC: /O2); optionally test',
  '   -ffp-contract=fast (/fp:contract) for more aggressive FMA/auto-SLP. */',
].join('\n');

/** C for a char-0 PolynomialChain. mode: 'Q' | 'R' (doubles: the exact chain
 *  constants rounded — the same code, ℝ differs only in its banner),
 *  'p61' | 'p89' | 'p127' (Mersenne primes; 'p' = 'p89').
 *  cstyle (Q only): 'float' | 'fraction'. */
export function char0C(chain, mode, { scaleBy = null, cstyle = 'float', name = 'eval_P' } = {}) {
  if (mode === 'p') mode = 'p89';
  const wnames = chain.wire_names ?? [];
  const nameOf = w => {
    if (w === 1) return 'x';
    if (w === 0) return '1';
    const given = wnames[w];
    return given && !/^y\d+$/.test(given) ? cIdent(given) : wireLetter(w - 2);
  };
  // constants table: one slot per nonzero affine constant, in program order
  const consts = [];
  const slot = new Map();          // form -> table index
  const forms = [];
  for (const g of chain.gates) forms.push(g.left, g.right);
  forms.push(chain.output);
  for (const f of forms) if (!isZeroConst(f.const)) { slot.set(f, consts.length); consts.push(f.const); }
  const cname = f => `alpha${slot.get(f)}`;
  const cref = f => `alpha[${slot.get(f)}]`;

  // mathematical rendering for the trailing comments
  const mForm = (f, paren) => {
    const parts = [];
    for (const [w, k] of entriesOf(f.terms)) {
      const nm = nameOf(w);
      parts.push(k === 1 ? nm : k === -1 ? `-${nm}` : `${k}*${nm}`);
    }
    if (slot.has(f)) parts.push(cname(f));
    if (!parts.length) parts.push('0');
    const body = parts.join(' + ').replace(/ \+ -/g, ' - ');
    return paren && parts.length > 1 ? `(${body})` : body;
  };
  const mGate = g => `${nameOf(g.out_wire)} = ${mForm(g.left, true)} * ${mForm(g.right, true)}`;

  const L = [C_PROVENANCE];
  const mults = chain.gates.length + (scaleBy !== null ? 1 : 0);
  const gateLabels = chain.gate_labels ?? null;
  const labelLine = i => {
    if (!gateLabels || !gateLabels[i] || (i > 0 && gateLabels[i] === gateLabels[i - 1])) return null;
    return `    /* ${gateLabels[i]} */`;
  };

  if (mode in PRIME_OPS) {
    const ops = PRIME_OPS[mode];
    const M = chain.field?.modulus ?? null;
    if (M !== null && M !== ops.prime) throw new Error(`Mersenne C generation for ${mode}: chain is over another prime`);
    L.push(`/* P(x) over ${ops.banner}: ${mults} multiplications, ${consts.length} constants. */`);
    L.push(...ops.intro);
    const fnL = [`${ops.T} ${name}(${ops.xT} x) {`, ...ops.entry];
    const cForm = f => {
      const ents = entriesOf(f.terms);
      if (ents.length === 1 && ents[0][0] === 1 && ents[0][1] === 1 && !slot.has(f)) return ['x', ops.xBound, true];
      const parts = [];
      for (const [w, k] of ents) parts.push({ neg: k < 0, v: ops.multiple(nameOf(w), Math.abs(k), w === 1) });
      if (slot.has(f)) parts.push({ neg: false, v: [cref(f), 1] });
      if (!parts.length) return ['0', 0, false];
      return ops.fold(parts);
    };
    const body = [];
    for (let i = 0; i < chain.gates.length; i++) {
      const g = chain.gates[i];
      const lab = labelLine(i); if (lab) body.push([lab, null]);
      const [e] = ops.mul(cForm(g.left), cForm(g.right));
      body.push([`    ${ops.T} ${nameOf(g.out_wire)} = ${e};`, mGate(g)]);
    }
    const [oe] = ops.clampOut(cForm(chain.output));
    body.push([`    ${ops.T} P = ${oe};`, `P = ${mForm(chain.output, false)}`]);
    fnL.push(...withComments(body));
    if (scaleBy !== null) fnL.push(ops.scale('P', scaleBy));
    fnL.push(...ops.finish('P'));
    fnL.push('    return P;');
    fnL.push('}');
    const fnText = fnL.join('\n');
    L.push(...ops.header(fnText).split('\n'));
    L.push('');
    L.push(`/* chain constants (the paper's alpha_i, after gadget preprocessing) */`);
    L.push(`static const ${ops.T} alpha[${consts.length}] = {`);
    L.push(...withComments(consts.map((c, i) => [`    ${ops.lit(c)},`, `alpha${i} = ${toBig(c)}`])));
    L.push('};');
    L.push('');
    L.push(fnText);
    return L.join('\n');
  }

  // ----- Q / R: doubles -----
  const real = mode === 'R';
  if (real) {
    L.push(`/* P(x) over R, evaluated in double precision: ${mults} multiplications, ${consts.length} constants. */`);
    L.push('/* The chain was preprocessed exactly (rational arithmetic, as over Q); its constants');
    L.push('   are rounded to the nearest double (shortest decimal that round-trips), so P is');
    L.push('   reproduced approximately. */');
  } else {
    L.push(`/* P(x) over Q, evaluated in double precision: ${mults} multiplications, ${consts.length} constants. */`);
    L.push('/* The chain is exact over Q; here the constants are rounded to the nearest double');
    if (cstyle === 'fraction')
      L.push('   ((double)NUM/DEN is correctly rounded whenever NUM and DEN fit in 53 bits). */');
    else
      L.push('   (shortest decimal that round-trips to the correctly rounded double). */');
  }
  L.push(DOUBLE_NOTE);
  L.push('');
  L.push(`/* chain constants (the paper's alpha_i, after gadget preprocessing) */`);
  L.push(`static const double alpha[${consts.length}] = {`);
  L.push(...withComments(consts.map((c, i) => {
    if (real) return [`    ${qConst(c, 'float').expr},`, `alpha${i}`];
    const { expr, note } = qConst(c, cstyle);
    const r = toRat(c);
    const cm = cstyle === 'fraction' ? `alpha${i}${note ? ': ' + note : ''}` : `alpha${i} = ${r}`;
    return [`    ${expr},`, cm];
  })));
  L.push('};');
  L.push('');
  L.push(`double ${name}(double x) {`);
  const cForm = (f, paren) => {
    const parts = [];
    for (const [w, k] of entriesOf(f.terms)) {
      const nm = nameOf(w);
      parts.push(k === 1 ? nm : k === -1 ? `-${nm}` : `${k}*${nm}`);
    }
    if (slot.has(f)) parts.push(cref(f));
    if (!parts.length) return '0.0';
    const body = parts.join(' + ').replace(/ \+ -/g, ' - ');
    return paren && parts.length > 1 ? `(${body})` : body;
  };
  const body = [];
  for (let i = 0; i < chain.gates.length; i++) {
    const g = chain.gates[i];
    const lab = labelLine(i); if (lab) body.push([lab, null]);
    body.push([`    double ${nameOf(g.out_wire)} = ${cForm(g.left, true)} * ${cForm(g.right, true)};`, mGate(g)]);
  }
  body.push([`    double P = ${cForm(chain.output, false)};`, `P = ${mForm(chain.output, false)}`]);
  L.push(...withComments(body));
  if (scaleBy !== null) {
    const { expr, note } = qConst(scaleBy, real ? 'float' : cstyle);
    L.push(`    return P * ${expr};  /* leading coefficient${note ? ' (' + note + ')' : ''} */`);
  } else L.push('    return P;');
  L.push('}');
  return L.join('\n');
}

// ---------- generic chain-lines -> C (for the comparison methods) ----------
// Grammar of rhs strings: expr := term ((' + '|' − '|' - ') term)*,
// term := factor (' * ' factor)*, factor := '(' expr ')' | token.
export function parseRhs(s) {
  let i = 0;
  const expr = () => {
    let firstNeg = false;
    if (s[i] === '-' && s[i + 1] === ' ') { firstNeg = true; i += 2; }
    const terms = [{ neg: firstNeg, t: term() }];
    for (;;) {
      if (s.startsWith(' + ', i)) { i += 3; terms.push({ neg: false, t: term() }); }
      else if (s.startsWith(' − ', i) || s.startsWith(' - ', i)) { i += 3; terms.push({ neg: true, t: term() }); }
      else break;
    }
    return { sum: terms };
  };
  const term = () => {
    const fs = [factor()];
    while (s.startsWith(' * ', i)) { i += 3; fs.push(factor()); }
    return fs;
  };
  const factor = () => {
    if (s[i] === '(') { i++; const e = expr(); i++; return e; }
    let j = i;
    while (j < s.length && !' ()'.includes(s[j])) j++;
    const tok = s.slice(i, j); i = j;
    return { tok };
  };
  return expr();
}

const isNum = t => /^-?(0x[0-9a-fA-F]+|\d+(\.\d+)?([eE][+-]?\d+)?(\/\d+)?)$/.test(t);
const SCALED_WIRE = /^(-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?)·([A-Za-z_][A-Za-z0-9_]*)$/;

// Evaluate an rhs AST into C with a mode-specific op set. Every value is a
// triple [expr, bound, isBareX] (bound/isBareX only matter in Mersenne modes).
function emitNode(node, ops, top = false) {
  if (node.tok !== undefined) {
    if (isNum(node.tok)) return ops.lit(node.tok);
    const scaled = SCALED_WIRE.exec(node.tok);
    if (scaled) return ops.mul(ops.lit(scaled[1]), ops.wire(scaled[2]));
    if (node.tok.startsWith('-')) return ops.neg(ops.wire(node.tok.slice(1)));
    return ops.wire(node.tok);
  }
  const parts = node.sum.map(({ neg, t }) => ({ neg, v: emitTerm(t, ops) }));
  const v = ops.fold(parts);
  return top ? v : [`(${v[0]})`, v[1], false];
}
function emitTerm(fs, ops) {
  return fs.map(f => emitNode(f, ops)).reduce((a, b) => ops.mul(a, b));
}

/** Normalize a methodChainC mode to a field id given the field object. */
function chainMode(mode, F) {
  if (mode === 'p') return 'p89';
  if (mode === 'gf2k') return `gf${F?.k}`;
  return mode;
}

/** Full C for a rendered method chain over a field mode (see the header).
 *  Options: name, mults, cstyle ('float'|'fraction', Q only), preprocessing
 *  (the method's preprocessing label; a constants table is emitted when it is
 *  not 'none' — always in the prime-field modes), constants ('auto'|'table'|'inline'). */
export function methodChainC(lines, mode, F, { name = 'method', mults = null, cstyle = 'float',
                                               preprocessing = null, constants = 'auto', fn = 'eval_P' } = {}) {
  mode = chainMode(mode, F);
  const isPrime = mode in PRIME_OPS;
  const isGF = /^gf\d+$/.test(mode);
  const G = isGF ? gfSpec(F) : null;
  if (isGF && `gf${F?.k}` !== mode) throw new Error(`mode ${mode} does not match ${F?.name}`);
  const useTable = constants === 'table' ||
    (constants === 'auto' && (isPrime || (preprocessing && preprocessing !== 'none')));
  const table = [];               // [{ lit, expr, comment }]
  const tableIdx = new Map();     // literal string -> index
  const wireBound = new Map();    // Mersenne: name -> bound (units of the lazy range)
  const litValue = t => {         // literal token -> C initializer + comment
    if (isGF) return { expr: useTable ? G.lit(BigInt(t)) : G.inline(BigInt(t)), comment: t };
    if (isPrime) return { expr: PRIME_OPS[mode].lit(BigInt(t)), comment: t };
    const neg = t.startsWith('-'); const u = neg ? t.slice(1) : t;
    if (u.includes('.') || /[eE]/.test(u)) return { expr: t, comment: '' };   // numeric (Motzkin, ℝ)
    const [a, b] = u.split('/');
    const r = new Rat(BigInt(neg ? '-' + a : a), b ? BigInt(b) : 1n);
    const { expr, note } = qConst(r, mode === 'R' ? 'float' : cstyle);
    return { expr, comment: cstyle === 'fraction' ? note : r.toString() };
  };
  const lit = t => {
    const { expr, comment } = litValue(t);
    if (!useTable) return [!isGF && !isPrime && /[-\/]/.test(expr) ? `(${expr})` : expr, 1, false];
    if (!tableIdx.has(t)) { tableIdx.set(t, table.length); table.push({ expr, comment }); }
    return [`c[${tableIdx.get(t)}]`, 1, false];
  };

  let T, xT, header, ops, entry = [], finish = () => [];
  if (isGF) {
    T = xT = G.T; header = null;
    ops = { lit, wire: w => [cIdent(w), 2, w === 'x'],
      neg: v => v,
      mul: (a, b) => {
        const left = unparen(a[0]), right = unparen(b[0]);
        return [G.square && left === right ? `${G.square}(${left})` : `${G.mul}(${left}, ${right})`, 2, false];
      },
      fold: ps => [ps.map(p => p.v[0]).join(' ^ '), 2, false] };
  } else if (isPrime) {
    const P = PRIME_OPS[mode];
    T = P.T; xT = P.xT; header = null;   // emitted after the body (helpers on demand)
    entry = P.entry; finish = P.finish;
    ops = { lit, wire: w => [cIdent(w), wireBound.get(w) ?? (w === 'x' ? P.xBound : P.wireBound), w === 'x'],
      neg: v => [...P.neg(v[0], v[1]), false],
      mul: P.mul,
      fold: ps => P.fold(ps) };
  } else {
    T = xT = 'double';
    // ℝ: the field's constants already print as doubles (shortest round-trip decimals)
    header = (mode !== 'R' && cstyle === 'fraction'
      ? '/* Constants are rounded to double: (double)NUM/DEN is correctly rounded when both fit in 53 bits. */'
      : '/* Constants are rounded to the nearest double (shortest round-trip decimal). */') +
      '\n' + DOUBLE_NOTE;
    ops = { lit, wire: w => [cIdent(w), 1, w === 'x'],
      neg: v => [`(-${v[0]})`, 1, false],
      mul: (a, b) => [`${a[0]} * ${b[0]}`, 1, false],
      fold: ps => [ps.map((p, i) =>
        (i === 0 ? (p.neg ? '-' : '') : (p.neg ? ' - ' : ' + ')) + p.v[0]).join(''), 1, false] };
  }
  const body = [];
  const last = lines.length - 1;
  let prevLayer, usesLdexp = false;
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    if (l.layer !== undefined && l.layer > 0 && l.layer !== prevLayer) {
      if (prevLayer !== undefined) body.push(['', null]);
      body.push([`    /* ---- layer ${l.layer} ---- */`, null]);
      prevLayer = l.layer;
    }
    let v;
    const radixInput = !isGF && !isPrime && l.radixShift !== undefined &&
      /^-?\d+(?:\.\d+)?(?:[eE][+-]?\d+)?·([A-Za-z_][A-Za-z0-9_]*)$/.exec(l.rhs);
    if (radixInput) {
      usesLdexp = true;
      v = [`ldexp(${cIdent(radixInput[1])}, ${l.radixShift})`, 1, false];
    } else v = emitNode(parseRhs(l.rhs), ops, true);
    const lhs = cIdent(l.lhs);
    if (isPrime && i === last) v = PRIME_OPS[mode].clampOut(v);
    wireBound.set(l.lhs, v[1]);
    body.push([`    ${T} ${lhs} = ${v[0]};`, `${l.lhs} = ${l.rhs}`]);
  }
  const fnL = [`${T} ${fn}(${xT} x) {`, ...entry, ...withComments(body)];
  const out = cIdent(lines[last].lhs);
  fnL.push(...finish(out));
  fnL.push(`    return ${out};`, '}');
  const fnText = fnL.join('\n');
  if (isGF) header = G.header(fnText);
  else if (header === null) header = PRIME_OPS[mode].header(fnText);
  else if (usesLdexp) header = '#include <math.h>\n' + header;
  const L = [C_PROVENANCE, `/* ${name}${mults !== null ? `: ${mults} multiplications` : ''} */`, header, ''];
  if (useTable && table.length) {
    L.push(`/* ${name} constants */`);
    L.push(`static const ${T} c[${table.length}] = {`);
    L.push(...withComments(table.map((t, i) => [`    ${t.expr},`, `c${i}${t.comment ? ' = ' + t.comment : ''}`])));
    L.push('};');
    L.push('');
  }
  L.push(fnText);
  return L.join('\n');
}
