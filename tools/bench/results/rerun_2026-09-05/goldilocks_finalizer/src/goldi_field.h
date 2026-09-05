/* Goldilocks prime field F_p, p = 2^64 - 2^32 + 1, scalar 64-bit arithmetic (v2: fused
 * multiply-add, selects forced branchless).
 *
 * Representation ("lazy"): a field element is any uint64_t v, standing for
 * v mod p; gl_fold() canonicalizes to [0, p).  Identities used:
 *   2^64 = EPS (mod p),  EPS = 2^32 - 1;   2^96 = -1 (mod p).
 * Product reduction (Plonky2's reduce128, branchless): for the 128-bit
 * value x = lo + 2^64 hi, hi = hi_hi 2^32 + hi_lo,
 *   x = lo + 2^64 hi_lo + 2^96 hi_hi = lo + EPS hi_lo - hi_hi   (mod p).
 * Bounds (checked against Python big ints by test_goldi_field.cpp /
 * check_goldi_field.py on 10^6 random inputs plus the edge values):
 *   t0 = lo - hi_hi, with p added back on a borrow (hi_hi < 2^32, so
 *        lo - hi_hi + p lies in (p - 2^32, p): no underflow);
 *   t1 = hi_lo * EPS = (hi_lo << 32) - hi_lo <= (2^32 - 1)^2 = 2^64 - 2^33 + 1;
 *   t2 = t0 + t1: on a carry the wrapped sum is <= 2^64 - 2^33, and adding
 *        EPS (== 2^64 mod p) stays below 2^64 -- one fix-up suffices.
 * The reduction is valid for ANY 128-bit input, so a b + c with a, b, c < 2^64
 * (at most 2^128 - 2^64, no overflow) reduces the same way: gl_mul_add fuses
 * the addition that follows a multiply into one adds/adc pair on the product
 * (the analogue of the char-2 circuit's reduce_add).
 * Addition gl_add_nb(a, b, nb) takes ANY a and a CANONICAL b (< p, nb = p - b
 * in (0, p]) and returns a non-canonical value: a - nb wraps iff a < nb, and
 * then a + b < p, so the alternative a + b does not overflow; otherwise
 * a - nb = a + b - p < 2^64.  subs / add / csel (cmov), 2 cycles.
 * Every select is marked __builtin_unpredictable: with random data a branch
 * would mispredict half the time (clang did emit jb/jae on x86-64 in v1). */
#ifndef GOLDI_FIELD_H
#define GOLDI_FIELD_H
#include <stdint.h>

#define GL_P   UINT64_C(0xFFFFFFFF00000001)
#define GL_EPS UINT64_C(0x00000000FFFFFFFF)
#if defined(__has_builtin)
#  if __has_builtin(__builtin_unpredictable)
#    define GL_UNPRED(c) __builtin_unpredictable(c)
#  endif
#endif
#ifndef GL_UNPRED
#  define GL_UNPRED(c) (c)
#endif

/* Any 64-bit value -> [0, p): one conditional subtraction. */
static inline uint64_t gl_fold(uint64_t v) { return GL_UNPRED(v >= GL_P) ? v - GL_P : v; }

/* a + b mod p, a arbitrary, b canonical with nb = p - b precomputed; result non-canonical. */
static inline uint64_t gl_add_nb(uint64_t a, uint64_t b, uint64_t nb) {
    const uint64_t r = a - nb;                 /* == a + b - p (mod 2^64) */
    return GL_UNPRED(a < nb) ? a + b : r;      /* a < nb: a + b < p, no overflow */
}
static inline uint64_t gl_add(uint64_t a, uint64_t b) { return gl_add_nb(a, b, GL_P - b); }

/* reduce(lo + 2^64 hi) mod p for any 128-bit input; result in [0, 2^64). */
static inline uint64_t gl_reduce128(uint64_t lo, uint64_t hi) {
    const uint64_t hi_hi = hi >> 32, hi_lo = hi & GL_EPS;
    const uint64_t d  = lo - hi_hi;
    const uint64_t t0 = GL_UNPRED(lo < hi_hi) ? d - GL_EPS : d;   /* borrow: == lo - hi_hi + p */
    const uint64_t t1 = (hi_lo << 32) - hi_lo;                    /* hi_lo * EPS */
    const uint64_t s  = t0 + t1;
    return GL_UNPRED(s < t0) ? s + GL_EPS : s;                    /* carry: 2^64 == EPS, no second overflow */
}

#if defined(__SIZEOF_INT128__)
static inline uint64_t gl_mul(uint64_t a, uint64_t b) {               /* a b mod p, any a, b */
    const unsigned __int128 x = (unsigned __int128)a * b;
    return gl_reduce128((uint64_t)x, (uint64_t)(x >> 64));
}
static inline uint64_t gl_mul_add(uint64_t a, uint64_t b, uint64_t c) { /* a b + c mod p, any a, b, c */
    const unsigned __int128 x = (unsigned __int128)a * b + c;         /* <= 2^128 - 2^64: no overflow */
    return gl_reduce128((uint64_t)x, (uint64_t)(x >> 64));
}
#else
/* 32-bit-limb fallback (no __int128): schoolbook 64x64 -> 128. */
static inline void gl_mul64_128(uint64_t a, uint64_t b, uint64_t* lo, uint64_t* hi) {
    const uint64_t a0 = (uint32_t)a, a1 = a >> 32, b0 = (uint32_t)b, b1 = b >> 32;
    const uint64_t p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
    const uint64_t mid = (p00 >> 32) + (uint32_t)p01 + (uint32_t)p10;
    *lo = (mid << 32) | (uint32_t)p00;
    *hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
}
static inline uint64_t gl_mul(uint64_t a, uint64_t b) { uint64_t lo, hi; gl_mul64_128(a, b, &lo, &hi); return gl_reduce128(lo, hi); }
static inline uint64_t gl_mul_add(uint64_t a, uint64_t b, uint64_t c) {
    uint64_t lo, hi; gl_mul64_128(a, b, &lo, &hi);
    const uint64_t s = lo + c; hi += (s < lo); return gl_reduce128(s, hi);
}
#endif

/* ---- the two finalizers (x canonical, keys canonical, nb[i] = p - key[i]) ----
 * G4  Motzkin's quartic:  y = x (x + b0) + b1,  out = y (y + x + b2) + b3
 *     2 multiplications; out = x^4 + (2 b0 + 1) x^3 + (b0^2 + b0 + 2 b1 + b2) x^2
 *     + (2 b0 b1 + b1 + b0 b2) x + (b1^2 + b1 b2 + b3): a bijection of
 *     (b0..b3) whenever 2 is invertible (check_bijections.py).
 * G5  the paper's degree-5 scheme with integer preprocessing:
 *     out = (x + c2) ((x^2 + c4)(x^2 + x + c3) + c1) + c0,  3 multiplications;
 *     out = x^5 + (c2 + 1) x^4 + (c2 + c3 + c4) x^3 + (c4 + c2 (c3 + c4)) x^2
 *     + (c1 + c3 c4 + c2 c4) x + (c0 + c2 (c1 + c3 c4)): unit pivots, a
 *     bijection over Z and hence over every field (check_bijections.py).
 * Schedule: the sums that involve only x and a key (x + b2, x + c3, x + c2) are
 * computed off the critical path and folded so they can serve as the canonical
 * operand of a later addition; every addition that follows a multiply is fused
 * into that multiply's reduction (gl_mul_add). */
static inline uint64_t gl_fin_g4(const uint64_t* b, const uint64_t* nb, uint64_t x) {
    const uint64_t xb2 = gl_fold(gl_add_nb(x, b[2], nb[2]));                      /* x + b2, canonical (off path) */
    const uint64_t y   = gl_mul_add(x, gl_add_nb(x, b[0], nb[0]), b[1]);          /* x (x + b0) + b1 */
    return gl_fold(gl_mul_add(y, gl_add_nb(y, xb2, GL_P - xb2), b[3]));           /* y (y + x + b2) + b3 */
}
static inline uint64_t gl_fin_g5(const uint64_t* c, const uint64_t* nc, uint64_t x) {
    const uint64_t xc3 = gl_fold(gl_add_nb(x, c[3], nc[3]));                      /* x + c3, canonical (off path) */
    const uint64_t xc2 = gl_add_nb(x, c[2], nc[2]);                               /* x + c2 (off path; a multiplicand may be non-canonical) */
    const uint64_t x2  = gl_mul(x, x);
    const uint64_t f   = gl_add_nb(x2, c[4], nc[4]);                              /* x^2 + c4 */
    const uint64_t g   = gl_add_nb(x2, xc3, GL_P - xc3);                          /* x^2 + x + c3 */
    const uint64_t t   = gl_mul_add(f, g, c[1]);                                  /* (x^2 + c4)(x^2 + x + c3) + c1 */
    return gl_fold(gl_mul_add(xc2, t, c[0]));                                     /* (x + c2) t + c0 */
}

/* Uniform element of F_p from a splitmix64 stream: rejection sampling
 * (a 64-bit word is rejected with probability (2^32 - 1)/2^64). */
static inline uint64_t gl_splitmix64(uint64_t* state) {
    uint64_t z = (*state += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}
static inline uint64_t gl_uniform(uint64_t* state) {
    uint64_t v;
    do { v = gl_splitmix64(state); } while (v >= GL_P);
    return v;
}
#endif
