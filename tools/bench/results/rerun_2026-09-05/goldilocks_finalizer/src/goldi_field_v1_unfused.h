/* Goldilocks prime field F_p, p = 2^64 - 2^32 + 1, scalar 64-bit arithmetic.
 *
 * Representation ("lazy"): a field element is any uint64_t v, standing for
 * v mod p; gl_fold() canonicalizes to [0, p).  Identities used:
 *   2^64 = EPS (mod p),  EPS = 2^32 - 1;   2^96 = -1 (mod p).
 * Product reduction (Plonky2's reduce128, made branchless): for the 128-bit
 * product x = lo + 2^64 hi, hi = hi_hi 2^32 + hi_lo,
 *   x = lo + 2^64 hi_lo + 2^96 hi_hi = lo + EPS hi_lo - hi_hi   (mod p).
 * Bounds (all proved in the comments, checked against Python big ints by
 * test_goldi_field.cpp / check_goldi_field.py on 10^6 random pairs plus the
 * edge values):
 *   t0 = lo - hi_hi, with p added back on a borrow (hi_hi < 2^32 so
 *        lo - hi_hi + p is in (p - 2^32, p): no underflow);
 *   t1 = hi_lo * EPS = (hi_lo << 32) - hi_lo <= (2^32 - 1)^2 = 2^64 - 2^33 + 1;
 *   t2 = t0 + t1: on a carry the wrapped sum is <= 2^64 - 2^33, and adding
 *        EPS (== 2^64 mod p) stays below 2^64 -- one fix-up suffices.
 * Addition gl_add(a, b) takes ANY a and a CANONICAL b (< p) and returns a
 * (non-canonical) value: with nb = p - b in (0, p], a - nb wraps iff a < nb,
 * and then a + b < p, so the fixed-up result a - nb + p = a + b does not
 * overflow; when it does not wrap, a - nb = a + b - p < 2^64.  Compiles to
 * subs / add / csel (2 cycles of latency, nb precomputed for key words).
 * Multiplication accepts any two uint64_t values (their product fits 128
 * bits); the output of a reduction is any uint64_t.  Every intermediate is
 * therefore < 2^64 by construction and the final gl_fold gives [0, p). */
#ifndef GOLDI_FIELD_H
#define GOLDI_FIELD_H
#include <stdint.h>

#define GL_P   UINT64_C(0xFFFFFFFF00000001)
#define GL_EPS UINT64_C(0x00000000FFFFFFFF)

/* Any 64-bit value -> [0, p): one conditional subtraction. */
static inline uint64_t gl_fold(uint64_t v) {
    return v - (GL_P & (UINT64_C(0) - (uint64_t)(v >= GL_P)));
}

/* a + b mod p with a arbitrary, nb = p - b for a canonical b (0 <= b < p,
 * so 0 < nb <= p).  Result is non-canonical (< 2^64), see the header comment. */
static inline uint64_t gl_add_nb(uint64_t a, uint64_t b, uint64_t nb) {
    const uint64_t r = a - nb;      /* == a + b - p (mod 2^64) */
    return (a < nb) ? a + b : r;    /* a < nb: a + b < p, no overflow */
}
/* Convenience: b canonical, nb computed here. */
static inline uint64_t gl_add(uint64_t a, uint64_t b) { return gl_add_nb(a, b, GL_P - b); }

/* reduce(lo + 2^64 hi) mod p, result in [0, 2^64) (non-canonical). */
static inline uint64_t gl_reduce128(uint64_t lo, uint64_t hi) {
    const uint64_t hi_hi = hi >> 32, hi_lo = hi & GL_EPS;
    uint64_t t0 = lo - hi_hi;                                     /* borrow iff lo < hi_hi */
    t0 -= GL_EPS & (UINT64_C(0) - (uint64_t)(lo < hi_hi));        /* == lo - hi_hi + p on a borrow */
    const uint64_t t1 = (hi_lo << 32) - hi_lo;                    /* hi_lo * EPS, <= 2^64 - 2^33 + 1 */
    uint64_t t2 = t0 + t1;                                        /* carry iff t2 < t0 */
    t2 += GL_EPS & (UINT64_C(0) - (uint64_t)(t2 < t0));           /* 2^64 == EPS; cannot overflow again */
    return t2;
}

/* a * b mod p, any a, b < 2^64; result non-canonical. */
static inline uint64_t gl_mul(uint64_t a, uint64_t b) {
    const unsigned __int128 x = (unsigned __int128)a * b;
    return gl_reduce128((uint64_t)x, (uint64_t)(x >> 64));
}

/* ---- the two finalizers (x canonical, keys canonical, nb[i] = p - key[i]) ----
 * G4  Motzkin's quartic:  y = x (x + b0) + b1,  out = y (y + x + b2) + b3
 *     2 multiplications; out = x^4 + (2 b0 + 1) x^3 + (b0^2 + b0 + 2 b1 + b2) x^2
 *     + (2 b0 b1 + b1 + b0 b2) x + (b1^2 + b1 b2 + b3): a bijection of
 *     (b0..b3) whenever 2 is invertible (check_bijections.py).
 * G5  the paper's degree-5 scheme with integer preprocessing:
 *     out = (x + c2) ((x^2 + c4)(x^2 + x + c3) + c1) + c0,  3 multiplications;
 *     out = x^5 + (c2 + 1) x^4 + (c2 + c3 + c4) x^3 + (c4 + c2 (c3 + c4)) x^2
 *     + (c1 + c3 c4 + c2 c4) x + (c0 + c2 (c1 + c3 c4)): unit pivots, a
 *     bijection over Z and hence over every field (check_bijections.py). */
static inline uint64_t gl_fin_g4(const uint64_t* b, const uint64_t* nb, uint64_t x) {
    const uint64_t nx = GL_P - x;                                  /* x canonical: p - x in (0, p] */
    const uint64_t y  = gl_add_nb(gl_mul(x, gl_add_nb(x, b[0], nb[0])), b[1], nb[1]);
    const uint64_t s  = gl_add_nb(gl_add_nb(y, x, nx), b[2], nb[2]);
    return gl_fold(gl_add_nb(gl_mul(y, s), b[3], nb[3]));
}
static inline uint64_t gl_fin_g5(const uint64_t* c, const uint64_t* nc, uint64_t x) {
    const uint64_t nx = GL_P - x;
    const uint64_t x2 = gl_mul(x, x);
    const uint64_t f  = gl_add_nb(x2, c[4], nc[4]);
    const uint64_t g  = gl_add_nb(gl_add_nb(x2, x, nx), c[3], nc[3]);
    const uint64_t t  = gl_add_nb(gl_mul(f, g), c[1], nc[1]);
    return gl_fold(gl_add_nb(gl_mul(gl_add_nb(x, c[2], nc[2]), t), c[0], nc[0]));
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
