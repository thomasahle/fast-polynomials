/* ***********************************************
 * Hash functions:
 * This file define several hash functions as
 * classes.
 *
 * If DEBUG is defined it asserts that initialization
 * is done properly.
 * ***********************************************/

#ifndef _MULTIPLICATION_H_
#define _MULTIPLICATION_H_

#include <x86intrin.h>
#include <immintrin.h>

#include <cstring>

#ifdef DEBUG
#include <cassert>
#endif

#include "randomgen.h"

using namespace std;

// Shifts a m128i down by 8 bytes, to create a new m128i with
// just the 64 original high bits as its low bits.
#define upper(m) (_mm_srli_si128(m, 8))
// Carryless multiplication of the 
#define clmul(a, b) (_mm_clmulepi64_si128(a, b, 0))
#define clmul_hi_lo(a, b) (_mm_clmulepi64_si128(a, b, 0x01))


// a * b = x 2^64 + y
//   p64 =   2^64 + r
// a * b - x p64 = y - xr
// So isn't it enough to do (y ^ mul(x, r))?
// No, because that's clearly not fully reduced,
// as x*r is probably too large. So we need to do it again,
// reducing xr = z 2^64 + t
// so y ^ t ^ zr.
// This time we are good, since z can't be very big.

/**
 * Calculate the product between two numbers in the finite field
 * GF(2^64).
 * In other words, take the product of the lower 64 bits of a and b,
 * and reduce the result modulo an irreducible polynomial.
 **/
static inline const __m128i gf64_mult(__m128i a, __m128i b) {
  // P64 is the "remainder", such that P64 = 2^64 + r is ireducible.
  __m128i r = _mm_set_epi64x(0, 27);
  // We multiply the contents of the low bits of a and b
  __m128i ab = clmul(a, b);          // ab = x 2^64 + y
  __m128i xr = clmul_hi_lo(ab, r);   // xr = z 2^64 + t
  // Note we can't just take mul(ab, r**2) here, as there is an implicit
  // right shift in the middle.
  __m128i zr = clmul_hi_lo(xr, r);   // zr
  // Note, we should only really return the lower 64 bits of this,
  // so be warned the high bits will contain garbage.
  return ab ^ xr ^ zr; // y ^ t ^ lower(zr)
}


/**
 * Reduces a 128 bit number modulo x^64 + x^4 + x^3 + x + 1.
 * Returns a m128i with the result in the lowest 64 bits.
 * The highest 64 bits are unspecified.
 * Idea is that if P64 = 2^64 + r, and a = x2^64 + y,
 * then a % P64 = a ^ (P64 x) = a ^ xr.
 * Let 
 **/
static __m128i lemire_modulo(__m128i a) {
  __m128i r = _mm_cvtsi64_si128(27);  // Same as P64 above, 0b11011
  __m128i xr = clmul_hi_lo(a, r);     // a[high] * r[low]
  // The only difference is that we use a table lookup instead
  // of the second multiplication.
  __m128i table = _mm_setr_epi8(0, 27, 54, 45, 108, 119, 90, 65, char(216),
                                char(195), char(238), char(245), char(180),
                                char(175), char(130), char(153));
  __m128i zr = _mm_shuffle_epi8(table, upper(xr));
  // Notice again, the upper 64 bits will be garbage.
  return a ^ xr ^ zr;
}

static char jakob_table[16] = {0,         27,        54,        45,
                               108,       119,       90,        65,
                               char(216), char(195), char(238), char(245),
                               char(180), char(175), char(130), char(153)};
static __m128i lemire_modulo_jakob(__m128i a) {
  __m128i r = _mm_cvtsi64_si128(27);  // Same as P64 above
  __m128i z = _mm_clmulepi64_si128(a, r, 0x01);

  __int64_t i = _mm_cvtsi128_si64(_mm_srli_si128(z, 8));
  __m128i y = _mm_cvtsi64_si128(jakob_table[i]);

  __m128i temp1 = _mm_xor_si128(z, a);
  return _mm_xor_si128(temp1, y);
}

/**
 * Takes three integers a, b, x and calculates approximately
 * (ax + b) mod p where p = 2^89 - 1. It assumes that a, b <= 2p.
 * It will return a number, y, that satisfies 0 <= y < 2p.
 **/
static inline __uint128_t fast_large_mult_mod(__uint128_t a, __uint128_t b,
                                              uint64_t x) {
  __uint128_t mul_low = (__uint128_t)(uint64_t)a * (__uint128_t)x;
  __uint128_t mul_high = (__uint128_t)(uint64_t)(a >> 64) * (__uint128_t)x;
  // Add b to low and high part.
  __uint128_t c = mul_low + (__uint128_t)(uint64_t)b;
  // Remember to move any carry from c onto the upper part.
  __uint128_t d = mul_high + (b >> 64) + (c >> 64);
  // We only need to use the mask & shift trick once.
  // We need the low bits from c, as they all survive masking, and none survive shifting.
  // We mask 25 bits off from d
  return ((d & (((uint64_t)1 << 25) - 1)) << 64) + (d >> 25) + (uint64_t)c;
}

/**
 * Computes a*x mod mod p where p = 2^89 - 1,
 * or a number equivalent to that but smaller than 2p.
 * It assumes that a, b <= 2p.
 * It will return a number, y, that satisfies 0 <= y < 2p.
 **/
static inline __uint128_t fast_large_mult_mod_2(__uint128_t a, uint64_t x) {
   return fast_large_mult_mod(a, 0, x);
}

/**
 * Takes three integers a, b, x and calculates (ax + b) mod p where p = 2^89-1.
 * Uses the "smart division" algorithm from the Mersenne paper.
 **/
inline const __uint128_t fast_large_mult_mod_exact(const __uint128_t a,
                                                   const __uint128_t b,
                                                   const uint64_t x) {
  __uint128_t fst_a = (uint64_t)(a >> 64);
  __uint128_t scd_a = (uint64_t)a;

  __uint128_t low = scd_a * x;
  __uint128_t high = fst_a * x;

  __uint128_t c_div = low + (uint64_t)(b + 1);
  __uint128_t d_div = high + ((b + 1) >> 64) + (c_div >> 64);

  __uint128_t e_div = d_div >> 25;
  c_div = (uint64_t)c_div + e_div;
  d_div = d_div + (c_div >> 64);

  __uint128_t e = b + (d_div >> 25);
  __uint128_t c_mod = low + (uint64_t)e;
  __uint128_t d_mod = high + (e >> 64) + (c_mod >> 64);  // carry from c_mod (fixed 2026-09-02)
  return (__uint128_t)(uint64_t)c_mod +
         ((d_mod & (((__uint128_t)1 << 25) - 1)) << 64);
}


/**
 * Takes three integers a, b, x and calculates approximately
 * (ab+d) mod p where p = 2^89 - 1. It assumes that a, b <= 2^c*p.
 * It will return a number, y, that satisfies 0 <= y < p + 4 + 2^c.
 * Assuming c < 23.
 * Actually we are now assuming c < 7.
 **/
static inline __uint128_t extra_large_mult_add_mod(__uint128_t a, __uint128_t b, __uint128_t d) {
  uint64_t a_lo = (uint64_t)a;
  uint64_t b_lo = (uint64_t)b;
  uint32_t a_hi = a >> 64;
  uint32_t b_hi = b >> 64;
  __uint128_t mul_low = (__uint128_t)a_lo * b_lo;  // < 2^128
  __uint128_t mul_mid0 = (__uint128_t)a_hi * b_lo; // < (2^c*p / 2^64) * 2^64 < 2^(89+c)
  __uint128_t mul_mid1 = (__uint128_t)a_lo * b_hi; // < 2^(89+c)
  uint64_t mul_high = (uint64_t)a_hi * b_hi;       // < (2^c*p)**2 / 2^128 < 2^(50+2c)

  // Move carries over
  // After carries are taken care of, we only care about the low 64 bits
  // of mul_low and mid.
  __uint128_t mid = mul_mid0 + mul_mid1 + (mul_low >> 64); // < 2*2^(89+c) + 2^64
  mul_high += mid >> 64;                                   // < 2^(50+2c) + 2^(26+c)

  uint64_t mask25 = (uint64_t(1) << 25) - 1;

  __uint128_t new_low = (uint64_t) mul_low;
  new_low += uint64_t(mid) >> 25;
  new_low += (mul_high & mask25) << 39;
  new_low += d; // Seems like a good place to add d

  uint64_t new_high = mid & mask25; // From masking; < 2^25
  new_high += mul_high >> 25; // From shifting;      < 2^(25+2c) + 2^(1+c)
  new_high += new_low >> 64; // Carry (shouldn't be more than 1)

  __uint128_t total = uint64_t(new_low);
  // We have to do one last reduction of high, since otherwise we'd return a value of
  // size 2^(89) + 2^(89+2c), which would be a factor 2^c increase on the input.
  // After this last reduction the output is only of size ~ 2^89 + 2^64 + 2^(2c).
  total += __uint128_t(new_high & mask25) << 64;
  total += new_high >> 25;
  return total;
}


/**
 * Takes three integers a, b, x and calculates approximately
 * (ab) mod p where p = 2^89 - 1. It assumes that a, b <= 2^c*p.
 * It will return a number, y, that satisfies 0 <= y < p + 4 + 2^c.
 * Assuming c < 23.
 * Actually we are now assuming c < 7.
 **/
static inline __uint128_t extra_large_mult_mod(__uint128_t a, __uint128_t b) {
  return extra_large_mult_add_mod(a, b, 0);
}

/**
 * Karatsuba version of extra_large_mult_add_mod.
 * Uses 3 multiplications instead of 4, which is faster on x86 for longer
 * polynomial chains (N >= 5) due to better instruction-level parallelism.
 *
 * For a,b < 2^90: a = a_hi*2^64 + a_lo, b = b_hi*2^64 + b_lo
 * Karatsuba: a*b = z0 + z1*2^64 + z2*2^128 where
 *   z0 = a_lo * b_lo, z2 = a_hi * b_hi
 *   z1 = (a_lo + a_hi)(b_lo + b_hi) - z0 - z2
 **/
static inline __uint128_t extra_large_mult_add_mod_karatsuba(__uint128_t a, __uint128_t b, __uint128_t d) {
    uint64_t a_lo = (uint64_t)a;
    uint64_t b_lo = (uint64_t)b;
    uint64_t a_hi = a >> 64;
    uint64_t b_hi = b >> 64;

    __uint128_t z0 = (__uint128_t)a_lo * b_lo;
    uint64_t z2 = a_hi * b_hi;

    // 65-bit sums with carry tracking
    uint64_t s_a = a_lo + a_hi;
    uint64_t c_a = (s_a < a_lo) ? 1 : 0;
    uint64_t s_b = b_lo + b_hi;
    uint64_t c_b = (s_b < b_lo) ? 1 : 0;

    // 65x65 multiplication: (s_a + c_a*2^64) * (s_b + c_b*2^64)
    __uint128_t prod = (__uint128_t)s_a * s_b;
    uint64_t w0 = (uint64_t)prod;
    __uint128_t w1_wide = (prod >> 64) + (c_a ? s_b : 0) + (c_b ? s_a : 0);
    uint64_t w1 = (uint64_t)w1_wide;

    uint64_t z0_lo = (uint64_t)z0;
    uint64_t z0_hi = z0 >> 64;

    // Multi-word subtraction: [w0,w1] - [z0_lo,z0_hi] - [z2,0]
    uint64_t borrow1 = (w0 < z0_lo) ? 1 : 0;
    uint64_t t0 = w0 - z0_lo;
    uint64_t borrow2 = (t0 < z2) ? 1 : 0;
    uint64_t r0 = t0 - z2;
    uint64_t total_borrow0 = borrow1 + borrow2;

    uint64_t t1 = w1 - total_borrow0;
    uint64_t r1 = t1 - z0_hi;

    // Reconstruct: a*b = z0 + z1*2^64 + z2*2^128
    __uint128_t mid = (__uint128_t)z0_hi + r0;
    uint64_t high = r1 + z2 + (mid >> 64);

    // Reduce mod 2^89 - 1
    uint64_t mask25 = (uint64_t(1) << 25) - 1;
    uint64_t mid_64 = (uint64_t)mid;

    __uint128_t new_low = z0_lo;
    new_low += mid_64 >> 25;
    new_low += (high & mask25) << 39;
    new_low += d;

    uint64_t new_high = mid_64 & mask25;
    new_high += high >> 25;
    new_high += new_low >> 64;

    __uint128_t total = (uint64_t)new_low;
    total += (__uint128_t)(new_high & mask25) << 64;
    total += new_high >> 25;
    return total;
}

static inline __uint128_t extra_large_mult_mod_karatsuba(__uint128_t a, __uint128_t b) {
    return extra_large_mult_add_mod_karatsuba(a, b, 0);
}

/**
 * Template wrapper to select between schoolbook and Karatsuba based on N.
 * On x86, Karatsuba is faster for N >= 5 due to instruction-level parallelism.
 **/
template<int N>
static inline __uint128_t extra_large_mult_add_mod_auto(__uint128_t a, __uint128_t b, __uint128_t d) {
    if constexpr (N >= 5) {
        return extra_large_mult_add_mod_karatsuba(a, b, d);
    } else {
        return extra_large_mult_add_mod(a, b, d);
    }
}

template<int N>
static inline __uint128_t extra_large_mult_mod_auto(__uint128_t a, __uint128_t b) {
    return extra_large_mult_add_mod_auto<N>(a, b, 0);
}

/**
 * Same as before, just faster.
 * This time we need c ~< 10, but it's not that bad.
 **/
static inline __uint128_t karatsuba_mult_mod(__uint128_t a, __uint128_t b) {
  __uint128_t mask89 = (__uint128_t(1) << 89) - 1;
  __uint128_t mask50 = (__uint128_t(1) << 50) - 1;
  __uint128_t mask25 = (__uint128_t(1) << 25) - 1;

  uint64_t a_lo = (uint64_t)(a & mask50);
  uint64_t b_lo = (uint64_t)(b & mask50);
  uint32_t a_hi = (a >> 50);
  uint32_t b_hi = (b >> 50);
  __uint128_t mul_low = (__uint128_t)a_lo * b_lo;
  __uint128_t mul_high = (__uint128_t)a_hi * b_hi;
  __uint128_t mul_mid = (__uint128_t)(a_hi + a_lo) * (b_hi + b_lo);
  mul_mid -= mul_low + mul_high;

  mul_low = (mul_low & mask89) + (mul_low >> 89);
  mul_mid = (mul_mid & (mask25 << 64)) + (mul_mid >> 25);
  mul_high = (mul_high << 39);

  __uint128_t total = mul_low + mul_mid + mul_high;
  total = (total & mask89) + (total >> 89);
  return total;
}


/**
 * Same as before, just faster.
 * This time we need c ~< 5, but it's not that bad.
 **/
static __uint128_t karatsuba_3_mult_mod(__uint128_t a, __uint128_t b) {
  __uint128_t mask89 = (__uint128_t(1) << 89) - 1;

  int c = 31;
  __uint128_t mask_c = (__uint128_t(1) << c) - 1;

  // a = a2*2^60 + a1*2^30 + a0
  uint32_t a0 = (uint32_t)(a & mask_c);
  uint32_t a1 = (uint32_t)((a >> c) & mask_c);
  uint32_t a2 = (uint32_t)(a >> 2*c);
  uint32_t b0 = (uint32_t)(b & mask_c);
  uint32_t b1 = (uint32_t)((b >> c) & mask_c);
  uint32_t b2 = (uint32_t)(b >> 2*c);

  uint64_t d0 = (uint64_t)a0 * b0;
  uint64_t d1 = (uint64_t)a1 * b1;
  uint64_t d2 = (uint64_t)a2 * b2;

  // C(x) = D2x^4 + (D1,2 − D1 − D2)x^3 + (D0,2 − D2 − D0 + D1)x^2 + (D0,1 − D1 − D0)x + D0
  uint64_t d01 = (uint64_t)(a0 + a1) * (b0 + b1) - d1 - d0;
  uint64_t d02 = (uint64_t)(a0 + a2) * (b0 + b2) + d1 - d2 - d0;
  uint64_t d12 = (uint64_t)(a1 + a2) * (b1 + b2) - d1 - d2;

  __uint128_t total = d0;
  total += ((__uint128_t(d01) << c) & mask89) + (d01 >> (89-c));
  total += ((__uint128_t(d02) << 2*c) & mask89) + (d01 >> (89-2*c));
  total += __int128_t(d02) << (3*c - 89);
  total += __int128_t(d12) << (4*c - 89);

  //__uint128_t total = mul_low + mul_mid + mul_high;
  total = (total & mask89) + (total >> 89);
  return total;
}


/**
 * Vectorized
 **/
static __uint128_t karatsuba_3vec_mult_mod(__uint128_t a, __uint128_t b) {
  __uint128_t mask89 = (__uint128_t(1) << 89) - 1;

  int c = 31;
  __uint128_t mask_c = (__uint128_t(1) << c) - 1;

  // a = a2*2^60 + a1*2^30 + a0
  uint32_t a0 = (uint32_t)(a & mask_c);
  uint32_t a1 = (uint32_t)((a >> c) & mask_c);
  uint32_t a2 = (uint32_t)(a >> 2*c);
  uint32_t b0 = (uint32_t)(b & mask_c);
  uint32_t b1 = (uint32_t)((b >> c) & mask_c);
  uint32_t b2 = (uint32_t)(b >> 2*c);

  __m256i av = _mm256_setr_epi32(a0, a1, a2, 0, 0, 0, 0, 0);
  __m256i bv = _mm256_setr_epi32(b0, b1, b2, 0, 0, 0, 0, 0);
  __m256i abv = _mm256_mul_epu32(av, bv);

  // Create a temporary register with the values (a1, a2, a0, 0)
  // There is no unsigned add? Is that a problem? Maybe I need c=30 to make sure the sign-bit is not set?
  __m256i aav = _mm256_add_epi32(av, _mm256_shuffle_epi32(av, _MM_SHUFFLE(1, 2, 0, 3)));

  // Create a temporary register with the values (b1, b2, b0, 0)
  __m256i bbv = _mm256_add_epi32(bv, _mm256_shuffle_epi32(bv, _MM_SHUFFLE(1, 2, 0, 3)));
  __m256i aabbv = _mm256_mul_epu32(av, bv);

  // C(x) = D2x^4 + (D1,2 − D1 − D2)x^3 + (D0,2 − D2 − D0 + D1)x^2 + (D0,1 − D1 − D0)x + D0
  // uint64_t d01 = (uint64_t)(a0 + a1) * (b0 + b1) - d1 - d0;
  // uint64_t d02 = (uint64_t)(a0 + a2) * (b0 + b2) + d1 - d2 - d0;
  // uint64_t d12 = (uint64_t)(a1 + a2) * (b1 + b2) - d1 - d2;

  // Add d1 to d02
  aabbv = _mm256_add_epi64(aabbv, _mm256_shuffle_epi32(abv, _MM_SHUFFLE(3, 1, 3, 3)));
  // Subtract (d0, d2, d1)
  aabbv = _mm256_sub_epi64(aabbv, _mm256_shuffle_epi32(abv, _MM_SHUFFLE(0, 2, 1, 3)));
  // Subtract (d1, d0, d2)
  aabbv = _mm256_sub_epi64(aabbv, _mm256_shuffle_epi32(abv, _MM_SHUFFLE(1, 0, 2, 3)));

  uint64_t* res0 = (uint64_t*) &abv;
  uint64_t* res1 = (uint64_t*) &aabbv;
  uint64_t d0 = res0[0];
  uint64_t d1 = res0[1];
  uint64_t d2 = res0[2];
  uint64_t d01 = res1[0];
  uint64_t d02 = res1[1];
  uint64_t d12 = res1[2];

  __uint128_t total = d0;
  total += ((__uint128_t(d01) << c) & mask89) + (d01 >> (89-c));
  total += ((__uint128_t(d02) << 2*c) & mask89) + (d01 >> (89-2*c));
  total += __int128_t(d02) << (3*c - 89);
  total += __int128_t(d12) << (4*c - 89);

  //__uint128_t total = mul_low + mul_mid + mul_high;
  total = (total & mask89) + (total >> 89);
  return total;
}

#endif  // _MULTIPLICATION_H_
