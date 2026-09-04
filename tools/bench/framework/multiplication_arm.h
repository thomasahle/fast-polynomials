/* ***********************************************
 * Multiplication functions for ARM NEON
 * Equivalent to multiplication.h but using ARM intrinsics
 * ***********************************************/

#ifndef _MULTIPLICATION_ARM_H_
#define _MULTIPLICATION_ARM_H_

#include <arm_neon.h>
#include <cstdint>
#include <cstring>

#ifdef DEBUG
#include <cassert>
#endif

#include "randomgen.h"

using namespace std;

// ARM NEON types for 128-bit vectors
// poly128_t is the result of polynomial multiply
// uint8x16_t is a generic 128-bit vector

// Helper to extract upper 64 bits
static inline uint64_t upper64(uint8x16_t v) {
    return vgetq_lane_u64(vreinterpretq_u64_u8(v), 1);
}

// Helper to extract lower 64 bits
static inline uint64_t lower64(uint8x16_t v) {
    return vgetq_lane_u64(vreinterpretq_u64_u8(v), 0);
}

// Create a 128-bit vector from two 64-bit values
static inline uint8x16_t make128(uint64_t lo, uint64_t hi) {
    uint64x2_t v = vcombine_u64(vcreate_u64(lo), vcreate_u64(hi));
    return vreinterpretq_u8_u64(v);
}

// Create a 128-bit vector from a single 64-bit value (high bits = 0)
static inline uint8x16_t from64(uint64_t lo) {
    return make128(lo, 0);
}

// XOR two 128-bit vectors
static inline uint8x16_t xor128(uint8x16_t a, uint8x16_t b) {
    return veorq_u8(a, b);
}

// Carryless multiplication of low 64 bits of a and b
// ARM equivalent of _mm_clmulepi64_si128(a, b, 0)
static inline poly128_t clmul_lo_lo(uint8x16_t a, uint8x16_t b) {
    poly64_t a_lo = vgetq_lane_p64(vreinterpretq_p64_u8(a), 0);
    poly64_t b_lo = vgetq_lane_p64(vreinterpretq_p64_u8(b), 0);
    return vmull_p64(a_lo, b_lo);
}

// Carryless multiplication of high 64 bits of a with low 64 bits of b
// ARM equivalent of _mm_clmulepi64_si128(a, b, 0x01)
static inline poly128_t clmul_hi_lo(uint8x16_t a, uint8x16_t b) {
    poly64_t a_hi = vgetq_lane_p64(vreinterpretq_p64_u8(a), 1);
    poly64_t b_lo = vgetq_lane_p64(vreinterpretq_p64_u8(b), 0);
    return vmull_p64(a_hi, b_lo);
}

// Convert poly128_t to uint8x16_t
static inline uint8x16_t poly_to_u8(poly128_t p) {
    return vreinterpretq_u8_p128(p);
}

// Shift right by 64 bits (move high to low, zero high)
// Using vextq_u8 for better performance on Apple Silicon
static inline uint8x16_t upper(uint8x16_t m) {
    uint8x16_t zero = vdupq_n_u8(0);
    return vextq_u8(m, zero, 8);
}

/**
 * Calculate the product between two numbers in the finite field GF(2^64).
 * Takes the product of the lower 64 bits of a and b,
 * and reduces the result modulo the irreducible polynomial x^64 + x^4 + x^3 + x + 1.
 **/
static inline uint8x16_t gf64_mult(uint8x16_t a, uint8x16_t b) {
    // r = 27 = 0b11011, the "remainder" of P64 = x^64 + x^4 + x^3 + x + 1
    uint8x16_t r = from64(27);

    // ab = a_lo * b_lo (carryless)
    poly128_t ab_poly = clmul_lo_lo(a, b);
    uint8x16_t ab = poly_to_u8(ab_poly);

    // xr = ab_hi * r_lo
    poly128_t xr_poly = clmul_hi_lo(ab, r);
    uint8x16_t xr = poly_to_u8(xr_poly);

    // zr = xr_hi * r_lo
    poly128_t zr_poly = clmul_hi_lo(xr, r);
    uint8x16_t zr = poly_to_u8(zr_poly);

    // Result: ab ^ xr ^ zr (only lower 64 bits are valid)
    return xor128(xor128(ab, xr), zr);
}

/**
 * Reduces a 128-bit number modulo x^64 + x^4 + x^3 + x + 1.
 * Returns result in lowest 64 bits (high 64 bits are garbage).
 * This is Lemire's fast reduction using a lookup table.
 **/
static inline uint8x16_t lemire_modulo(uint8x16_t a) {
    uint8x16_t r = from64(27);

    // xr = a_hi * r_lo
    poly128_t xr_poly = clmul_hi_lo(a, r);
    uint8x16_t xr = poly_to_u8(xr_poly);

    // Table lookup for the final reduction (parallel byte shuffle)
    // Each byte in upper(xr) is used as an index into the table
    static const uint8_t table_data[16] = {
        0, 27, 54, 45, 108, 119, 90, 65,
        216, 195, 238, 245, 180, 175, 130, 153
    };
    uint8x16_t table = vld1q_u8(table_data);

    // ARM vqtbl1q_u8 returns 0 for indices >= 16, unlike x86 shuffle which masks.
    // Mask indices to low 4 bits to match x86 behavior.
    uint8x16_t indices = vandq_u8(upper(xr), vdupq_n_u8(0x0F));
    uint8x16_t zr = vqtbl1q_u8(table, indices);

    return xor128(xor128(a, xr), zr);
}

/**
 * Takes three integers a, b, x and calculates approximately
 * (ax + b) mod p where p = 2^89 - 1. It assumes that a, b <= 2p.
 * Returns a number y that satisfies 0 <= y < 2p.
 **/
static inline __uint128_t fast_large_mult_mod(__uint128_t a, __uint128_t b,
                                              uint64_t x) {
    __uint128_t mul_low = (__uint128_t)(uint64_t)a * (__uint128_t)x;
    __uint128_t mul_high = (__uint128_t)(uint64_t)(a >> 64) * (__uint128_t)x;
    __uint128_t c = mul_low + (__uint128_t)(uint64_t)b;
    __uint128_t d = mul_high + (b >> 64) + (c >> 64);
    return ((d & (((uint64_t)1 << 25) - 1)) << 64) + (d >> 25) + (uint64_t)c;
}

/**
 * Computes a*x mod p where p = 2^89 - 1.
 **/
static inline __uint128_t fast_large_mult_mod_2(__uint128_t a, uint64_t x) {
    return fast_large_mult_mod(a, 0, x);
}

/**
 * Takes three integers a, b, x and calculates (ax + b) mod p where p = 2^89-1.
 * Uses the "smart division" algorithm.
 **/
static inline __uint128_t fast_large_mult_mod_exact(__uint128_t a,
                                                    __uint128_t b,
                                                    uint64_t x) {
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
 * Extra large multiplication with addition mod 2^89-1.
 **/
static inline __uint128_t extra_large_mult_add_mod(__uint128_t a, __uint128_t b, __uint128_t d) {
    uint64_t a_lo = (uint64_t)a;
    uint64_t b_lo = (uint64_t)b;
    uint32_t a_hi = a >> 64;
    uint32_t b_hi = b >> 64;
    __uint128_t mul_low = (__uint128_t)a_lo * b_lo;
    __uint128_t mul_mid0 = (__uint128_t)a_hi * b_lo;
    __uint128_t mul_mid1 = (__uint128_t)a_lo * b_hi;
    uint64_t mul_high = (uint64_t)a_hi * b_hi;

    __uint128_t mid = mul_mid0 + mul_mid1 + (mul_low >> 64);
    mul_high += mid >> 64;

    uint64_t mask25 = (uint64_t(1) << 25) - 1;

    __uint128_t new_low = (uint64_t)mul_low;
    new_low += uint64_t(mid) >> 25;
    new_low += (mul_high & mask25) << 39;
    new_low += d;

    uint64_t new_high = mid & mask25;
    new_high += mul_high >> 25;
    new_high += new_low >> 64;

    __uint128_t total = uint64_t(new_low);
    total += __uint128_t(new_high & mask25) << 64;
    total += new_high >> 25;
    return total;
}

// Note: A Karatsuba version was attempted but benchmarked ~23% slower than
// schoolbook on ARM due to overhead from extra additions/subtractions and
// borrow handling. The schoolbook version above is used.

/**
 * Extra large multiplication mod 2^89-1.
 **/
static inline __uint128_t extra_large_mult_mod(__uint128_t a, __uint128_t b) {
    return extra_large_mult_add_mod(a, b, 0);
}

#endif  // _MULTIPLICATION_ARM_H_
