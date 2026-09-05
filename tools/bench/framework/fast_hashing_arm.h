/* ***********************************************
 * Hash functions for ARM NEON
 * Equivalent to fast_hashing.h but using ARM intrinsics
 * ***********************************************/

#ifndef _FAST_HASHING_ARM_H_
#define _FAST_HASHING_ARM_H_

#include <arm_neon.h>
#include <cstdint>
#include <type_traits>
#include <vector>

#ifdef DEBUG
#include <cassert>
#endif

#include "multiplication_arm.h"
#include "randomgen.h"

using namespace std;

/* ***************************************************
 * Normal polyhash using Horner (Mersenne prime)
 * ***************************************************/

template <const int L>
class poly_64_normal {
    __uint128_t m[L];
    constexpr static __uint128_t m_p = ((__uint128_t)1 << 89) - 1;

public:
    void init() {
        for (int i = 0; i < L; i++) {
            m[i] = getRandomUInt128() >> 39;
        }
    }
    uint64_t operator()(uint64_t x) {
        __uint128_t h = m[0];
        for (int i = 1; i < L; i++) {
            h = fast_large_mult_mod(h, m[i], x);
            if (h >= m_p) h -= m_p;
        }
        return h;
    }
};

/* ***************************************************
 * Mersenne polyhash using Horner (optimized)
 * ***************************************************/

template <const int L>
class poly_64 {
    __uint128_t m[L];
    constexpr static __uint128_t m_p = ((__uint128_t)1 << 89) - 1;

public:
    void init() {
        for (int i = 0; i < L; i++) {
            m[i] = getRandomUInt128() >> 39;
        }
    }
    uint64_t operator()(uint64_t x) {
        __uint128_t h = m[0];
        for (int i = 1; i < L; i++) {
            h = fast_large_mult_mod(h, m[i], x);
        }
        if (h >= m_p) h -= m_p;
        return h;
    }
};

/* ***************************************************
 * Smart polynomials (Mersenne)
 * ***************************************************/

template <std::size_t N>
class smartpoly_64 {
    __uint128_t ms[N];
    constexpr static __uint128_t M89 = ((__uint128_t)1 << 89) - 1;

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            ms[i] = getRandomUInt128() >> 39;
        }
    }
    uint64_t operator()(uint64_t x) {
        if (N == 2) return mult2(x);
        if (N == 3) return mult3(x);
        if (N == 4) return mult4(x);
        if (N == 5) return mult5(x);
        if (N == 6) return mult6(x);
        if (N == 7) return mult7(x);
        if (N == 8) return mult8(x);
        if (N == 9) return mult9(x);
        assert(false);
        return 0;
    }

private:
    uint64_t mult2(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t P = y + ms[1];
        if (P >= M89) P -= M89;
        return P;
    }
    uint64_t mult3(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t z = fast_large_mult_mod_2(x + y + ms[1], x + 0);
        __uint128_t P = z + ms[2];
        if (P >= M89) P -= M89;
        return P;
    }
    uint64_t mult4(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t z = extra_large_mult_mod(y + ms[1], x + y + ms[2]);
        __uint128_t P = z + ms[3];
        if (P >= M89) P -= M89;
        return P;
    }
    uint64_t mult5(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t z = extra_large_mult_mod(y + ms[1], x + y + ms[2]);
        __uint128_t t = fast_large_mult_mod_2(y + z + ms[3], x + 0);
        __uint128_t P = t + ms[4];
        if (P >= M89) P -= M89;
        return P;
    }
    uint64_t mult6(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t z = fast_large_mult_mod_2(x + y + ms[1], x + 0);
        __uint128_t t = extra_large_mult_mod(y + z + ms[2], x + z + ms[3]);
        __uint128_t u = fast_large_mult_mod_2(z + ms[4], x + 0);
        __uint128_t P = t + u + ms[5];
        if (P >= M89) P -= M89;
        return P;
    }
    uint64_t mult7(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t z = extra_large_mult_mod(y + ms[1], x + ms[2]);
        __uint128_t t = fast_large_mult_mod_2(z + ms[3], x + 0);
        __uint128_t u = extra_large_mult_mod(z + ms[4], y + z + t + ms[5]);
        __uint128_t P = u + y + ms[6];
        if (P >= M89) P -= M89;
        return P;
    }
    uint64_t mult8(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t z = extra_large_mult_mod(y + ms[1], x + y + ms[2]);
        __uint128_t t = fast_large_mult_mod_2(x + ms[3], x + 0);
        __uint128_t u = extra_large_mult_mod(z + ms[4], y + z + t + ms[5]);
        __uint128_t v = fast_large_mult_mod_2(z + t + ms[6], x + 0);
        __uint128_t P = u + v + z + ms[7];
        if (P >= M89) P -= M89;
        return P;
    }
    uint64_t mult9(uint64_t input) {
        __uint128_t x = input;
        __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);
        __uint128_t z = fast_large_mult_mod_2(y + ms[1], x + 0);
        __uint128_t t = extra_large_mult_mod(y + z + ms[2], x + z + ms[3]);
        __uint128_t u = extra_large_mult_mod(x + y + z + ms[4], x + ms[5]);
        __uint128_t v = extra_large_mult_mod(x + y + t + ms[6], z + ms[7]);
        __uint128_t P = u + v + ms[8];
        if (P >= M89) P -= M89;
        return P;
    }
};

/* ***************************************************
 * Motzkin's quartic over the Mersenne prime p = 2^61 - 1
 * (4-wise independent, two multiplications)
 *
 *   y = x (x + b0) + b1,      P = y (y + x + b2) + b3
 *
 * Expanded:  P = x^4 + (2 b0 + 1) x^3 + (b0^2 + b0 + 2 b1 + b2) x^2
 *               + (b1 (2 b0 + 1) + b0 b2) x + (b1^2 + b1 b2 + b3).
 * In odd characteristic the key map (b0,b1,b2,b3) -> (a3,a2,a1,a0) is a
 * bijection onto the monic quartics, with explicit decoder
 *   b0 = (a3 - 1)/2,  c = a2 - b0^2 - b0,  b1 = a1 - b0 c,
 *   b2 = c - 2 b1,    b3 = a0 - b1^2 - b1 b2,
 * so uniform keys give a uniformly random monic quartic and the hash is
 * exactly 4-wise independent on the universe [p].  (Over GF(2^64) the same
 * circuit has a3 = 2 b0 + 1 = 1 and is only 3-wise: see smartcl_64<4>.)
 * 64-bit inputs are folded modulo p (x and x + p collide); the output is
 * fully reduced into [0, p).
 *
 * The arithmetic is lazy: values stay below 2^64 and are only folded with
 * 2^61 = 1 (mod p).  The bound at each step is noted inline; all of them
 * are exercised by `bench_tabrows selftest` (extreme keys and inputs,
 * compared against Horner evaluation of the expanded quartic).
 * ***************************************************/

class motzkin_61 {
  uint64_t b[4];
  constexpr static uint64_t P61 = ((uint64_t)1 << 61) - 1;

  // v mod p (lazily): (v mod 2^61) + (v >> 61) < 2^61 + 8 for any 64-bit v.
  static inline uint64_t fold(uint64_t v) { return (v & P61) + (v >> 61); }
  // a * b mod p (lazily): one 64x64->128 product and one fold.  Requires
  // a * b < 7 * 2^122 so that the fold cannot overflow; the result is
  // < 2^61 + (a * b >> 61).
  static inline uint64_t mul(uint64_t a, uint64_t b) {
    __uint128_t z = (__uint128_t)a * b;
    return ((uint64_t)z & P61) + (uint64_t)(z >> 61);
  }

 public:
  void init() {
    for (int i = 0; i < 4; i++) {
      do { b[i] = getRandomUInt64() >> 3; } while (b[i] >= P61);  // uniform in [0, p)
    }
  }
  void set_keys(uint64_t b0, uint64_t b1, uint64_t b2, uint64_t b3) {
    b[0] = b0; b[1] = b1; b[2] = b2; b[3] = b3;
  }
  const uint64_t* keys() const { return b; }
  uint64_t operator()(uint64_t x) {
    x = fold(x);                                 // x < 2^61 + 8,  x + b0 < 2^62 + 8
    uint64_t y = fold(mul(x, x + b[0]) + b[1]);  // product < 2^123 + 2^66,  y < 2^61 + 4
    uint64_t t = y + x + b[2];                   // t < 3 * 2^61 + 12
    uint64_t P = mul(y, t) + b[3];               // product < 3 * 2^122 + 2^66,  P < 5 * 2^61 + 32
    P = fold(P);                                 // P < 2^61 + 5
    return P - (P61 & (0 - (uint64_t)(P >= P61)));  // canonical [0, p), branch-free
  }
};

/* ***************************************************
 * Carryless multiplication (Horner) - GF(2^64)
 * ***************************************************/

template <std::size_t N>
class carryless_64 {
    uint8x16_t ms[(N + 1) / 2];

public:
    void init() {
        for (std::size_t i = 0; i < (N + 1) / 2; ++i) {
            ms[i] = make128(getRandomUInt64(), getRandomUInt64());
        }
    }
    uint64_t operator()(uint64_t input) {
        uint8x16_t x = from64(input);
        uint8x16_t h = ms[0];
        if ((N & 1) == 0) {
            h = xor128(gf64_mult(h, x), upper(ms[0]));
        }
        for (size_t i = 1; i < (N + 1) / 2; i++) {
            h = xor128(gf64_mult(h, x), ms[i]);
            h = xor128(gf64_mult(h, x), upper(ms[i]));
        }
        return lower64(h);
    }
};

/* ***************************************************
 * Fast reduction helper (3-PMULL, faster than table on ARM)
 * ***************************************************/

static inline uint8x16_t reduce_gf64(uint8x16_t ab) {
    uint8x16_t r = from64(27);
    uint8x16_t xr = poly_to_u8(clmul_hi_lo(ab, r));
    uint8x16_t zr = poly_to_u8(clmul_hi_lo(xr, r));
    return xor128(xor128(ab, xr), zr);
}

// Vector multiply with fast reduction
static inline uint8x16_t vmul(uint8x16_t a, uint8x16_t b) {
    return reduce_gf64(poly_to_u8(clmul_lo_lo(a, b)));
}

// Scalar multiply helper
static inline uint64_t smul(uint64_t a, uint64_t b) {
    return vgetq_lane_u64(vreinterpretq_u64_u8(
        reduce_gf64(poly_to_u8(clmul_lo_lo(from64(a), from64(b))))), 0);
}

/* ***************************************************
 * Lemire/Horner - GF(2^64) with scalar keys
 * ***************************************************/

template <std::size_t N>
class lemire_64 {
    uint64_t k[N];  // Scalar key storage

public:
    void init() {
        for (std::size_t i = 0; i < N; ++i) {
            k[i] = getRandomUInt64();
        }
    }
    uint64_t operator()(uint64_t x) {
        uint64_t h = k[0];
        for (std::size_t i = 1; i < N; ++i) {
            h = smul(h, x) ^ k[i];
        }
        return h;
    }
};

/* ***************************************************
 * Estrin's scheme - GF(2^64) with scalar keys
 * Parallel evaluation exposing ILP
 * ***************************************************/

template <std::size_t N>
class estrin_64 {
    uint64_t k[N];  // Scalar key storage

public:
    void init() {
        for (size_t i = 0; i < N; i++)
            k[i] = getRandomUInt64();
    }
    uint64_t operator()(uint64_t x) {
        if constexpr (N == 2) return mult2(x);
        else if constexpr (N == 3) return mult3(x);
        else if constexpr (N == 4) return mult4(x);
        else if constexpr (N == 5) return mult5(x);
        else if constexpr (N == 6) return mult6(x);
        else if constexpr (N == 7) return mult7(x);
        else if constexpr (N == 8) return mult8(x);
        else if constexpr (N == 9) return mult9(x);
        else { assert(false); return 0; }
    }

private:
    // Estrin: evaluate polynomial by pairing coefficients
    // P(x) = c0 + c1*x + c2*x^2 + ... = (c0 + c1*x) + x^2*(c2 + c3*x) + ...
    uint64_t mult2(uint64_t x) {
        // k0 + k1*x
        return smul(k[0], x) ^ k[1];
    }
    uint64_t mult3(uint64_t x) {
        uint64_t x2 = smul(x, x);
        uint64_t c0 = smul(k[0], x) ^ k[1];  // k0 + k1*x
        return smul(k[2], x2) ^ c0;          // k2*x^2 + c0
    }
    uint64_t mult4(uint64_t x) {
        uint64_t x2 = smul(x, x);
        uint64_t c0 = smul(k[0], x) ^ k[1];
        uint64_t c1 = smul(k[2], x) ^ k[3];
        return smul(c1, x2) ^ c0;
    }
    uint64_t mult5(uint64_t x) {
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t c0 = smul(k[0], x) ^ k[1];
        uint64_t c1 = smul(k[2], x) ^ k[3];
        uint64_t d0 = smul(c1, x2) ^ c0;
        return smul(k[4], x4) ^ d0;
    }
    uint64_t mult6(uint64_t x) {
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t c0 = smul(k[0], x) ^ k[1];
        uint64_t c1 = smul(k[2], x) ^ k[3];
        uint64_t c2 = smul(k[4], x) ^ k[5];
        uint64_t d0 = smul(c1, x2) ^ c0;
        return smul(c2, x4) ^ d0;
    }
    uint64_t mult7(uint64_t x) {
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t c0 = smul(k[0], x) ^ k[1];
        uint64_t c1 = smul(k[2], x) ^ k[3];
        uint64_t c2 = smul(k[4], x) ^ k[5];
        uint64_t d0 = smul(c1, x2) ^ c0;
        uint64_t d1 = smul(k[6], x2) ^ c2;
        return smul(d1, x4) ^ d0;
    }
    uint64_t mult8(uint64_t x) {
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t c0 = smul(k[0], x) ^ k[1];
        uint64_t c1 = smul(k[2], x) ^ k[3];
        uint64_t c2 = smul(k[4], x) ^ k[5];
        uint64_t c3 = smul(k[6], x) ^ k[7];
        uint64_t d0 = smul(c1, x2) ^ c0;
        uint64_t d1 = smul(c3, x2) ^ c2;
        return smul(d1, x4) ^ d0;
    }
    uint64_t mult9(uint64_t x) {
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t x8 = smul(x4, x4);
        uint64_t c0 = smul(k[0], x) ^ k[1];
        uint64_t c1 = smul(k[2], x) ^ k[3];
        uint64_t c2 = smul(k[4], x) ^ k[5];
        uint64_t c3 = smul(k[6], x) ^ k[7];
        uint64_t d0 = smul(c1, x2) ^ c0;
        uint64_t d1 = smul(c3, x2) ^ c2;
        uint64_t e0 = smul(d1, x4) ^ d0;
        return smul(k[8], x8) ^ e0;
    }
};

/* ***************************************************
 * Rabin-Winograd - GF(2^64) with scalar keys
 * Uses smul for all multiplications
 * ***************************************************/

template <std::size_t N>
class rw_64 {
    uint64_t k[N];  // Scalar keys

public:
    void init() {
        for (size_t i = 0; i < N; i++)
            k[i] = getRandomUInt64();
    }
    uint64_t operator()(uint64_t x) {
        if constexpr (N == 9) return mult9(x);
        else if constexpr (N == 8) return mult8(x);
        else if constexpr (N == 7) return mult7(x);
        else if constexpr (N == 6) return mult6(x);
        else if constexpr (N == 5) return mult5(x);
        else if constexpr (N == 4) return mult4(x);
        else if constexpr (N == 3) return mult3(x);
        else if constexpr (N == 2) return mult2(x);
        else { assert(false); return 0; }
    }

private:
    // R-W algorithm using scalar multiplies
    // Key mapping: k[0]=M0, k[1]=M1, k[2]=M2, etc.
    uint64_t mult2(uint64_t x) {
        // H1 = x + M0, H2 = H1*x + M1
        return smul(x ^ k[0], x) ^ k[1];
    }
    uint64_t mult3(uint64_t x) {
        // x2 = x*x, H1 = x+M0, G1 = x+M1, H3 = H1*(x2+M2) + G1
        uint64_t x2 = smul(x, x);
        return smul(x ^ k[0], x2 ^ k[2]) ^ (x ^ k[1]);
    }
    uint64_t mult4(uint64_t x) {
        // Same as mult3 + one more Horner step
        uint64_t x2 = smul(x, x);
        uint64_t h3 = smul(x ^ k[0], x2 ^ k[2]) ^ (x ^ k[1]);
        return smul(h3, x) ^ k[3];
    }
    uint64_t mult5(uint64_t x) {
        // mult4 + parallel term x^4 * (x + M4)
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t h3 = smul(x ^ k[0], x2 ^ k[2]) ^ (x ^ k[1]);
        uint64_t h4 = smul(h3, x) ^ k[3];
        return h4 ^ smul(x4, x ^ k[4]);
    }
    uint64_t mult6(uint64_t x) {
        // Split into two chains that merge
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t h3 = smul(x ^ k[0], x2 ^ k[2]) ^ (x ^ k[1]);
        uint64_t h4 = smul(h3, x) ^ k[5];
        uint64_t g2 = smul(x ^ k[3], x) ^ k[4];
        return smul(g2, x4) ^ h4;
    }
    uint64_t mult7(uint64_t x) {
        // Two parallel chains that merge at the end
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t h3 = smul(x ^ k[0], x2 ^ k[4]) ^ (x ^ k[1]);
        uint64_t g3 = smul(x ^ k[3], x2 ^ k[5]) ^ (x ^ k[2]);
        return smul(g3, x4 ^ k[6]) ^ h3;
    }
    uint64_t mult8(uint64_t x) {
        // mult7 + one more Horner step
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t h3 = smul(x ^ k[0], x2 ^ k[4]) ^ (x ^ k[1]);
        uint64_t g3 = smul(x ^ k[3], x2 ^ k[5]) ^ (x ^ k[2]);
        uint64_t h7 = smul(g3, x4 ^ k[6]) ^ h3;
        return smul(h7, x) ^ k[7];
    }
    uint64_t mult9(uint64_t x) {
        // mult8 + parallel term x^8 * (x + M5)
        uint64_t x2 = smul(x, x);
        uint64_t x4 = smul(x2, x2);
        uint64_t x8 = smul(x4, x4);
        uint64_t h3 = smul(x ^ k[0], x2 ^ k[4]) ^ (x ^ k[1]);
        uint64_t g3 = smul(x ^ k[3], x2 ^ k[7]) ^ (x ^ k[2]);
        uint64_t h7 = smul(g3, x4 ^ k[6]) ^ h3;
        uint64_t h8 = smul(h7, x) ^ k[8];
        return smul(x ^ k[5], x8) ^ h8;
    }
};

/* ***************************************************
 * Smart polynomials - GF(2^64)
 * Uses scalar key storage for better performance on ARM
 * Uses 3-PMULL reduction (faster than table lookup on ARM)
 * ***************************************************/

// Helper: fast 3-PMULL reduction (faster than table lookup on Apple Silicon)
static inline uint8x16_t reduce_fast(uint8x16_t ab) {
    uint8x16_t r = from64(27);
    uint8x16_t xr = poly_to_u8(clmul_hi_lo(ab, r));
    uint8x16_t zr = poly_to_u8(clmul_hi_lo(xr, r));
    return xor128(xor128(ab, xr), zr);
}

// Helper: scalar multiply - takes two uint64_t values, returns result as uint64_t
static inline uint64_t slemul(uint64_t a, uint64_t b) {
    uint8x16_t result = reduce_fast(poly_to_u8(clmul_lo_lo(from64(a), from64(b))));
    return vgetq_lane_u64(vreinterpretq_u64_u8(result), 0);
}

template <std::size_t N>
class smartcl_64 {
    // Store keys as scalar pairs for better codegen
    uint64_t k[N + 1];  // (N+1)/2 pairs = N+1 values (rounded up)

public:
    void init() {
        for (size_t i = 0; i < N + 1; i++)
            k[i] = getRandomUInt64();
    }
    uint64_t operator()(uint64_t x) {
        if constexpr (N == 2) return small(x);
        else if constexpr (N == 3) return mult3(x);
        else if constexpr (N == 4) return mult4(x);
        else if constexpr (N == 5) return mult5(x);
        else if constexpr (N == 6) return mult6(x);
        else if constexpr (N == 7) return mult7(x);
        else if constexpr (N == 8) return mult8(x);
        else if constexpr (N == 9) return mult9(x);
        else { assert(false); return 0; }
    }

private:
    uint64_t small(uint64_t x) {
        uint64_t h = k[0];
        if ((N & 1) == 0) {
            h = slemul(h, x) ^ k[1];
        }
        for (std::size_t i = 1; i < (N + 1) / 2; ++i) {
            h = slemul(h, x) ^ k[i*2];
            h = slemul(h, x) ^ k[i*2+1];
        }
        return h;
    }
    uint64_t mult3(uint64_t x) {
        uint64_t y = slemul(x, x);
        uint64_t z = slemul(x ^ k[0], y ^ k[1]);
        return z ^ k[2];
    }
    uint64_t mult4(uint64_t x) {
        // Motzkin's method for degree 4 with 2 multiplications:
        // y = x(x + k[0]) + k[1]
        // H = y(y + x + k[2]) + k[3]
        uint64_t y = slemul(x, x ^ k[0]) ^ k[1];
        uint64_t H = slemul(y, y ^ x ^ k[2]) ^ k[3];
        return H;
    }
    uint64_t mult5(uint64_t x) {
        uint64_t y = slemul(x, x);
        uint64_t z = slemul(y ^ k[0], x ^ y ^ k[1]);
        uint64_t w = slemul(x ^ k[2], z ^ k[3]);
        return w ^ k[4];
    }
    uint64_t mult6(uint64_t x) {
        uint64_t y = slemul(x, x ^ k[0]);
        uint64_t z = slemul(y ^ k[1], x ^ y ^ k[2]);
        uint64_t t = slemul(z ^ k[3], y);
        uint64_t u = slemul(x ^ k[4], x);
        return t ^ u ^ k[5];
    }
    uint64_t mult7(uint64_t x) {
        uint64_t y = slemul(x, x ^ k[0]);
        uint64_t z = slemul(x ^ k[1], y ^ k[2]);
        uint64_t t = slemul(z ^ k[3], z);
        uint64_t u = slemul(x ^ y ^ t ^ k[4], x ^ k[5]);
        return u ^ k[6];
    }
    uint64_t mult8(uint64_t x) {
        uint64_t y = slemul(x, x ^ k[0]);
        uint64_t z = slemul(x, y);
        uint64_t t = slemul(y ^ k[1], y ^ z ^ k[2]);
        uint64_t u = slemul(x ^ y ^ t ^ k[3], z ^ k[4]);
        uint64_t v = slemul(x ^ k[5], y ^ k[6]);
        return u ^ v ^ k[7];
    }
    uint64_t mult9(uint64_t x) {
        uint64_t y = slemul(x, x);
        uint64_t z = slemul(k[0] ^ x, k[1] ^ y);
        uint64_t u = slemul(k[2] ^ x, k[3] ^ y);
        uint64_t t = slemul(k[4] ^ z, k[5] ^ y ^ z);
        uint64_t v = slemul(k[6] ^ t, k[7] ^ x ^ z);
        return k[8] ^ u ^ v;
    }
};

/* ***************************************************
 * The two quartic circuits over GF(2^64) as separately named classes, so
 * that both exist on both platforms with the same names.  (Here
 * smartcl_64<4>::mult4 is Motzkin's two-multiplication circuit; in
 * fast_hashing.h smartcl_64<4>::mult4 is the three-multiplication circuit.
 * Both existing classes are left untouched.)
 *
 * quartic2_64 -- Motzkin's quartic, two multiplications:
 *   y = x (x + a0) + a1,   P = y (y + x + a2) + a3
 *     = x^4 + (2 a0 + 1) x^3 + (a0^2 + a0 + a2) x^2 + (a0 a2 + a1) x
 *       + (a1^2 + a1 a2 + a3).
 *   In characteristic 2 the x^3 coefficient is 2 a0 + 1 = 1 for every key,
 *   so the family is exactly 3-wise independent (the other three
 *   coefficients are uniform).  Same circuit as motzkin_61 over 2^61 - 1,
 *   where it is 4-wise.
 *
 * quartic3_64 -- x Q3(x) + a3 with Q3 the two-multiplication cubic, three
 * multiplications:
 *   y = x^2,  z = (x + a0)(y + a1),  t = (z + a2) x,  P = t + a3
 *     = x^4 + a0 x^3 + a1 x^2 + (a0 a1 + a2) x + a3.
 *   The key map is a bijection onto the monic quartics, with decoder
 *   a0 = c3, a1 = c2, a2 = c1 + c3 c2, a3 = c0, so the hash is 4-wise.
 *
 * Both are checked against Horner on the expanded polynomial (and the
 * quartic3_64 decoder round-trip) by `bench_tabrows selftest`.
 * ***************************************************/

class quartic2_64 {
    uint64_t k[4];

public:
    void init() {
        for (int i = 0; i < 4; i++) k[i] = getRandomUInt64();
    }
    void set_keys(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3) {
        k[0] = a0; k[1] = a1; k[2] = a2; k[3] = a3;
    }
    uint64_t operator()(uint64_t x) {
        // Identical to smartcl_64<4>::mult4 in this file.
        uint64_t y = slemul(x, x ^ k[0]) ^ k[1];      // y = x (x + a0) + a1
        return slemul(y, y ^ x ^ k[2]) ^ k[3];        // P = y (y + x + a2) + a3
    }
};

class quartic3_64 {
    uint64_t k[4];

public:
    void init() {
        for (int i = 0; i < 4; i++) k[i] = getRandomUInt64();
    }
    void set_keys(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3) {
        k[0] = a0; k[1] = a1; k[2] = a2; k[3] = a3;
    }
    uint64_t operator()(uint64_t x) {
        uint64_t y = slemul(x, x);                    // y = x^2
        uint64_t z = slemul(x ^ k[0], y ^ k[1]);      // z = (x + a0) (y + a1)
        uint64_t t = slemul(z ^ k[2], x);             // t = (z + a2) x
        return t ^ k[3];                              // P = t + a3
    }
};

/* ***************************************************
 * Tabulation hashing (for comparison)
 * ***************************************************/

class tabulation_64 {
    uint64_t table[8][256];

public:
    void init() {
        for (int i = 0; i < 8; i++)
            for (int j = 0; j < 256; j++)
                table[i][j] = getRandomUInt64();
    }
    uint64_t operator()(uint64_t x) {
        uint64_t res = 0;
        for (int i = 0; i < 8; i++) {
            res ^= table[i][(uint8_t)x];
            x >>= 8;
        }
        return res;
    }
};

#endif  // _FAST_HASHING_ARM_H_
