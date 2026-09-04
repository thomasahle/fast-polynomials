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
