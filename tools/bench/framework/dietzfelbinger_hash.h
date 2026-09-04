/* ***********************************************
 * Dietzfelbinger's k-wise independent hashing
 * Using integer arithmetic mod 2^W (no finite field)
 *
 * Based on: Martin Dietzfelbinger, "Universal Hashing via
 * Integer Arithmetic Without Primes, Revisited" (2018)
 * https://link.springer.com/content/pdf/10.1007/978-3-319-98355-4_15.pdf
 *
 * The construction uses polynomial evaluation mod 2^W with
 * the top bits extracted as the hash. Theorem 3(b) gives
 * exact k-wise independence when:
 *   W >= (n-1) + l + ceil(log2(k choose 2))
 * where n = input bits, l = output bits, k = independence.
 *
 * For 64-bit keys -> 64-bit hash (Theorem 3b bound):
 *   W >= 127 + ceil(log2(k*(k-1)/2))
 *
 *   k=2: W >= 127  -> W=128 works ✓
 *   k=3: W >= 129  -> W=128 INVALID, need W=192
 *   k=4: W >= 130  -> need W=192
 *   k=5: W >= 131  -> need W=192
 *   k=9: W >= 133  -> need W=192
 *
 * IMPORTANT: Using W=128 for k>=3 does NOT give true k-wise independence!
 * The hash function will have subtle correlations. Use W=192 for k>=3.
 *
 * Trade-off vs carryless GF(2^64):
 *   - Dietzfelbinger uses standard integer multiply (128-bit for k>=2)
 *   - GF(2^64) uses PCLMULQDQ/PMULL which is a single instruction
 *   - 128-bit multiply requires ~3 MUL64 instructions
 *   - Higher k needs larger W, making the gap worse
 * ***********************************************/

#ifndef _DIETZFELBINGER_HASH_H_
#define _DIETZFELBINGER_HASH_H_

#include <cstdint>
#include <cassert>
#include "randomgen.h"

/* ***************************************************
 * Helper: compute required W for exact k-wise independence
 * W >= (n-1) + l + ceil(log2(k choose 2))
 * ***************************************************/

static inline unsigned dietz_binom2(unsigned k) {
    // k choose 2 = k*(k-1)/2
    return (k < 2) ? 0 : (k * (k - 1)) / 2;
}

static inline unsigned dietz_ceil_log2(unsigned x) {
    if (x <= 1) return 0;
    return 32u - __builtin_clz(x - 1);
}

static inline unsigned dietz_required_W(unsigned n_bits, unsigned out_bits, unsigned k) {
    // Theorem 3(b): W >= (n-1) + l + ceil(log2(k choose 2))
    unsigned c = dietz_binom2(k);
    return (n_bits - 1) + out_bits + dietz_ceil_log2(c);
}

/* ***************************************************
 * W=128 implementation using __uint128_t
 * Suitable for 64-bit keys when k=2 ONLY
 *
 * For 64->64 with k=2: need W>=127, so W=128 works
 * For 64->64 with k>=3: need W>=129, so W=128 is INVALID
 * ***************************************************/

template <std::size_t N>
class dietz_128 {
    __uint128_t a[N];  // k coefficients in Z_{2^128}

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            a[i] = getRandomUInt128();
        }
    }

    uint64_t operator()(uint64_t x) {
        // Horner's rule: acc = a[N-1]*x + a[N-2], then acc*x + a[N-3], etc.
        // All arithmetic is mod 2^128 (automatic wraparound)
        __uint128_t acc = a[N - 1];
        for (size_t i = N - 1; i-- > 0;) {
            acc = acc * (__uint128_t)x + a[i];
        }
        // Return top 64 bits (the hash)
        return (uint64_t)(acc >> 64);
    }
};

/* ***************************************************
 * W=128 with optimized multiply: (u128 * u64) mod 2^128
 * Uses only 2 MUL64 instead of 4 for full u128*u128
 * ***************************************************/

static inline __attribute__((always_inline))
__uint128_t dietz_mul128_64(__uint128_t a, uint64_t x) {
    // (a_hi * 2^64 + a_lo) * x mod 2^128
    // = a_lo * x + (a_hi * x) << 64   (mod 2^128)
    uint64_t a_lo = (uint64_t)a;
    uint64_t a_hi = (uint64_t)(a >> 64);

    __uint128_t p0 = (__uint128_t)a_lo * x;  // 128-bit result
    uint64_t p1_lo = a_hi * x;               // only need low 64 bits

    return p0 + ((__uint128_t)p1_lo << 64);  // mod 2^128 automatically
}

template <std::size_t N>
class dietz_128_opt {
    __uint128_t a[N];

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            a[i] = getRandomUInt128();
        }
    }

    uint64_t operator()(uint64_t x) {
        __uint128_t acc = a[N - 1];
        for (size_t i = N - 1; i-- > 0;) {
            acc = dietz_mul128_64(acc, x) + a[i];
        }
        return (uint64_t)(acc >> 64);
    }
};

/* ***************************************************
 * W=128 fully unrolled Horner
 * Manual unrolling for each N to help compiler optimization
 *
 * Note: For integer polynomials, we cannot reduce the number
 * of multiplications like we can for GF(2^64). The best we
 * can do is k-1 multiplies with Horner's rule.
 * ***************************************************/

template <std::size_t N>
class dietz_128_estrin {
    __uint128_t a[N];

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            a[i] = getRandomUInt128();
        }
    }

    uint64_t operator()(uint64_t x) {
        // Fully unrolled Horner for each N
        // P(x) = a[0] + x*(a[1] + x*(a[2] + ... + x*a[N-1]))
        //      = (...((a[N-1]*x + a[N-2])*x + a[N-3])*x + ... + a[0])

        if constexpr (N == 2) {
            __uint128_t h = dietz_mul128_64(a[1], x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else if constexpr (N == 3) {
            __uint128_t h = dietz_mul128_64(a[2], x) + a[1];
            h = dietz_mul128_64(h, x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else if constexpr (N == 4) {
            __uint128_t h = dietz_mul128_64(a[3], x) + a[2];
            h = dietz_mul128_64(h, x) + a[1];
            h = dietz_mul128_64(h, x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else if constexpr (N == 5) {
            __uint128_t h = dietz_mul128_64(a[4], x) + a[3];
            h = dietz_mul128_64(h, x) + a[2];
            h = dietz_mul128_64(h, x) + a[1];
            h = dietz_mul128_64(h, x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else if constexpr (N == 6) {
            __uint128_t h = dietz_mul128_64(a[5], x) + a[4];
            h = dietz_mul128_64(h, x) + a[3];
            h = dietz_mul128_64(h, x) + a[2];
            h = dietz_mul128_64(h, x) + a[1];
            h = dietz_mul128_64(h, x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else if constexpr (N == 7) {
            __uint128_t h = dietz_mul128_64(a[6], x) + a[5];
            h = dietz_mul128_64(h, x) + a[4];
            h = dietz_mul128_64(h, x) + a[3];
            h = dietz_mul128_64(h, x) + a[2];
            h = dietz_mul128_64(h, x) + a[1];
            h = dietz_mul128_64(h, x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else if constexpr (N == 8) {
            __uint128_t h = dietz_mul128_64(a[7], x) + a[6];
            h = dietz_mul128_64(h, x) + a[5];
            h = dietz_mul128_64(h, x) + a[4];
            h = dietz_mul128_64(h, x) + a[3];
            h = dietz_mul128_64(h, x) + a[2];
            h = dietz_mul128_64(h, x) + a[1];
            h = dietz_mul128_64(h, x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else if constexpr (N == 9) {
            __uint128_t h = dietz_mul128_64(a[8], x) + a[7];
            h = dietz_mul128_64(h, x) + a[6];
            h = dietz_mul128_64(h, x) + a[5];
            h = dietz_mul128_64(h, x) + a[4];
            h = dietz_mul128_64(h, x) + a[3];
            h = dietz_mul128_64(h, x) + a[2];
            h = dietz_mul128_64(h, x) + a[1];
            h = dietz_mul128_64(h, x) + a[0];
            return (uint64_t)(h >> 64);
        }
        else {
            // Generic loop for larger N
            __uint128_t h = a[N - 1];
            for (size_t i = N - 1; i-- > 0;) {
                h = dietz_mul128_64(h, x) + a[i];
            }
            return (uint64_t)(h >> 64);
        }
    }
};

/* ***************************************************
 * W=192 implementation using 3x64-bit limbs
 * More efficient than W=256 for k=4-9
 *
 * For 64->64:
 *   k=4: need W>=129 -> W=192 works
 *   k=5: need W>=130 -> W=192 works
 *   k=9: need W>=132 -> W=192 works
 * ***************************************************/

struct u192 {
    uint64_t w[3];  // w[0] = least significant, w[2] = most significant

    u192() : w{0, 0, 0} {}
    u192(uint64_t v0, uint64_t v1, uint64_t v2) : w{v0, v1, v2} {}
};

static inline __attribute__((always_inline))
u192 dietz_u192_add(u192 a, u192 b) {
    u192 r;
    __uint128_t t0 = (__uint128_t)a.w[0] + b.w[0];
    r.w[0] = (uint64_t)t0;

    __uint128_t t1 = (__uint128_t)a.w[1] + b.w[1] + (t0 >> 64);
    r.w[1] = (uint64_t)t1;

    r.w[2] = a.w[2] + b.w[2] + (uint64_t)(t1 >> 64);
    return r;
}

static inline __attribute__((always_inline))
u192 dietz_u192_mul_u64(u192 a, uint64_t x) {
    // Compute (a * x) mod 2^192 where x is 64-bit
    // Uses 3 independent 64x64->128 multiplies
    u192 r;

    __uint128_t p0 = (__uint128_t)a.w[0] * x;
    __uint128_t p1 = (__uint128_t)a.w[1] * x;
    uint64_t p2_lo = a.w[2] * x;  // only need low 64 bits

    r.w[0] = (uint64_t)p0;

    __uint128_t t1 = p1 + (p0 >> 64);
    r.w[1] = (uint64_t)t1;

    r.w[2] = p2_lo + (uint64_t)(t1 >> 64);
    return r;
}

// Fused multiply-add: (a * x + b) mod 2^192
// More efficient than separate mul and add
static inline __attribute__((always_inline))
u192 dietz_u192_muladd(u192 a, uint64_t x, u192 b) {
    // Compute (a * x + b) mod 2^192
    __uint128_t p0 = (__uint128_t)a.w[0] * x;
    __uint128_t p1 = (__uint128_t)a.w[1] * x;
    uint64_t p2_lo = a.w[2] * x;

    u192 r;

    // Step 1: low64(p0) + b.w[0]
    // Must cast to __uint128_t BEFORE adding to capture carry
    __uint128_t s0 = (__uint128_t)(uint64_t)p0 + b.w[0];
    r.w[0] = (uint64_t)s0;

    // Step 2: low64(p1 + high64(p0)) + b.w[1] + carry from s0
    __uint128_t mid = p1 + (p0 >> 64);
    __uint128_t s1 = (__uint128_t)(uint64_t)mid + b.w[1] + (s0 >> 64);
    r.w[1] = (uint64_t)s1;

    // Step 3: p2_lo + high64(mid) + b.w[2] + carry from s1
    r.w[2] = p2_lo + (uint64_t)(mid >> 64) + b.w[2] + (uint64_t)(s1 >> 64);
    return r;
}

template <std::size_t N>
class dietz_192 {
    u192 a[N];

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            a[i].w[0] = getRandomUInt64();
            a[i].w[1] = getRandomUInt64();
            a[i].w[2] = getRandomUInt64();
        }
    }

    uint64_t operator()(uint64_t x) {
        u192 acc = a[N - 1];
        for (size_t i = N - 1; i-- > 0;) {
            acc = dietz_u192_muladd(acc, x, a[i]);  // fused multiply-add
        }
        // Return top 64 bits (from most significant limb)
        return acc.w[2];
    }
};

/* ***************************************************
 * W=192 with Estrin's scheme
 * Combines smaller modulus with ILP
 * ***************************************************/

static inline u192 dietz_u192_mul_u192(u192 a, u192 b) {
    // Full 192x192 multiply mod 2^192
    // We only need the high 192 bits, but for simplicity compute mod 2^192
    u192 r;

    // a = a0 + a1*2^64 + a2*2^128
    // b = b0 + b1*2^64 + b2*2^128
    // a*b mod 2^192 = a0*b0 + (a0*b1 + a1*b0)*2^64 + (a0*b2 + a1*b1 + a2*b0)*2^128

    __uint128_t p00 = (__uint128_t)a.w[0] * b.w[0];
    __uint128_t p01 = (__uint128_t)a.w[0] * b.w[1];
    __uint128_t p10 = (__uint128_t)a.w[1] * b.w[0];
    uint64_t p02 = a.w[0] * b.w[2];  // only need low 64 bits
    uint64_t p11 = a.w[1] * b.w[1];  // only need low 64 bits
    uint64_t p20 = a.w[2] * b.w[0];  // only need low 64 bits

    r.w[0] = (uint64_t)p00;

    __uint128_t mid = (p00 >> 64) + p01 + p10;
    r.w[1] = (uint64_t)mid;

    r.w[2] = (uint64_t)(mid >> 64) + p02 + p11 + p20;
    return r;
}

template <std::size_t N>
class dietz_192_estrin {
    u192 a[N];

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            a[i].w[0] = getRandomUInt64();
            a[i].w[1] = getRandomUInt64();
            a[i].w[2] = getRandomUInt64();
        }
    }

    uint64_t operator()(uint64_t x) {
        // Use Horner with fused muladd
        // Estrin would need u192 squaring which adds complexity
        u192 acc = a[N - 1];
        for (size_t i = N - 1; i-- > 0;) {
            acc = dietz_u192_muladd(acc, x, a[i]);
        }
        return acc.w[2];
    }
};

/* ***************************************************
 * W=256 implementation using 4x64-bit limbs
 * Needed only if W=192 is insufficient (k very large)
 * ***************************************************/

struct u256 {
    uint64_t w[4];  // w[0] = least significant, w[3] = most significant

    u256() : w{0, 0, 0, 0} {}
    u256(uint64_t v0, uint64_t v1, uint64_t v2, uint64_t v3)
        : w{v0, v1, v2, v3} {}
};

static inline __attribute__((always_inline))
u256 dietz_u256_add(u256 a, u256 b) {
    u256 r;
    __uint128_t t0 = (__uint128_t)a.w[0] + b.w[0];
    r.w[0] = (uint64_t)t0;

    __uint128_t t1 = (__uint128_t)a.w[1] + b.w[1] + (t0 >> 64);
    r.w[1] = (uint64_t)t1;

    __uint128_t t2 = (__uint128_t)a.w[2] + b.w[2] + (t1 >> 64);
    r.w[2] = (uint64_t)t2;

    r.w[3] = a.w[3] + b.w[3] + (uint64_t)(t2 >> 64);
    return r;  // overflow discarded (mod 2^256)
}

static inline __attribute__((always_inline))
u256 dietz_u256_mul_u64(u256 a, uint64_t x) {
    // Compute (a * x) mod 2^256 where x is 64-bit
    // Uses 4 independent 64x64->128 multiplies
    u256 r;

    __uint128_t p0 = (__uint128_t)a.w[0] * x;
    __uint128_t p1 = (__uint128_t)a.w[1] * x;
    __uint128_t p2 = (__uint128_t)a.w[2] * x;
    uint64_t p3_lo = a.w[3] * x;  // only need low 64 bits

    r.w[0] = (uint64_t)p0;

    __uint128_t t1 = p1 + (p0 >> 64);
    r.w[1] = (uint64_t)t1;

    __uint128_t t2 = p2 + (t1 >> 64);
    r.w[2] = (uint64_t)t2;

    r.w[3] = p3_lo + (uint64_t)(t2 >> 64);
    return r;
}

// Fused multiply-add: (a * x + b) mod 2^256
static inline __attribute__((always_inline))
u256 dietz_u256_muladd(u256 a, uint64_t x, u256 b) {
    __uint128_t p0 = (__uint128_t)a.w[0] * x;
    __uint128_t p1 = (__uint128_t)a.w[1] * x;
    __uint128_t p2 = (__uint128_t)a.w[2] * x;
    uint64_t p3_lo = a.w[3] * x;

    u256 r;

    // Step 1: low64(p0) + b.w[0]
    // Must cast to __uint128_t BEFORE adding to capture carry
    __uint128_t s0 = (__uint128_t)(uint64_t)p0 + b.w[0];
    r.w[0] = (uint64_t)s0;

    // Step 2: low64(p1 + high64(p0)) + b.w[1] + carry from s0
    __uint128_t mid1 = p1 + (p0 >> 64);
    __uint128_t s1 = (__uint128_t)(uint64_t)mid1 + b.w[1] + (s0 >> 64);
    r.w[1] = (uint64_t)s1;

    // Step 3: low64(p2 + high64(mid1)) + b.w[2] + carry from s1
    __uint128_t mid2 = p2 + (mid1 >> 64);
    __uint128_t s2 = (__uint128_t)(uint64_t)mid2 + b.w[2] + (s1 >> 64);
    r.w[2] = (uint64_t)s2;

    // Step 4: p3_lo + high64(mid2) + b.w[3] + carry from s2
    r.w[3] = p3_lo + (uint64_t)(mid2 >> 64) + b.w[3] + (uint64_t)(s2 >> 64);
    return r;
}

template <std::size_t N>
class dietz_256 {
    u256 a[N];

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            // Fill with 256 bits of randomness
            a[i].w[0] = getRandomUInt64();
            a[i].w[1] = getRandomUInt64();
            a[i].w[2] = getRandomUInt64();
            a[i].w[3] = getRandomUInt64();
        }
    }

    uint64_t operator()(uint64_t x) {
        u256 acc = a[N - 1];
        for (size_t i = N - 1; i-- > 0;) {
            acc = dietz_u256_muladd(acc, x, a[i]);  // fused multiply-add
        }
        // Return top 64 bits (from the most significant limb)
        return acc.w[3];
    }
};

/* ***************************************************
 * Unified wrapper that picks appropriate W based on k
 * Uses W=128 for k=2, W=192 for k>=3
 *
 * For benchmarking, we provide both versions separately
 * so we can compare the overhead of larger W.
 * ***************************************************/

template <std::size_t N>
class dietz_auto {
    // For 64->64 hashing:
    // k=2: W=128 suffices (need W>=127)
    // k>=3: need W>=129, use W=192
    static constexpr bool use_192 = (N >= 3);

    // Storage for both variants (only one is used)
    __uint128_t a128[N];
    u192 a192[N];

public:
    void init() {
        if constexpr (use_192) {
            for (size_t i = 0; i < N; i++) {
                a192[i].w[0] = getRandomUInt64();
                a192[i].w[1] = getRandomUInt64();
                a192[i].w[2] = getRandomUInt64();
            }
        } else {
            for (size_t i = 0; i < N; i++) {
                a128[i] = getRandomUInt128();
            }
        }
    }

    uint64_t operator()(uint64_t x) {
        if constexpr (use_192) {
            u192 acc = a192[N - 1];
            for (size_t i = N - 1; i-- > 0;) {
                acc = dietz_u192_muladd(acc, x, a192[i]);
            }
            return acc.w[2];
        } else {
            __uint128_t acc = a128[N - 1];
            for (size_t i = N - 1; i-- > 0;) {
                acc = dietz_mul128_64(acc, x) + a128[i];
            }
            return (uint64_t)(acc >> 64);
        }
    }
};

/* ***************************************************
 * 2-wise special case: multiply-shift with addition
 * h(x) = ((ax + b) mod 2^128) >> 64
 *
 * This is the fastest Dietzfelbinger variant for 2-wise.
 * Uses only 2 MUL64 operations.
 * ***************************************************/

class dietz_2wise {
    __uint128_t a, b;

public:
    void init() {
        a = getRandomUInt128();
        b = getRandomUInt128();
    }

    uint64_t operator()(uint64_t x) {
        // (a * x + b) mod 2^128, then take top 64 bits
        __uint128_t y = dietz_mul128_64(a, x) + b;
        return (uint64_t)(y >> 64);
    }
};

/* ***************************************************
 * Thorup's pair-multiply-shift for 64-bit keys
 * Uses only 64-bit multiplies to get 2-wise independence
 * h(x) = ((a1 + x) * (a2 + (x >> 32)) + b) >> (64 - l)
 *
 * For l <= 32 bits output.
 * Can concatenate two outputs to get 64 bits.
 * ***************************************************/

class thorup_pair_64 {
    uint64_t a1, a2, b1, b2;

public:
    void init() {
        a1 = getRandomUInt64();
        a2 = getRandomUInt64();
        b1 = getRandomUInt64();
        b2 = getRandomUInt64();
    }

    uint64_t operator()(uint64_t x) {
        // Two 32-bit outputs concatenated to 64 bits
        // Note: This gives two approximately independent 32-bit hashes
        uint64_t x_hi = x >> 32;

        // First 32 bits: Thorup's pair-multiply-shift
        uint64_t h1 = (a1 + x) * (a2 + x_hi) + b1;
        uint32_t out1 = (uint32_t)(h1 >> 32);

        // Second 32 bits: use different random values
        // (XOR with constants then add - note parentheses for correct precedence)
        uint64_t h2 = ((a1 ^ 0x12345678ULL) + x) * ((a2 ^ 0x9abcdef0ULL) + x_hi) + b2;
        uint32_t out2 = (uint32_t)(h2 >> 32);

        return ((uint64_t)out1 << 32) | out2;
    }
};

#endif  // _DIETZFELBINGER_HASH_H_
