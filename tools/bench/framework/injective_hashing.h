/* ***********************************************
 * Injective/Universal Hashing for x86 (PCLMULQDQ)
 *
 * x86 port of injective_hashing_arm.h.  The class bodies below are
 * copied verbatim from the ARM header; only the NEON-specific helper
 * primitives (from64 / lower64 / upper64 / xor128 / clmul_lo_lo /
 * poly_to_u8) are re-implemented on top of SSE2 + PCLMULQDQ, and the
 * NEON vector type uint8x16_t is replaced by __m128i.
 *
 * This file contains hash functions for UNIVERSAL HASHING,
 * where the stored arrays are MESSAGE DATA and the input
 * parameters (x, y) are the KEYS.
 *
 * Key insight: These constructions use O(1) key size to hash
 * variable-length messages, unlike multilinear hashing (CLNH)
 * which requires key size proportional to message size.
 *
 * Terminology:
 *   - m[], m_a[], m_b[]: Message data (the input being hashed)
 *   - x, y: Keys (random field elements, O(1) total)
 *
 * Compile: clang++ -O3 -std=c++17 -mpclmul -msse4.1
 * ***********************************************/

#ifndef _INJECTIVE_HASHING_H_
#define _INJECTIVE_HASHING_H_

#include <cstddef>
#include <cstdint>

#include "multiplication.h"
#include "randomgen.h"

/* ***************************************************
 * x86 equivalents of the NEON helpers in multiplication_arm.h
 * (same names, so the class bodies can be shared verbatim).
 * ***************************************************/

// Create a 128-bit vector from a single 64-bit value (high bits = 0)
static inline __m128i from64(uint64_t x) {
    return _mm_set_epi64x(0, x);
}

// Helper to extract lower 64 bits
static inline uint64_t lower64(__m128i v) {
    return _mm_cvtsi128_si64(v);
}

// Helper to extract upper 64 bits
static inline uint64_t upper64(__m128i v) {
    return _mm_cvtsi128_si64(_mm_srli_si128(v, 8));
}

// XOR two 128-bit vectors
static inline __m128i xor128(__m128i a, __m128i b) {
    return _mm_xor_si128(a, b);
}

// Carryless multiplication of low 64 bits of a and b
// (ARM: vmull_p64 on lane 0 of each)
static inline __m128i clmul_lo_lo(__m128i a, __m128i b) {
    return _mm_clmulepi64_si128(a, b, 0x00);
}

// On ARM this converts poly128_t -> uint8x16_t; on x86 the product is
// already an __m128i, so this is the identity.
static inline __m128i poly_to_u8(__m128i p) {
    return p;
}

/* ***************************************************
 * smul: Single multiplication in GF(2^64)
 * Takes lower 64 bits of result after reduction
 * ***************************************************/
static inline uint64_t inj_smul(uint64_t a, uint64_t b) {
    return lower64(gf64_mult(from64(a), from64(b)));
}

/* ***************************************************
 * Injective Polynomial Hashing - GF(2^64)
 *
 * Recurrence: P_0 = x, P_i = a_i + (b_i + y)(P_{i-1} + x²)
 *
 * Message: (a_1, b_1, ..., a_N, b_N) - 2N values stored in m_a[], m_b[]
 * Keys: (x, y) - just 2 random field elements (O(1) key size!)
 *
 * Uses N multiplications to hash 2N message values.
 * Compare to Horner which uses 2N-1 multiplications.
 *
 * Provides universality (collision resistance).
 * ***************************************************/

template <std::size_t N>
class univ_injective_64 {
    uint64_t m_a[N];  // First half of message data
    uint64_t m_b[N];  // Second half of message data

public:
    void init() {
        // Initialize with random "message" for benchmarking
        for (size_t i = 0; i < N; i++) {
            m_a[i] = getRandomUInt64();
            m_b[i] = getRandomUInt64();
        }
    }

    // Hash 2N message values using keys (x, y)
    // Keys: (x, y) - just 2 random field elements
    // Returns hash value in GF(2^64)
    uint64_t operator()(uint64_t x, uint64_t y) {
        uint64_t x2 = inj_smul(x, x);  // Precompute x²
        uint64_t P = x;                 // P_0 = x

        for (size_t i = 0; i < N; i++) {
            // P_i = a_i + (b_i + y) * (P_{i-1} + x²)
            P = m_a[i] ^ inj_smul(m_b[i] ^ y, P ^ x2);
        }
        return P;
    }

    // Single-key version using x³ instead of y
    // (Degree 3n polynomial, slightly worse collision bound)
    uint64_t operator()(uint64_t x) {
        uint64_t x2 = inj_smul(x, x);
        uint64_t x3 = inj_smul(x2, x);
        uint64_t P = x;

        for (size_t i = 0; i < N; i++) {
            P = m_a[i] ^ inj_smul(m_b[i] ^ x3, P ^ x2);
        }
        return P;
    }
};

/* ***************************************************
 * Lane-Interleaved Injective Hashing - GF(2^64)
 *
 * Same recurrence as univ_injective_64, but the N message pairs are
 * dealt round-robin to L independent chains ("lanes"): lane j consumes
 * the pairs i = j, j+L, j+2L, ... < N in order, starting from
 * P^(j)_0 = x.  The L multiplications of one round are independent, so
 * the multiplier pipeline can overlap them (ILP), at a cost of only
 * L-1 extra multiplications (plus O(log N) for x^D) over the
 * sequential N.
 *
 * Single key: H = sum_j P^(j)(x) * x^(jD) with D = 3*ceil(N/L) + 3,
 * strictly larger than the degree 3*ceil(N/L) + 2 of every lane
 * polynomial, so the lanes occupy disjoint degree ranges and the
 * message -> polynomial map stays injective for fixed N.
 * Degree <= (L-1)*D + 3*ceil(N/L) + 2.
 *
 * Two keys (x, y): H = sum_j P^(j) * y^j, evaluated by Horner in y.
 *
 * Message: (a_1, b_1, ..., a_N, b_N) - 2N values in m_a[], m_b[]
 * Keys: x (or x, y) - O(1) key size, as in univ_injective_64.
 * Multiplications: N + L - 1 chain/combine, +2 for x^2, x^3,
 * +O(log(N/L)) for x^D.
 *
 * The lane loop is written out in both overloads (rather than shared
 * through a helper) so the compiler keeps the L lane states in
 * registers instead of spilling them through an out-pointer.
 * ***************************************************/

template <int N, int L>
class univ_injective_lanes_64 {
    static_assert(1 <= L && L <= N, "univ_injective_lanes_64: need 1 <= L <= N");

    static constexpr int ROUNDS = (N + L - 1) / L;  // ceil(N/L): max pairs per lane
    static constexpr int FULL = N / L;              // rounds in which every lane gets a pair
    static constexpr int D = 3 * ROUNDS + 3;        // lane spacing exponent (single key)

    uint64_t m_a[N];  // First half of message data
    uint64_t m_b[N];  // Second half of message data

public:
    void init() {
        // Initialize with random "message" for benchmarking
        for (int i = 0; i < N; i++) {
            m_a[i] = getRandomUInt64();
            m_b[i] = getRandomUInt64();
        }
    }

    const uint64_t* a() const { return m_a; }
    const uint64_t* b() const { return m_b; }

    // Single-key version: lanes use x^3, combined with x^D.
    uint64_t operator()(uint64_t x) {
        uint64_t x2 = inj_smul(x, x);
        uint64_t x3 = inj_smul(x2, x);

        // L interleaved chains, P^(j)_0 = x.  Round r hands pair r*L + j
        // to lane j; the inner loop has a constexpr trip count and its
        // L multiplications are mutually independent.
        uint64_t P[L];
        for (int j = 0; j < L; j++) P[j] = x;
        for (int r = 0; r < FULL; r++) {
            for (int j = 0; j < L; j++) {
                const int i = r * L + j;
                P[j] = m_a[i] ^ inj_smul(m_b[i] ^ x3, P[j] ^ x2);
            }
        }
        // Tail round: the remaining N mod L pairs go to lanes 0..N%L-1.
        for (int j = 0; j < N - FULL * L; j++) {
            const int i = FULL * L + j;
            P[j] = m_a[i] ^ inj_smul(m_b[i] ^ x3, P[j] ^ x2);
        }

        // xD = x^D = (x^3)^E with E = ROUNDS + 1, by left-to-right
        // square-and-multiply on the constexpr exponent E (unrolls).
        constexpr int E = ROUNDS + 1;
        constexpr int top = []() {
            int t = 0;
            while ((E >> (t + 1)) != 0) t++;
            return t;
        }();
        uint64_t xD = x3;
        for (int bit = top - 1; bit >= 0; bit--) {
            xD = inj_smul(xD, xD);
            if ((E >> bit) & 1) xD = inj_smul(xD, x3);
        }

        // H = sum_j P^(j) * x^(jD), Horner in x^D
        uint64_t H = P[L - 1];
        for (int j = L - 2; j >= 0; j--) {
            H = inj_smul(H, xD) ^ P[j];
        }
        return H;
    }

    // Two-key version: lanes use y, combined with y.
    uint64_t operator()(uint64_t x, uint64_t y) {
        uint64_t x2 = inj_smul(x, x);

        // Same L interleaved chains, with y in place of x^3.
        uint64_t P[L];
        for (int j = 0; j < L; j++) P[j] = x;
        for (int r = 0; r < FULL; r++) {
            for (int j = 0; j < L; j++) {
                const int i = r * L + j;
                P[j] = m_a[i] ^ inj_smul(m_b[i] ^ y, P[j] ^ x2);
            }
        }
        for (int j = 0; j < N - FULL * L; j++) {
            const int i = FULL * L + j;
            P[j] = m_a[i] ^ inj_smul(m_b[i] ^ y, P[j] ^ x2);
        }

        // H = sum_j P^(j) * y^j, Horner in y
        uint64_t H = P[L - 1];
        for (int j = L - 2; j >= 0; j--) {
            H = inj_smul(H, y) ^ P[j];
        }
        return H;
    }

    // Independent keys xs[0..L): lane j runs the single-key recurrence with
    // its own key x_j (P_0 = x_j, constants x_j^2, x_j^3), and the lanes are
    // combined as H = XOR_j x_j * P^(j)(x_j).  A differing lane contributes a
    // non-constant polynomial in its own independent variable, so conditioning
    // on the other keys gives Pr[collision] <= (3*ceil(N/L) + 3)/2^64, the
    // per-lane degree.  (Plain XOR without the multiply is NOT safe: the last
    // a-word enters every lane with coefficient 1, so equal changes to the
    // last a-words of two lanes cancel for every key.)  Resident key: 3L words.
    uint64_t operator()(const uint64_t* xs) {
        uint64_t P[L], X2[L], X3[L];
        for (int j = 0; j < L; j++) {
            P[j] = xs[j];
            X2[j] = inj_smul(xs[j], xs[j]);
            X3[j] = inj_smul(X2[j], xs[j]);
        }
        for (int r = 0; r < FULL; r++) {
            for (int j = 0; j < L; j++) {
                const int i = r * L + j;
                P[j] = m_a[i] ^ inj_smul(m_b[i] ^ X3[j], P[j] ^ X2[j]);
            }
        }
        for (int j = 0; j < N - FULL * L; j++) {
            const int i = FULL * L + j;
            P[j] = m_a[i] ^ inj_smul(m_b[i] ^ X3[j], P[j] ^ X2[j]);
        }
        uint64_t H = 0;
        for (int j = 0; j < L; j++) H ^= inj_smul(P[j], xs[j]);
        return H;
    }
};

/* ***************************************************
 * Horner Baseline for Universal Hashing - GF(2^64)
 *
 * Standard Horner evaluation: h = m[0]; h = h*x + m[i]
 *
 * Message: m[0..2N-1] - 2N values to hash
 * Key: x - single random field element
 *
 * Uses 2N-1 multiplications to hash 2N message values.
 * For fair comparison with univ_injective_64 which uses N.
 * ***************************************************/

template <std::size_t N>
class univ_horner_64 {
    uint64_t m[2*N];  // 2N message values

public:
    void init() {
        for (size_t i = 0; i < 2*N; i++) {
            m[i] = getRandomUInt64();
        }
    }

    // Hash 2N message values using key x
    uint64_t operator()(uint64_t x) {
        uint64_t h = m[0];
        for (size_t i = 1; i < 2*N; i++) {
            h = inj_smul(h, x) ^ m[i];
        }
        return h;
    }
};

/* ***************************************************
 * Parallel Injective Hashing with Prefix Scan - GF(2^64)
 *
 * Same recurrence as univ_injective_64, but parallelized
 * using transfer function composition.
 *
 * Transfer function: (c_i, d_i) where c_i = b_i + y, d_i = a_i + c_i × x²
 * Composition: (c_a,d_a) ∘ (c_b,d_b) = (c_b×c_a, d_b + c_b×d_a)
 *
 * Uses O(N) multiplications but O(log N) critical path depth.
 * Trade-off: More total multiplications (3N vs N), but much better ILP.
 * ***************************************************/

template <std::size_t N>
class univ_injective_parallel_64 {
    uint64_t m_a[N];  // First half of message data
    uint64_t m_b[N];  // Second half of message data

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            m_a[i] = getRandomUInt64();
            m_b[i] = getRandomUInt64();
        }
    }

    // Hash 2N message values using keys (x, y) with parallel prefix scan
    uint64_t operator()(uint64_t x, uint64_t y) {
        uint64_t x2 = inj_smul(x, x);

        // Phase 1: Compute all transfer functions in parallel
        uint64_t c[N], d[N];
        for (size_t i = 0; i < N; i++) {
            c[i] = m_b[i] ^ y;
            d[i] = m_a[i] ^ inj_smul(c[i], x2);
        }

        // Phase 2: Parallel prefix scan
        for (size_t stride = 1; stride < N; stride *= 2) {
            for (size_t i = 0; i + stride < N; i += 2 * stride) {
                size_t j = i + stride;
                uint64_t new_c = inj_smul(c[j], c[i]);
                uint64_t new_d = d[j] ^ inj_smul(c[j], d[i]);
                c[i] = new_c;
                d[i] = new_d;
            }
        }

        return d[0] ^ inj_smul(c[0], x);
    }

    // Single-key version
    uint64_t operator()(uint64_t x) {
        uint64_t x2 = inj_smul(x, x);
        uint64_t x3 = inj_smul(x2, x);

        uint64_t c[N], d[N];
        for (size_t i = 0; i < N; i++) {
            c[i] = m_b[i] ^ x3;
            d[i] = m_a[i] ^ inj_smul(c[i], x2);
        }

        for (size_t stride = 1; stride < N; stride *= 2) {
            for (size_t i = 0; i + stride < N; i += 2 * stride) {
                size_t j = i + stride;
                uint64_t new_c = inj_smul(c[j], c[i]);
                uint64_t new_d = d[j] ^ inj_smul(c[j], d[i]);
                c[i] = new_c;
                d[i] = new_d;
            }
        }

        return d[0] ^ inj_smul(c[0], x);
    }
};

/* ***************************************************
 * BRW (Bernstein-Rabin-Winograd) Universal Hashing - GF(2^64)
 *
 * Recursive divide-and-conquer polynomial structure:
 *   BRW(x; m₁) = m₁
 *   BRW(x; m₁,m₂) = m₁ × x + m₂
 *   BRW(x; m₁,m₂,m₃) = (x + m₁)(x² + m₂) + m₃
 *   BRW(x; m₁,...,m_{2^k-1}) = BRW(left) × (x^{2^{k-1}} + m_{2^{k-1}}) + BRW(right)
 *
 * Message: m[0..N-1] - N values to hash
 * Key: x - single random field element
 *
 * Uses ~N/2 multiplications + O(log N) squarings.
 * Designed for universal hashing (MAC), NOT k-wise independence.
 * ***************************************************/

template <std::size_t N>
class univ_brw_64 {
    uint64_t m[N];  // Message blocks

public:
    void init() {
        for (size_t i = 0; i < N; i++)
            m[i] = getRandomUInt64();
    }

    uint64_t operator()(uint64_t x) {
        // Precompute powers: x, x², x⁴, x⁸, ...
        constexpr size_t MAX_POWERS = 16;
        uint64_t xpow[MAX_POWERS];
        xpow[0] = x;
        size_t num_powers = 1;
        while ((1ULL << num_powers) <= N) {
            xpow[num_powers] = inj_smul(xpow[num_powers-1], xpow[num_powers-1]);
            num_powers++;
        }

        return brw_recursive(0, N, xpow);
    }

private:
    uint64_t brw_recursive(size_t start, size_t len, const uint64_t* xpow) {
        if (len == 0) return 0;
        if (len == 1) return m[start];
        if (len == 2) return inj_smul(m[start], xpow[0]) ^ m[start+1];
        if (len == 3) {
            return inj_smul(xpow[0] ^ m[start], xpow[1] ^ m[start+1]) ^ m[start+2];
        }

        size_t r = 0;
        while ((1ULL << (r+1)) <= len) r++;
        size_t pow2r = 1ULL << r;

        uint64_t left = brw_recursive(start, pow2r - 1, xpow);
        uint64_t right = brw_recursive(start + pow2r, len - pow2r, xpow);

        return inj_smul(left, xpow[r] ^ m[start + pow2r - 1]) ^ right;
    }
};

/* ***************************************************
 * c-decimated BRW Universal Hashing - GF(2^64)
 *
 * Splits message into c interleaved streams, applies BRW
 * to each stream, and combines with Horner.
 *
 * Message: m[0..N-1] - N values to hash
 * Key: x - single random field element
 *
 * Better parallelism than plain BRW for certain message sizes.
 * ***************************************************/

template <std::size_t c, std::size_t N>
class univ_c_decbrw_64 {
    uint64_t m[N];  // Message blocks

public:
    void init() {
        for (size_t i = 0; i < N; i++)
            m[i] = getRandomUInt64();
    }

    uint64_t operator()(uint64_t x) {
        constexpr size_t stream_len = (N + c - 1) / c;
        constexpr size_t r = []() {
            size_t r = 0;
            while ((1ULL << r) < stream_len) r++;
            return r;
        }();
        constexpr size_t d_exp = r + 1;

        constexpr size_t MAX_POWERS = 16;
        uint64_t xpow[MAX_POWERS];
        xpow[0] = x;
        for (size_t i = 1; i <= d_exp && i < MAX_POWERS; i++) {
            xpow[i] = inj_smul(xpow[i-1], xpow[i-1]);
        }
        uint64_t xd = xpow[d_exp];

        uint64_t results[c];
        for (size_t i = 0; i < c; i++) {
            results[i] = brw_stream(i, xpow);
        }

        // Combine with Horner
        uint64_t h = results[c-1];
        for (int i = c - 2; i >= 0; i--) {
            h = inj_smul(h, xd) ^ results[i];
        }
        return h;
    }

private:
    uint64_t brw_stream(size_t stream_idx, const uint64_t* xpow) {
        // Collect elements for this stream
        constexpr size_t stream_len = (N + c - 1) / c;
        uint64_t stream[stream_len];
        size_t actual_len = 0;

        for (size_t i = stream_idx; i < N; i += c) {
            stream[actual_len++] = m[i];
        }

        return brw_recursive(stream, actual_len, xpow);
    }

    uint64_t brw_recursive(const uint64_t* arr, size_t len, const uint64_t* xpow) {
        if (len == 0) return 0;
        if (len == 1) return arr[0];
        if (len == 2) return inj_smul(arr[0], xpow[0]) ^ arr[1];
        if (len == 3) {
            return inj_smul(xpow[0] ^ arr[0], xpow[1] ^ arr[1]) ^ arr[2];
        }

        size_t r = 0;
        while ((1ULL << (r+1)) <= len) r++;
        size_t pow2r = 1ULL << r;

        uint64_t left = brw_recursive(arr, pow2r - 1, xpow);
        uint64_t right = brw_recursive(arr + pow2r, len - pow2r, xpow);

        return inj_smul(left, xpow[r] ^ arr[pow2r - 1]) ^ right;
    }
};

// Convenience typedefs for c=2 and c=4
template <std::size_t N>
using univ_c2_decbrw_64 = univ_c_decbrw_64<2, N>;

template <std::size_t N>
using univ_c4_decbrw_64 = univ_c_decbrw_64<4, N>;

/* ***************************************************
 * Parallel Horner - GF(2^64) with parallel prefix scan
 *
 * Horner's rule h_{i+1} = h_i × x + k_{i+1} is a linear recurrence
 * with constant coefficient x. We can parallelize using:
 *
 * 1. Precompute powers: x, x², x⁴, x⁸, ...
 * 2. Combine pairs: d[i] = k[2i+1] + x×k[2i] with coeff x²
 * 3. Tree reduction on the (coeff, const) pairs
 *
 * Trade-off: O(N) more multiplications but O(log N) critical path.
 * ***************************************************/

template <std::size_t N>
class horner_parallel_64 {
    uint64_t k[N];  // Coefficients

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            k[i] = getRandomUInt64();
        }
    }

    uint64_t operator()(uint64_t x) {
        // Precompute powers of x: x¹, x², x⁴, x⁸, ...
        constexpr size_t MAX_POWERS = 16;
        uint64_t xpow[MAX_POWERS];
        xpow[0] = x;
        for (size_t i = 1; i < MAX_POWERS && (1ULL << i) <= N; i++) {
            xpow[i] = inj_smul(xpow[i-1], xpow[i-1]);
        }

        // Each coefficient k[i] contributes transfer function (x, k[i])
        // Meaning: h → h×x + k[i]
        //
        // Composition: (c_a, d_a) ∘ (c_b, d_b) = (c_b×c_a, d_b + c_b×d_a)
        //
        // For pairs with same c=x:
        // (x, k[i]) ∘ (x, k[i+1]) = (x², k[i+1] + x×k[i])
        //
        // We build a tree where:
        // - Level 0: N individual (x, k[i]) pairs
        // - Level 1: N/2 combined (x², d) pairs
        // - Level 2: N/4 combined (x⁴, d) pairs
        // - etc.

        // Work array for d values (c values are just xpow[level])
        uint64_t d[N];
        for (size_t i = 0; i < N; i++) {
            d[i] = k[i];
        }

        // Tree reduction
        size_t len = N;
        size_t level = 0;
        while (len > 1) {
            size_t half = len / 2;
            // Combine pairs: d[i] = d[2i+1] + x^{2^level} × d[2i]
            for (size_t i = 0; i < half; i++) {
                d[i] = d[2*i + 1] ^ inj_smul(xpow[level], d[2*i]);
            }
            // Handle odd element if present
            if (len & 1) {
                d[half] = d[len - 1];
                half++;
            }
            len = half;
            level++;
        }

        // Final result: d[0] contains the polynomial value
        // (Starting with h_0 = 0, which is implicit in Horner)
        return d[0];
    }
};

/* ***************************************************
 * CLNH - Carry-Less NH hash (from Lemire-Kaser CLHASH)
 *
 * Multilinear hash: h = (a₁⊕x₁)(a₂⊕x₂) ⊕ (a₃⊕x₃)(a₄⊕x₄) ⊕ ...
 *
 * Key insight: ALL multiplications are independent!
 * For 2N keys, uses N multiplications with O(1) critical path.
 * This is Δ-universal by Lemma 5 of Lemire-Kaser 2015.
 * ***************************************************/

template <std::size_t N>
class clnh_64 {
    uint64_t k[2*N];  // 2N keys for N multiplications

public:
    void init() {
        for (size_t i = 0; i < 2*N; i++) {
            k[i] = getRandomUInt64();
        }
    }

    uint64_t operator()(uint64_t x) {
        // All N multiplications are independent!
        // h = (k[0]⊕x)(k[1]⊕x) ⊕ (k[2]⊕x)(k[3]⊕x) ⊕ ...
        uint64_t h = 0;
        for (size_t i = 0; i < N; i++) {
            h ^= inj_smul(k[2*i] ^ x, k[2*i+1] ^ x);
        }
        return h;
    }
};

/* ***************************************************
 * Unrolled Horner - GF(2^64) with manual unrolling
 *
 * Process multiple coefficients per iteration to expose ILP.
 * Each iteration computes 4 steps in parallel where possible.
 * ***************************************************/

template <std::size_t N>
class horner_unrolled_64 {
    uint64_t k[N];

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            k[i] = getRandomUInt64();
        }
    }

    uint64_t operator()(uint64_t x) {
        // Precompute x², x⁴ for unrolled steps
        uint64_t x2 = inj_smul(x, x);
        uint64_t x4 = inj_smul(x2, x2);

        uint64_t h = k[0];
        size_t i = 1;

        // Process 4 coefficients at a time using Estrin-like grouping
        // h = ((h×x + k[i])×x + k[i+1])×x + k[i+2])×x + k[i+3]
        //   = h×x⁴ + k[i]×x³ + k[i+1]×x² + k[i+2]×x + k[i+3]
        //   = h×x⁴ + (k[i]×x + k[i+1])×x² + (k[i+2]×x + k[i+3])
        while (i + 3 < N) {
            uint64_t lo = inj_smul(k[i+2], x) ^ k[i+3];      // k[i+2]×x + k[i+3]
            uint64_t hi = inj_smul(k[i], x) ^ k[i+1];        // k[i]×x + k[i+1]
            uint64_t mid = inj_smul(hi, x2) ^ lo;             // hi×x² + lo
            h = inj_smul(h, x4) ^ mid;                        // h×x⁴ + mid
            i += 4;
        }

        // Handle remaining coefficients with standard Horner
        while (i < N) {
            h = inj_smul(h, x) ^ k[i];
            i++;
        }

        return h;
    }
};

/* ***************************************************
 * 128-BIT OUTPUT HASH FUNCTIONS
 *
 * Three approaches compared:
 * 1. CLNH-128: Keep full 128-bit products (no reduction!)
 * 2. Two independent 64-bit hashes
 * 3. GF(2^128) polynomial hash
 * ***************************************************/

// Return type for 128-bit hashes
struct hash128_t {
    uint64_t lo, hi;
    hash128_t() : lo(0), hi(0) {}
    hash128_t(uint64_t l, uint64_t h) : lo(l), hi(h) {}
    hash128_t operator^(const hash128_t& other) const {
        return hash128_t(lo ^ other.lo, hi ^ other.hi);
    }
};

/* ***************************************************
 * CLNH-128: Multilinear hash with 128-bit output
 *
 * Key insight: 64×64 multiply gives 128-bit product.
 * Instead of reducing to 64 bits, keep the full product!
 * XOR the 128-bit products together.
 *
 * Same number of multiplies as 64-bit CLNH, but 128-bit output.
 * This is the approach from Lemire-Kaser's CLHASH paper.
 * ***************************************************/

template <std::size_t N>
class clnh_128 {
    uint64_t k[2*N];

public:
    void init() {
        for (size_t i = 0; i < 2*N; i++) {
            k[i] = getRandomUInt64();
        }
    }

    hash128_t operator()(uint64_t x) {
        // All N multiplications are independent!
        // Keep full 128-bit products, XOR together
        uint64_t lo = 0, hi = 0;
        for (size_t i = 0; i < N; i++) {
            // 64×64 → 128 bit product (no reduction!)
            __m128i prod = poly_to_u8(clmul_lo_lo(
                from64(k[2*i] ^ x), from64(k[2*i+1] ^ x)));
            lo ^= lower64(prod);
            hi ^= upper64(prod);
        }
        return hash128_t(lo, hi);
    }
};

/* ***************************************************
 * Two independent 64-bit CLNH hashes (baseline)
 * ***************************************************/

template <std::size_t N>
class clnh_2x64 {
    uint64_t k1[2*N];
    uint64_t k2[2*N];

public:
    void init() {
        for (size_t i = 0; i < 2*N; i++) {
            k1[i] = getRandomUInt64();
            k2[i] = getRandomUInt64();
        }
    }

    hash128_t operator()(uint64_t x) {
        uint64_t h1 = 0, h2 = 0;
        for (size_t i = 0; i < N; i++) {
            h1 ^= inj_smul(k1[2*i] ^ x, k1[2*i+1] ^ x);
            h2 ^= inj_smul(k2[2*i] ^ x, k2[2*i+1] ^ x);
        }
        return hash128_t(h1, h2);
    }
};

/* ***************************************************
 * GF(2^128) multiply using Karatsuba
 *
 * For (a1·2^64 + a0) × (b1·2^64 + b0):
 * - z0 = a0 × b0
 * - z2 = a1 × b1
 * - z1 = (a0+a1) × (b0+b1) - z0 - z2
 * - Result = z2·2^128 + z1·2^64 + z0
 *
 * Then reduce mod x^128 + x^7 + x^2 + x + 1
 * ***************************************************/

// 128×128 carryless multiply → 256 bits (stored as 4 uint64_t)
static inline void clmul_128x128(uint64_t a_lo, uint64_t a_hi,
                                  uint64_t b_lo, uint64_t b_hi,
                                  uint64_t& r0, uint64_t& r1,
                                  uint64_t& r2, uint64_t& r3) {
    // Karatsuba: 3 multiplies instead of 4
    __m128i z0 = poly_to_u8(clmul_lo_lo(from64(a_lo), from64(b_lo)));
    __m128i z2 = poly_to_u8(clmul_lo_lo(from64(a_hi), from64(b_hi)));
    __m128i z1 = poly_to_u8(clmul_lo_lo(from64(a_lo ^ a_hi), from64(b_lo ^ b_hi)));

    // z1 = z1 - z0 - z2 (XOR in GF(2))
    z1 = xor128(xor128(z1, z0), z2);

    // Combine: result = z2·2^128 + z1·2^64 + z0
    r0 = lower64(z0);
    r1 = upper64(z0) ^ lower64(z1);
    r2 = lower64(z2) ^ upper64(z1);
    r3 = upper64(z2);
}

// Reduce 256-bit value mod x^128 + x^7 + x^2 + x + 1
static inline void reduce_gf128(uint64_t r0, uint64_t r1, uint64_t r2, uint64_t r3,
                                 uint64_t& out_lo, uint64_t& out_hi) {
    // The irreducible polynomial is x^128 + x^7 + x^2 + x + 1
    // So x^128 = x^7 + x^2 + x + 1 (mod P)
    // Reduction constant: 0x87 in the low byte position

    // Reduce r3 (bits 192-255): multiply by x^64 reduction
    __m128i r3_red = poly_to_u8(clmul_lo_lo(from64(r3), from64(0x87)));
    r1 ^= lower64(r3_red);
    r2 ^= upper64(r3_red);

    // Reduce r2 (bits 128-191): multiply by reduction polynomial
    __m128i r2_red = poly_to_u8(clmul_lo_lo(from64(r2), from64(0x87)));
    r0 ^= lower64(r2_red);
    r1 ^= upper64(r2_red);

    out_lo = r0;
    out_hi = r1;
}

// Full GF(2^128) multiply with reduction
static inline hash128_t gf128_mul(hash128_t a, hash128_t b) {
    uint64_t r0, r1, r2, r3;
    clmul_128x128(a.lo, a.hi, b.lo, b.hi, r0, r1, r2, r3);

    uint64_t out_lo, out_hi;
    reduce_gf128(r0, r1, r2, r3, out_lo, out_hi);

    return hash128_t(out_lo, out_hi);
}

/* ***************************************************
 * Polynomial hash in GF(2^128) using Horner
 * (Similar to GHASH structure)
 * ***************************************************/

template <std::size_t N>
class poly_gf128 {
    hash128_t k[N];

public:
    void init() {
        for (size_t i = 0; i < N; i++) {
            k[i] = hash128_t(getRandomUInt64(), getRandomUInt64());
        }
    }

    hash128_t operator()(uint64_t x_lo, uint64_t x_hi) {
        hash128_t x(x_lo, x_hi);
        hash128_t h = k[0];
        for (size_t i = 1; i < N; i++) {
            h = gf128_mul(h, x) ^ k[i];
        }
        return h;
    }

    hash128_t operator()(uint64_t x) {
        return (*this)(x, x);
    }
};

#endif  // _INJECTIVE_HASHING_H_
