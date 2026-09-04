/* ***********************************************************************
 * Reference implementations used by the adversarial-collision experiments
 * (tools/bench/adversarial/).  Everything is self-contained: no external code.
 *
 * Message model: a message is a byte string; all experiments use lengths
 * that are multiples of 16 bytes (an even number L of 64-bit little-endian
 * words w[0..L-1]).  The paper's hashes read the words as the stream
 * (a_1,b_1,a_2,b_2,...) = (w[0],w[1],w[2],w[3],...).
 *
 * Hashes:
 *   PROVEN (Schwartz-Zippel / strong universality):
 *     PaperGF64      - Section 3 recurrence P_i = a_i + (b_i + x^3)(P_{i-1} + x^2)
 *                      over GF(2^64) (x^64+x^4+x^3+x+1), one random key x.
 *                      Collision probability <= (3N+2)/2^64, N = L/2.
 *     PaperMersenne  - same recurrence over GF(p), p = 2^61-1, each 64-bit word
 *                      split into two 32-bit field elements (injective), so
 *                      N = L pairs, bound (3L+2)/p.
 *     VectorMultShift- Dietzfelbinger's vector multiply-add-shift
 *                      h(w) = ((a_0 + sum_i a_i w_i) mod 2^128) >> 64, a_i uniform
 *                      128-bit: strongly universal, collision prob <= 2^-64.
 *   HEURISTIC (no proof):
 *     PaperMumXor    - the paper's recurrence with the field product replaced
 *                      by the MUM fold lo64(ab) ^ hi64(ab), '+' = XOR.
 *     PaperMumAdd    - same, '+' = integer addition mod 2^64, fold lo ^ hi.
 *     Wyhash         - wyhash final version 4.3 (Wang Yi), verbatim structure.
 *     Rapidhash      - rapidhash v1.0 (Nicolas De Carli, 2024), verbatim structure.
 *     Mum            - MUM v3 (Vladimir Makarov, mum.h, default macros:
 *                      neither MUM_V1/V2/V3 defined), fold = hi + lo.
 *     Xxh3           - XXH3_64bits_withSeed (Yann Collet), 9..128-byte paths.
 * ***********************************************************************/
#ifndef ADVERSARIAL_HASHES_H
#define ADVERSARIAL_HASHES_H

#include <cstdint>
#include <cstring>
#include <cstddef>

typedef unsigned __int128 u128;

/* ------------------------------------------------------------------ */
/* Small deterministic PRNG (splitmix64 + xoshiro256**), per thread.  */
/* ------------------------------------------------------------------ */
struct Rng {
    uint64_t s[4];
    static uint64_t splitmix(uint64_t& x) {
        uint64_t z = (x += 0x9e3779b97f4a7c15ull);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
        return z ^ (z >> 31);
    }
    explicit Rng(uint64_t seed = 1) { for (int i = 0; i < 4; i++) s[i] = splitmix(seed); }
    static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
    uint64_t next() {
        uint64_t r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
        s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
        return r;
    }
    u128 next128() { return ((u128)next() << 64) | next(); }
};

/* ------------------------------------------------------------------ */
/* Helpers                                                              */
/* ------------------------------------------------------------------ */
static inline uint64_t rd64(const uint8_t* p) { uint64_t v; memcpy(&v, p, 8); return v; }
static inline uint64_t rd32(const uint8_t* p) { uint32_t v; memcpy(&v, p, 4); return v; }
static inline void wr64(uint8_t* p, uint64_t v) { memcpy(p, &v, 8); }

// The MUM fold with XOR (wyhash _wymix / xxh3 mul128_fold64 / paper's "MUM").
static inline uint64_t mum_xor(uint64_t a, uint64_t b) {
    u128 r = (u128)a * b; return (uint64_t)r ^ (uint64_t)(r >> 64);
}
// The MUM fold with addition (Makarov's _mum).
static inline uint64_t mum_add(uint64_t a, uint64_t b) {
    u128 r = (u128)a * b; return (uint64_t)r + (uint64_t)(r >> 64);
}

/* ------------------------------------------------------------------ */
/* GF(2^64) multiplication, x^64 + x^4 + x^3 + x + 1 (same as the      */
/* benchmark framework).  Carry-less multiply via PMULL / PCLMULQDQ    */
/* with function-level target attributes so that -march=native works  */
/* on Apple clang (which does not enable +aes by default).             */
/* ------------------------------------------------------------------ */
#if defined(__aarch64__)
#include <arm_neon.h>
__attribute__((target("aes")))
static inline void clmul64(uint64_t a, uint64_t b, uint64_t& lo, uint64_t& hi) {
    poly128_t r = vmull_p64((poly64_t)a, (poly64_t)b);
    u128 v; memcpy(&v, &r, 16);
    lo = (uint64_t)v; hi = (uint64_t)(v >> 64);
}
#define GF64_TARGET __attribute__((target("aes")))
#elif defined(__x86_64__)
#include <immintrin.h>
__attribute__((target("pclmul,sse2")))
static inline void clmul64(uint64_t a, uint64_t b, uint64_t& lo, uint64_t& hi) {
    __m128i r = _mm_clmulepi64_si128(_mm_set_epi64x(0, (long long)a), _mm_set_epi64x(0, (long long)b), 0);
    lo = (uint64_t)_mm_cvtsi128_si64(r);
    hi = (uint64_t)_mm_cvtsi128_si64(_mm_srli_si128(r, 8));
}
#define GF64_TARGET __attribute__((target("pclmul,sse2")))
#else
static inline void clmul64(uint64_t a, uint64_t b, uint64_t& lo, uint64_t& hi) {
    lo = hi = 0;
    for (int i = 0; i < 64; i++) if ((b >> i) & 1) { lo ^= a << i; if (i) hi ^= a >> (64 - i); }
}
#define GF64_TARGET
#endif

GF64_TARGET
static inline uint64_t gf64_mul(uint64_t a, uint64_t b) {
    uint64_t lo, hi, lo2, hi2, lo3, hi3;
    clmul64(a, b, lo, hi);          // a*b = hi*x^64 + lo
    clmul64(hi, 27, lo2, hi2);      // x^64 = x^4+x^3+x+1 = 27; hi2 < 2^4
    clmul64(hi2, 27, lo3, hi3);     // hi3 = 0
    return lo ^ lo2 ^ lo3;
}

/* ------------------------------------------------------------------ */
/* Mersenne field p = 2^61 - 1                                          */
/* ------------------------------------------------------------------ */
static const uint64_t MERS_P = (1ull << 61) - 1;
static inline uint64_t mers_mul(uint64_t a, uint64_t b) {
    u128 r = (u128)a * b;                     // < 2^122
    uint64_t s = (uint64_t)r & MERS_P, q = (uint64_t)(r >> 61);
    uint64_t t = s + q; if (t >= MERS_P) t -= MERS_P; return t;
}
static inline uint64_t mers_add(uint64_t a, uint64_t b) { uint64_t t = a + b; if (t >= MERS_P) t -= MERS_P; return t; }

/* ================================================================== */
/*  The paper's Section-3 hash (single key x): P_0 = x,                 */
/*  P_i = a_i + (b_i + x^3)(P_{i-1} + x^2)                              */
/* ================================================================== */
struct PaperGF64 {
    static constexpr const char* name = "Paper GF(2^64) [proven]";
    uint64_t x, x2, x3;
    void seed(Rng& r) { x = r.next(); x2 = gf64_mul(x, x); x3 = gf64_mul(x2, x); }
    GF64_TARGET uint64_t operator()(const uint8_t* p, size_t len) const {
        uint64_t P = x;
        for (size_t i = 0; i + 16 <= len; i += 16)
            P = rd64(p + i) ^ gf64_mul(rd64(p + i + 8) ^ x3, P ^ x2);
        return P;
    }
};

struct PaperMersenne {
    static constexpr const char* name = "Paper Mersenne 2^61-1 [proven]";
    uint64_t x, x2, x3;
    void seed(Rng& r) { do { x = r.next() >> 3; } while (x >= MERS_P); x2 = mers_mul(x, x); x3 = mers_mul(x2, x); }
    // each 64-bit word -> two 32-bit field elements (injective); pairs (a,b) = consecutive elements
    uint64_t operator()(const uint8_t* p, size_t len) const {
        uint64_t P = x;
        for (size_t i = 0; i + 8 <= len; i += 8) {
            uint64_t w = rd64(p + i);
            uint64_t a = (uint32_t)w, b = w >> 32;
            P = mers_add(a, mers_mul(mers_add(b, x3), mers_add(P, x2)));
        }
        return P;
    }
};

/* Vector multiply-add-shift (Dietzfelbinger 1996), strongly universal. */
struct VectorMultShift {
    static constexpr const char* name = "Vector multiply-shift [proven]";
    static const int MAXW = 64;
    u128 a[MAXW + 1];
    void seed(Rng& r) { for (int i = 0; i <= MAXW; i++) a[i] = r.next128(); }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        u128 acc = a[0]; int k = 1;
        for (size_t i = 0; i + 8 <= len; i += 8) acc += a[k++] * (u128)rd64(p + i);
        return (uint64_t)(acc >> 64);
    }
};

/* ================================================================== */
/*  The paper's recurrence with the MUM fold instead of the field mult. */
/* ================================================================== */
struct PaperMumXor {
    static constexpr const char* name = "Paper recurrence + MUM fold (xor)";
    uint64_t x, x2, x3;
    void seed(Rng& r) { x = r.next(); x2 = mum_xor(x, x); x3 = mum_xor(x2, x); }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        uint64_t P = x;
        for (size_t i = 0; i + 16 <= len; i += 16)
            P = rd64(p + i) ^ mum_xor(rd64(p + i + 8) ^ x3, P ^ x2);
        return P;
    }
};
struct PaperMumAdd {
    static constexpr const char* name = "Paper recurrence + MUM fold (add)";
    uint64_t x, x2, x3;
    void seed(Rng& r) { x = r.next(); x2 = mum_xor(x, x); x3 = mum_xor(x2, x); }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        uint64_t P = x;
        for (size_t i = 0; i + 16 <= len; i += 16)
            P = rd64(p + i) + mum_xor(rd64(p + i + 8) + x3, P + x2);
        return P;
    }
};

/* ================================================================== */
/*  wyhash final version 4.3 (WYHASH_CONDOM=1, 64-bit mum)              */
/*  https://github.com/wangyi-fudan/wyhash  (structure copied verbatim) */
/* ================================================================== */
static const uint64_t WYHASH_SECRET_DEFAULT[4] = {0x2d358dccaa6c78a5ull, 0x8bb84b93962eacc9ull, 0x4b33a62ed433d4a3ull, 0x4d5a2da51de1aa47ull};

static inline void _wymum(uint64_t* A, uint64_t* B) { u128 r = *A; r *= *B; *A = (uint64_t)r; *B = (uint64_t)(r >> 64); }
static inline uint64_t _wymix(uint64_t A, uint64_t B) { _wymum(&A, &B); return A ^ B; }
static inline uint64_t _wyr3(const uint8_t* p, size_t k) { return (((uint64_t)p[0]) << 16) | (((uint64_t)p[k >> 1]) << 8) | p[k - 1]; }

static inline uint64_t wyhash_ref(const void* key, size_t len, uint64_t seed, const uint64_t* secret) {
    const uint8_t* p = (const uint8_t*)key; seed ^= _wymix(seed ^ secret[0], secret[1]); uint64_t a, b;
    if (len <= 16) {
        if (len >= 4) { a = (rd32(p) << 32) | rd32(p + ((len >> 3) << 2)); b = (rd32(p + len - 4) << 32) | rd32(p + len - 4 - ((len >> 3) << 2)); }
        else if (len > 0) { a = _wyr3(p, len); b = 0; }
        else a = b = 0;
    } else {
        size_t i = len;
        if (i >= 48) {
            uint64_t see1 = seed, see2 = seed;
            do {
                seed = _wymix(rd64(p) ^ secret[1], rd64(p + 8) ^ seed);
                see1 = _wymix(rd64(p + 16) ^ secret[2], rd64(p + 24) ^ see1);
                see2 = _wymix(rd64(p + 32) ^ secret[3], rd64(p + 40) ^ see2);
                p += 48; i -= 48;
            } while (i >= 48);
            seed ^= see1 ^ see2;
        }
        while (i > 16) { seed = _wymix(rd64(p) ^ secret[1], rd64(p + 8) ^ seed); i -= 16; p += 16; }
        a = rd64(p + i - 16); b = rd64(p + i - 8);
    }
    a ^= secret[1]; b ^= seed; _wymum(&a, &b);
    return _wymix(a ^ secret[0] ^ len, b ^ secret[1]);
}

template <bool RANDOM_SECRET>
struct Wyhash {
    static constexpr const char* name = RANDOM_SECRET ? "wyhash 4.3 (random secret)" : "wyhash 4.3 (default secret)";
    uint64_t sd; uint64_t secret[4];
    void seed(Rng& r) {
        sd = r.next();
        if (RANDOM_SECRET) for (int i = 0; i < 4; i++) secret[i] = r.next() | 1;   // make_secret produces odd words
        else memcpy(secret, WYHASH_SECRET_DEFAULT, sizeof secret);
    }
    uint64_t operator()(const uint8_t* p, size_t len) const { return wyhash_ref(p, len, sd, secret); }
};

/* ================================================================== */
/*  rapidhash v1.0 (Nicolas De Carli, 2024, RAPIDHASH_FAST, unrolled)   */
/*  https://github.com/Nicoshev/rapidhash tag rapidhash_v1.0            */
/* ================================================================== */
static const uint64_t RAPID_SECRET_DEFAULT[3] = {0x2d358dccaa6c78a5ull, 0x8bb84b93962eacc9ull, 0x4b33a62ed433d4a3ull};
static inline void rapid_mum(uint64_t* A, uint64_t* B) { u128 r = (u128)*A * *B; *A = (uint64_t)r; *B = (uint64_t)(r >> 64); }
static inline uint64_t rapid_mix(uint64_t A, uint64_t B) { rapid_mum(&A, &B); return A ^ B; }
static inline uint64_t rapid_readSmall(const uint8_t* p, size_t k) { return (((uint64_t)p[0]) << 56) | (((uint64_t)p[k >> 1]) << 32) | p[k - 1]; }

static inline uint64_t rapidhash_ref(const void* key, size_t len, uint64_t seed, const uint64_t* secret) {
    const uint8_t* p = (const uint8_t*)key;
    seed ^= rapid_mix(seed ^ secret[0], secret[1]) ^ len;
    uint64_t a, b;
    if (len <= 16) {
        if (len >= 4) {
            const uint8_t* plast = p + len - 4;
            a = (rd32(p) << 32) | rd32(plast);
            const uint64_t delta = ((len & 24) >> (len >> 3));
            b = ((rd32(p + delta) << 32) | rd32(plast - delta));
        } else if (len > 0) { a = rapid_readSmall(p, len); b = 0; }
        else a = b = 0;
    } else {
        size_t i = len;
        if (i > 48) {
            uint64_t see1 = seed, see2 = seed;
            while (i >= 96) {
                seed = rapid_mix(rd64(p) ^ secret[0], rd64(p + 8) ^ seed);
                see1 = rapid_mix(rd64(p + 16) ^ secret[1], rd64(p + 24) ^ see1);
                see2 = rapid_mix(rd64(p + 32) ^ secret[2], rd64(p + 40) ^ see2);
                seed = rapid_mix(rd64(p + 48) ^ secret[0], rd64(p + 56) ^ seed);
                see1 = rapid_mix(rd64(p + 64) ^ secret[1], rd64(p + 72) ^ see1);
                see2 = rapid_mix(rd64(p + 80) ^ secret[2], rd64(p + 88) ^ see2);
                p += 96; i -= 96;
            }
            if (i >= 48) {
                seed = rapid_mix(rd64(p) ^ secret[0], rd64(p + 8) ^ seed);
                see1 = rapid_mix(rd64(p + 16) ^ secret[1], rd64(p + 24) ^ see1);
                see2 = rapid_mix(rd64(p + 32) ^ secret[2], rd64(p + 40) ^ see2);
                p += 48; i -= 48;
            }
            seed ^= see1 ^ see2;
        }
        if (i > 16) {
            seed = rapid_mix(rd64(p) ^ secret[2], rd64(p + 8) ^ seed ^ secret[1]);
            if (i > 32) seed = rapid_mix(rd64(p + 16) ^ secret[2], rd64(p + 24) ^ seed);
        }
        a = rd64(p + i - 16); b = rd64(p + i - 8);
    }
    a ^= secret[1]; b ^= seed; rapid_mum(&a, &b);
    return rapid_mix(a ^ secret[0] ^ len, b ^ secret[1]);
}

template <bool RANDOM_SECRET>
struct Rapidhash {
    static constexpr const char* name = RANDOM_SECRET ? "rapidhash v1 (random secret)" : "rapidhash v1 (default secret)";
    uint64_t sd; uint64_t secret[3];
    void seed(Rng& r) {
        sd = r.next();
        if (RANDOM_SECRET) for (int i = 0; i < 3; i++) secret[i] = r.next() | 1;
        else memcpy(secret, RAPID_SECRET_DEFAULT, sizeof secret);
    }
    uint64_t operator()(const uint8_t* p, size_t len) const { return rapidhash_ref(p, len, sd, secret); }
};

/* ================================================================== */
/*  MUM hash (Vladimir Makarov, mum.h master 2016-2025), default macro   */
/*  configuration (MUM_V1/V2/V3 and MUM_QUALITY undefined), aligned      */
/*  path.  _MUM_UNROLL_FACTOR = 8 on x86-64, 16 on aarch64 (template).   */
/* ================================================================== */
static const uint64_t MUM_PRIMES[16] = {
    0X9ebdcae10d981691, 0X32b9b9b97a27ac7d, 0X29b5584d83d35bbd, 0X4b04e0e61401255f,
    0X25e8f7b1f1c9d027, 0X80d4c8c000f3e881, 0Xbd1255431904b9dd, 0X8a3bd4485eee6d81,
    0X3bc721b2aad05197, 0X71b1a19b907d6e33, 0X525e6c1084a8534b, 0X9e4c2cd340c1299f,
    0Xde3add92e94caa37, 0X7e14eadb1f65311d, 0X3f5aa40f89812853, 0X33b15a3b587d15c9,
};
static const uint64_t MUM_BLOCK_START_PRIME = 0xc42b5e2e6480b23bULL;
static const uint64_t MUM_UNROLL_PRIME = 0x7b51ec3d22f7096fULL;
static const uint64_t MUM_TAIL_PRIME = 0xaf47d47c99b1461bULL;
static inline uint64_t _mum(uint64_t v, uint64_t p) { return mum_add(v, p); }
// default (non-MUM_V3) _mum_xor: guards against a zero multiplicand
static inline uint64_t _mum_xor(uint64_t a, uint64_t b) { return (a ^ b) != 0 ? a ^ b : b; }

template <int UNROLL>
static inline uint64_t mum_hash_ref(const void* key, size_t len, uint64_t seed) {
    uint64_t result = seed + len;
    const uint8_t* str = (const uint8_t*)key;
    result = _mum(result, MUM_BLOCK_START_PRIME);
    while (len > UNROLL * sizeof(uint64_t)) {
        for (int i = 0; i < UNROLL; i += 2)
            result ^= _mum(_mum_xor(rd64(str + 8 * i), MUM_PRIMES[i]), _mum_xor(rd64(str + 8 * (i + 1)), MUM_PRIMES[i + 1]));
        len -= UNROLL * sizeof(uint64_t); str += UNROLL * sizeof(uint64_t);
        result = _mum(result, MUM_UNROLL_PRIME);
    }
    size_t n = len / sizeof(uint64_t);
    for (size_t i = 0; i < n; i++) result ^= _mum(rd64(str + 8 * i), MUM_PRIMES[i]);
    len -= n * sizeof(uint64_t); str += n * sizeof(uint64_t);
    if (len) {  // tail (1..7 bytes): _MUM_TAIL_START = 0 in the default configuration
        uint64_t u64 = 0; memcpy(&u64, str, len);
        result ^= _mum(u64, MUM_TAIL_PRIME);
    }
    return _mum(result, result);   // _mum_final, default configuration
}

template <int UNROLL>
struct Mum {
    static constexpr const char* name = UNROLL == 8 ? "MUM v3 (unroll 8, x86-64 default)" : "MUM v3 (unroll 16, aarch64 default)";
    uint64_t sd;
    void seed(Rng& r) { sd = r.next(); }
    uint64_t operator()(const uint8_t* p, size_t len) const { return mum_hash_ref<UNROLL>(p, len, sd); }
};

/* ================================================================== */
/*  XXH3_64bits_withSeed (xxHash 0.8.x), lengths 9..240 only            */
/* ================================================================== */
static const uint8_t XXH3_KSECRET[192] = {
    0xb8,0xfe,0x6c,0x39,0x23,0xa4,0x4b,0xbe,0x7c,0x01,0x81,0x2c,0xf7,0x21,0xad,0x1c,
    0xde,0xd4,0x6d,0xe9,0x83,0x90,0x97,0xdb,0x72,0x40,0xa4,0xa4,0xb7,0xb3,0x67,0x1f,
    0xcb,0x79,0xe6,0x4e,0xcc,0xc0,0xe5,0x78,0x82,0x5a,0xd0,0x7d,0xcc,0xff,0x72,0x21,
    0xb8,0x08,0x46,0x74,0xf7,0x43,0x24,0x8e,0xe0,0x35,0x90,0xe6,0x81,0x3a,0x26,0x4c,
    0x3c,0x28,0x52,0xbb,0x91,0xc3,0x00,0xcb,0x88,0xd0,0x65,0x8b,0x1b,0x53,0x2e,0xa3,
    0x71,0x64,0x48,0x97,0xa2,0x0d,0xf9,0x4e,0x38,0x19,0xef,0x46,0xa9,0xde,0xac,0xd8,
    0xa8,0xfa,0x76,0x3f,0xe3,0x9c,0x34,0x3f,0xf9,0xdc,0xbb,0xc7,0xc7,0x0b,0x4f,0x1d,
    0x8a,0x51,0xe0,0x4b,0xcd,0xb4,0x59,0x31,0xc8,0x9f,0x7e,0xc9,0xd9,0x78,0x73,0x64,
    0xea,0xc5,0xac,0x83,0x34,0xd3,0xeb,0xc3,0xc5,0x81,0xa0,0xff,0xfa,0x13,0x63,0xeb,
    0x17,0x0d,0xdd,0x51,0xb7,0xf0,0xda,0x49,0xd3,0x16,0x55,0x26,0x29,0xd4,0x68,0x9e,
    0x2b,0x16,0xbe,0x58,0x7d,0x47,0xa1,0xfc,0x8f,0xf8,0xb8,0xd1,0x7a,0xd0,0x31,0xce,
    0x45,0xcb,0x3a,0x8f,0x95,0x16,0x04,0x28,0xaf,0xd7,0xfb,0xca,0xbb,0x4b,0x40,0x7e,
};
static const uint64_t XXH_PRIME64_1 = 0x9E3779B185EBCA87ULL;
static const uint64_t XXH_PRIME_MX1 = 0x165667919E3779F9ULL;
static inline uint64_t xxh3_avalanche(uint64_t h) { h ^= h >> 37; h *= XXH_PRIME_MX1; h ^= h >> 32; return h; }
static inline uint64_t xxh3_mix16B(const uint8_t* in, const uint8_t* sec, uint64_t seed) {
    uint64_t lo = rd64(in), hi = rd64(in + 8);
    return mum_xor(lo ^ (rd64(sec) + seed), hi ^ (rd64(sec + 8) - seed));
}
static inline uint64_t xxh3_64_ref(const uint8_t* in, size_t len, uint64_t seed) {
    const uint8_t* sec = XXH3_KSECRET;
    if (len <= 16) {      // only 9..16 supported here
        uint64_t bitflip1 = (rd64(sec + 24) ^ rd64(sec + 32)) + seed;
        uint64_t bitflip2 = (rd64(sec + 40) ^ rd64(sec + 48)) - seed;
        uint64_t input_lo = rd64(in) ^ bitflip1, input_hi = rd64(in + len - 8) ^ bitflip2;
        uint64_t acc = len + __builtin_bswap64(input_lo) + input_hi + mum_xor(input_lo, input_hi);
        return xxh3_avalanche(acc);
    }
    if (len > 128) {  // 129..240: XXH3_len_129to240_64b
        uint64_t acc = len * XXH_PRIME64_1;
        size_t nbRounds = len / 16;
        for (size_t i = 0; i < 8; i++) acc += xxh3_mix16B(in + 16 * i, sec + 16 * i, seed);
        acc = xxh3_avalanche(acc);
        for (size_t i = 8; i < nbRounds; i++) acc += xxh3_mix16B(in + 16 * i, sec + 16 * (i - 8) + 3, seed);   // XXH3_MIDSIZE_STARTOFFSET = 3
        acc += xxh3_mix16B(in + len - 16, sec + 136 - 17, seed);                                            // SECRET_SIZE_MIN - MIDSIZE_LASTOFFSET
        return xxh3_avalanche(acc);
    }
    // 17..128
    uint64_t acc = len * XXH_PRIME64_1;
    if (len > 32) {
        if (len > 64) {
            if (len > 96) { acc += xxh3_mix16B(in + 48, sec + 96, seed); acc += xxh3_mix16B(in + len - 64, sec + 112, seed); }
            acc += xxh3_mix16B(in + 32, sec + 64, seed); acc += xxh3_mix16B(in + len - 48, sec + 80, seed);
        }
        acc += xxh3_mix16B(in + 16, sec + 32, seed); acc += xxh3_mix16B(in + len - 32, sec + 48, seed);
    }
    acc += xxh3_mix16B(in + 0, sec + 0, seed); acc += xxh3_mix16B(in + len - 16, sec + 16, seed);
    return xxh3_avalanche(acc);
}
template <bool SEEDED>
struct Xxh3 {
    static constexpr const char* name = SEEDED ? "XXH3-64 (random seed)" : "XXH3-64 (seed 0)";
    uint64_t sd;
    void seed(Rng& r) { sd = SEEDED ? r.next() : 0; }
    uint64_t operator()(const uint8_t* p, size_t len) const { return xxh3_64_ref(p, len, sd); }
};

#endif  // ADVERSARIAL_HASHES_H
