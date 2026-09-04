/* ***********************************************************************
 * Throughput-harness hash set (tools/bench/adversarial/speed.cpp).
 *
 * Every hash exposes   void seed(Rng&)   and   uint64_t operator()(const uint8_t*, size_t).
 * Threat model (fixed): the key/secret is random and hidden, the attacker
 * chooses inputs, collision probability is over the random secret.
 *
 * Paper hashes here use the repo's OPTIMIZED field arithmetic from
 * tools/bench/framework/multiplication_arm.h:
 *   - GF(2^64): gf64_mult / inj_smul (3x PMULL, x^64 + x^4 + x^3 + x + 1, r = 27)
 *   - F_{2^89-1}: fast_large_mult_mod (2 mul, lazy "smart" Mersenne reduction,
 *     64-bit multiplier) and extra_large_mult_add_mod (89 x 89 schoolbook + lazy
 *     reduction); one exact reduction at the end.
 * Vendored: komihash (header-only), UMASH (separate C TU), XXH3 from the system
 * xxhash.h (XXH_INLINE_ALL; the local hashes.h XXH3 port covers 9..240 bytes only).
 * ***********************************************************************/
#ifndef SPEED_HASHES_H
#define SPEED_HASHES_H

#include <iostream>            // framework/randomgen.h uses cout without including it
#include "hashes.h"            // Rng, rd64, gf64_mul, Wyhash, Rapidhash, Mum, VectorMultShift, reference PaperGF64/xxh3_64_ref
#include "../framework/multiplication_arm.h"
#include "../framework/injective_hashing_arm.h"
#include "vendor/komihash/komihash.h"
#include "vendor/umash/umash.h"
#define XXH_INLINE_ALL
#include <xxhash.h>
#include "vendor/polymur/polymur-hash.h"   // Orson Peters' Polymur (proven, 4-word key)
#include "../chainhash/chainhash.h"        // ChainHash: PH blocks + three-key injective recurrence + additive twist + degree-5 finalizer

/* XXH3-128 with a random seed; both halves XORed only to feed the benchmark sink. */
struct Xxh3_128Seeded {
    uint64_t sd;
    void seed(Rng& r) { sd = r.next(); }
    uint64_t operator()(const uint8_t* b, size_t n) const { XXH128_hash_t h = XXH3_128bits_withSeed(b, n, sd); return h.low64 ^ h.high64; }
};

/* Polymur with a fully random key: k from k_seed (a generator 37^e), s from s_seed. */
struct Polymur {
    PolymurHashParams p;
    void seed(Rng& r) { polymur_init_params(&p, r.next(), r.next()); }
    uint64_t operator()(const uint8_t* b, size_t n) const { return polymur_hash(b, n, &p, 0); }
};

/* ChainHash with BW-word PH blocks (8*BW bytes of PH key), the degree-K
 * finalizer behind the additive input twist (K = 5 is the only shipped
 * chain: 3 multiplications) and S sub-blocks per block.
 * Shipped: <32, 5, 1> = chainhash-256, <128, 5, 2> = chainhash-1k. */
template <int BW, int K = 5, int S = 1>
struct ChainHashRow {
    chainhash::ChainHash<BW, K, S> h{0};
    void seed(Rng& r) { h.init(r.next()); }
    uint64_t operator()(const uint8_t* b, size_t n) const { return h(b, n); }
};

/* ================================================================== */
/*  GF(2^64) arithmetic kept in NEON registers (no GPR round trips).    */
/*  Layout: every value lives in lane 0; lane 1 of a state register is  */
/*  garbage that nothing reads (consumers take lane 0, or the high half  */
/*  of a fresh 128-bit product).  Reduction: x^64 = 27, applied twice.  */
/* ================================================================== */
namespace gf64v {
static inline uint8x16_t pmull_lo(uint8x16_t a, uint8x16_t b) {   // lane0(a) * lane0(b); inline asm: clang would emit DUP + PMULL2
    uint8x16_t r; __asm__("pmull %0.1q, %1.1d, %2.1d" : "=w"(r) : "w"(a), "w"(b)); return r;
}
static inline uint8x16_t pmull_hi(uint8x16_t a, uint8x16_t b) {   // lane1(a) * lane1(b)
    uint8x16_t r; __asm__("pmull2 %0.1q, %1.2d, %2.2d" : "=w"(r) : "w"(a), "w"(b)); return r;
}
static inline uint8x16_t RR() { return vreinterpretq_u8_u64(vdupq_n_u64(27)); }
static inline uint8x16_t reduce(uint8x16_t ab, uint8x16_t RR) {          // 128-bit product -> lane 0 (lane 1 garbage)
    uint8x16_t xr = pmull_hi(ab, RR);
    uint8x16_t zr = pmull_hi(xr, RR);
    return xor128(xor128(ab, xr), zr);
}
static inline uint8x16_t mul(uint8x16_t a, uint8x16_t b, uint8x16_t RR) { return reduce(pmull_lo(a, b), RR); }
/* Recurrence step on state Q = P + u:  Q' = (a + u) + (b + y) Q.
 * bv has b + y in lane 0, av has a in lane 0 (loaded straight into SIMD). */
static inline uint8x16_t step(uint8x16_t Q, uint8x16_t bv, uint8x16_t av, uint8x16_t U, uint8x16_t RR) {
    uint8x16_t ab = pmull_lo(bv, Q);
    uint8x16_t xr = pmull_hi(ab, RR);
    uint8x16_t zr = pmull_hi(xr, RR);
    return xor128(xor128(xor128(ab, xr), zr), xor128(av, U));
}
/* Operand loads for the pair (a, b) at p: b into lane 0 via a 16-byte load at
 * p + 8 (reads the next pair's a into lane 1, so only valid when p + 24 <= end),
 * or via an 8-byte load for the last pair; a via an 8-byte load. */
static inline uint8x16_t a_lane(const uint8_t* p) {
    return vreinterpretq_u8_u64(vcombine_u64(vld1_u64((const uint64_t*)p), vdup_n_u64(0)));
}
static inline uint8x16_t b_wide(const uint8_t* p, uint8x16_t Y) { return xor128(vld1q_u8(p + 8), Y); }
static inline uint8x16_t b_last(const uint8_t* p, uint8x16_t Y) {
    return xor128(vreinterpretq_u8_u64(vcombine_u64(vld1_u64((const uint64_t*)(p + 8)), vdup_n_u64(0))), Y);
}
}  // namespace gf64v

/* ================================================================== */
/*  Paper GF(2^64) three-key recurrence, framework arithmetic,          */
/*  NEON-resident.  Keys u, y, z independent uniform field elements:    */
/*  P_0 = z,  P_i = a_i + (b_i + y)(P_{i-1} + u),  16 bytes/step.       */
/*  The difference polynomial of two distinct n-pair messages is nonzero */
/*  of total degree <= n in (u, y, z) (the top term y^n (z + u) cancels), */
/*  so Pr[collision] <= n/2^64 (Schwartz-Zippel).  Three 64-bit keys.   */
/*  The single-key recurrence of hashes.h PaperGF64 is the special case  */
/*  (u, y, z) = (x^2, x^3, x).                                           */
/* ================================================================== */
struct PaperGF64Opt {
    static constexpr const char* name = "Paper GF(2^64) injective, three keys (framework gf64_mult, NEON-resident)";
    uint64_t u, y, z;
    void set_key(uint64_t u_, uint64_t y_, uint64_t z_) { u = u_; y = y_; z = z_; }
    void seed(Rng& r) { uint64_t a = r.next(), b = r.next(), c = r.next(); set_key(a, b, c); }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        const uint8x16_t Y = from64(y), U = from64(u);
        const uint8x16_t RR = gf64v::RR();
        uint8x16_t Q = from64(z ^ u);                       // state Q = P + u, lane 0
        size_t i = 0;
        for (; i + 24 <= len; i += 16) Q = gf64v::step(Q, gf64v::b_wide(p + i, Y), gf64v::a_lane(p + i), U, RR);
        if (i + 16 <= len)             Q = gf64v::step(Q, gf64v::b_last(p + i, Y), gf64v::a_lane(p + i), U, RR);
        return lower64(Q) ^ u;
    }
};

/* Same three-key recurrence, L independent interleaved lanes (pair i -> lane
 * i mod L, every lane starting from P_0 = z), combined with an independent
 * fourth key w:  H = sum_j P_j * w^j, evaluated as a balanced tree with
 * w^2, w^4 derived per call (two squarings, off the critical path).  Each
 * lane holds at most ceil(N/L) pairs, so the difference polynomial in
 * (u, y, z, w) is nonzero of total degree <= ceil(N/L) + L - 1 and
 * Pr[collision] <= (ceil(N/L) + L - 1)/2^64 (Schwartz-Zippel).  Four keys. */
template <int L>
struct PaperGF64Lanes {
    static_assert(L == 1 || L == 2 || L == 4 || L == 8 || L == 16, "tree combine needs a power-of-two lane count");
    static constexpr const char* name = "Paper GF(2^64) injective, three keys, L interleaved lanes + tree-in-w combine";
    uint64_t u, y, z, w;
    void seed(Rng& r) { u = r.next(); y = r.next(); z = r.next(); w = r.next(); }
    template <int n>
    static inline uint8x16_t tree(const uint8x16_t* P, const uint8x16_t* wp, uint8x16_t RR) {   // sum_{j<n} P_j w^j
        if constexpr (n == 1) return P[0];
        else {
            constexpr int h = n / 2, k = (h == 1) ? 0 : (h == 2) ? 1 : (h == 4) ? 2 : 3;   // wp[k] = w^h
            return xor128(tree<h>(P, wp, RR), gf64v::mul(tree<h>(P + h, wp, RR), wp[k], RR));
        }
    }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        const uint8x16_t Y = from64(y), U = from64(u);
        const uint8x16_t RR = gf64v::RR();
        uint8x16_t Q[L];
        for (int j = 0; j < L; j++) Q[j] = from64(z ^ u);
        size_t i = 0;
        for (; i + 16 * L + 8 <= len; i += 16 * L)
            for (int j = 0; j < L; j++) Q[j] = gf64v::step(Q[j], gf64v::b_wide(p + i + 16 * j, Y), gf64v::a_lane(p + i + 16 * j), U, RR);
        for (int j = 0; i + 16 <= len; i += 16, j++)                       // tail pairs, lanes 0,1,...
            Q[j] = gf64v::step(Q[j], (i + 24 <= len) ? gf64v::b_wide(p + i, Y) : gf64v::b_last(p + i, Y), gf64v::a_lane(p + i), U, RR);
        constexpr int KP = (L == 1) ? 1 : (L == 2) ? 1 : (L == 4) ? 2 : (L == 8) ? 3 : 4;   // powers w^(2^k) needed
        uint8x16_t wp[4];
        wp[0] = from64(w);
        for (int k = 1; k < KP; k++) wp[k] = gf64v::mul(wp[k - 1], wp[k - 1], RR);
        for (int j = 0; j < L; j++) Q[j] = xor128(Q[j], U);                // back to P_j
        return lower64(tree<L>(Q, wp, RR));
    }
};

/* ================================================================== */
/*  Mersenne prime p = 2^89 - 1 helpers                                 */
/* ================================================================== */
static const u128 M89P = (((u128)1) << 89) - 1;
static inline u128 m89_reduce(u128 h) {            // any 128-bit h  ->  [0, p)
    h = (h & M89P) + (h >> 89);
    h = (h & M89P) + (h >> 89);
    if (h >= M89P) h -= M89P;
    return h;
}
// slow reference product (binary method), used for key setup and selftests
static inline u128 m89_ref_mulmod(u128 a, u128 b) {
    a = m89_reduce(a); b = m89_reduce(b);
    u128 r = 0;
    for (int i = 0; i < 89; i++) {
        if ((b >> i) & 1) { r += a; if (r >= M89P) r -= M89P; }
        a <<= 1; if (a >= M89P) a -= M89P;
    }
    return r;
}
static inline u128 m89_random_key(Rng& r) { u128 x; do { x = r.next128() >> 39; } while (x >= M89P); return x; }

/* Horner over F_{2^89-1}: h = h*x + m_i, 64-bit key x (uniform on [0,2^64)),
 * one framework fast_large_mult_mod per word, exact reduction once at the end.
 * Message words are 8-byte (W=8) or 11-byte (W=11, 88-bit < p) chunks.
 * Pr[collision] <= (words-1) * 2^25 / p  ~  words / 2^64  (64-bit truncated output). */
template <int W>
struct MersHorner89 {
    static constexpr const char* name = "Mersenne 2^89-1 Horner, fast_large_mult_mod, 64-bit key";
    uint64_t x;
    void seed(Rng& r) { x = r.next(); }
    static inline u128 word(const uint8_t* p, size_t n) {         // n <= 11 bytes, zero-extended
        uint64_t lo = 0, hi = 0;
        if (n >= 8) { lo = rd64(p); memcpy(&hi, p + 8, n - 8); } else memcpy(&lo, p, n);
        return ((u128)hi << 64) | lo;
    }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        u128 h = 0;
        size_t i = 0;
        if (W == 8) {
            for (; i + 8 <= len; i += 8) h = fast_large_mult_mod(h, rd64(p + i), x);
        } else {
            for (; i + 11 <= len; i += 11) {
                uint64_t lo = rd64(p + i), hi = rd64(p + i + 3) >> 40;    // bytes 8..10
                h = fast_large_mult_mod(h, ((u128)hi << 64) | lo, x);
            }
        }
        if (i < len) h = fast_large_mult_mod(h, word(p + i, len - i), x);   // zero-padded tail word
        return (uint64_t)m89_reduce(h);
    }
};

/* Paper injective recurrence over F_{2^89-1}, two keys (x in [0,p), y in [0,2^63)):
 *   P_0 = x,  P_i = a_i + (b_i + y)(P_{i-1} + x^2)
 * with a_i an 8-byte word and b_i a 7-byte word (b_i + y < 2^64), so that each
 * step is ONE framework fast_large_mult_mod(P + x^2, a_i, b_i + y) (2 mul).
 * 15 bytes per step.  Total degree N+2 in (x,y); Pr[collision] <= (N+2)*2/2^64. */
struct PaperMers89Smart {
    static constexpr const char* name = "Paper injective over F_{2^89-1}, fast_large_mult_mod, 15-byte steps";
    u128 x, x2; uint64_t y;
    void seed(Rng& r) { x = m89_random_key(r); x2 = m89_ref_mulmod(x, x); y = r.next() >> 1; }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        u128 P = x;
        size_t i = 0;
        for (; i + 15 <= len; i += 15) {
            uint64_t a = rd64(p + i), b = rd64(p + i + 7) >> 8;           // b = bytes 8..14 (56 bits)
            P = fast_large_mult_mod(P + x2, a, b + y);
        }
        if (i < len) {                                                     // zero-padded tail (< 15 bytes)
            uint64_t a = 0, b = 0; size_t n = len - i;
            if (n >= 8) { a = rd64(p + i); memcpy(&b, p + i + 8, n - 8); } else memcpy(&a, p + i, n);
            P = fast_large_mult_mod(P + x2, a, b + y);
        }
        return (uint64_t)m89_reduce(P);
    }
};

/* Paper injective recurrence over F_{2^89-1}, single 89-bit key x:
 *   P_0 = x,  P_i = a_i + (b_i + x^3)(P_{i-1} + x^2),  a_i, b_i 8-byte words.
 * General 89 x 89 product: framework extra_large_mult_add_mod (schoolbook, lazy
 * reduction).  16 bytes per step.  Pr[collision] <= (3N+2)*2^25/p ~ (3N+2)/2^64. */
struct PaperMers89General {
    static constexpr const char* name = "Paper injective over F_{2^89-1}, extra_large_mult_add_mod, 16-byte steps";
    u128 x, x2, x3;
    void seed(Rng& r) { x = m89_random_key(r); x2 = m89_ref_mulmod(x, x); x3 = m89_ref_mulmod(x2, x); }
    uint64_t operator()(const uint8_t* p, size_t len) const {
        u128 P = x;
        for (size_t i = 0; i + 16 <= len; i += 16)
            P = extra_large_mult_add_mod(rd64(p + i + 8) + x3, P + x2, rd64(p + i));
        return (uint64_t)m89_reduce(P);
    }
};

/* ================================================================== */
/*  Framework universal-hash classes (injective_hashing_arm.h).         */
/*  The MESSAGE lives inside the object (filled by init() from the      */
/*  framework's bytes1.bin); the KEY x is the call argument.            */
/* ================================================================== */
template <class C, size_t WORDS>
struct FW {
    static constexpr size_t bytes = WORDS * 8;
    C c; uint64_t x;
    void seed(Rng& r) { c.init(); x = r.next(); }
    uint64_t operator()(const uint8_t*, size_t) { return c(x); }
};

/* ================================================================== */
/*  Vendored heuristics / hybrids                                       */
/* ================================================================== */
struct Komihash {
    static constexpr const char* name = "komihash 5.34 (random seed)";
    uint64_t sd;
    void seed(Rng& r) { sd = r.next(); }
    uint64_t operator()(const uint8_t* p, size_t n) const { return komihash(p, n, sd); }
};

struct Umash64 {
    static constexpr const char* name = "UMASH 64-bit umash_full (random 32-byte key)";
    struct umash_params params;
    void seed(Rng& r) { uint8_t key[32]; for (int i = 0; i < 4; i++) wr64(key + 8 * i, r.next()); umash_params_derive(&params, 0, key); }
    uint64_t operator()(const uint8_t* p, size_t n) const { return umash_full(&params, 0, 0, p, n); }
};
struct Umash128 {
    static constexpr const char* name = "UMASH 128-bit umash_fprint (random 32-byte key)";
    struct umash_params params;
    void seed(Rng& r) { uint8_t key[32]; for (int i = 0; i < 4; i++) wr64(key + 8 * i, r.next()); umash_params_derive(&params, 0, key); }
    uint64_t operator()(const uint8_t* p, size_t n) const { struct umash_fp f = umash_fprint(&params, 0, p, n); return f.hash[0] ^ f.hash[1]; }
};

struct Xxh3Seeded {
    static constexpr const char* name = "XXH3-64 0.8.3 withSeed (random seed)";
    uint64_t sd;
    void seed(Rng& r) { sd = r.next(); }
    uint64_t operator()(const uint8_t* p, size_t n) const { return XXH3_64bits_withSeed(p, n, sd); }
};
struct Xxh3Secret {
    static constexpr const char* name = "XXH3-64 0.8.3 withSecret (random 192-byte secret)";
    uint8_t secret[192];
    void seed(Rng& r) { for (int i = 0; i < 24; i++) wr64(secret + 8 * i, r.next()); }
    uint64_t operator()(const uint8_t* p, size_t n) const { return XXH3_64bits_withSecret(p, n, secret, sizeof secret); }
};

#endif  // SPEED_HASHES_H
