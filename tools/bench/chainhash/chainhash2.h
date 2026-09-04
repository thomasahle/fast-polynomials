/* ***********************************************************************
 * ChainHash-2 -- CANDIDATE definition variant of ChainHash: STRIDED WORD
 * PAIRING (item B1 of the performance plan).  Not the shipped function:
 * chainhash.h is the function behind the registered SMHasher3 verification
 * codes; this header exists to measure what the re-pairing is worth.
 * Header-only, arm64 (NEON PMULL).  Reference: chainhash2_ref.h.
 *
 * THE ONE DEFINITIONAL CHANGE (level 1, the PH/CLNH pairing).
 *   chainhash.h : pair s of a (sub-)block is (w_{2s}, w_{2s+1}) with keys
 *                 (k_{2s}, k_{2s+1}); the last block holds W' = ceil(r/16)
 *                 pairs, the final partial pair zero-padded to 16 bytes.
 *   chainhash2.h: the four words of every 32-byte group,
 *                 (w_{4j}, w_{4j+1}, w_{4j+2}, w_{4j+3}), form the two pairs
 *                 (w_{4j}, w_{4j+2}) and (w_{4j+1}, w_{4j+3}), every word
 *                 XORed with the key word of its OWN position:
 *       PH(g) = XOR_j [ clmul64(w_{4j}   ^ k_{4j},   w_{4j+2} ^ k_{4j+2})
 *                     ^ clmul64(w_{4j+1} ^ k_{4j+1}, w_{4j+3} ^ k_{4j+3}) ];
 *                 the last block (r bytes) is zero-padded to a whole number
 *                 of 32-byte groups: G' = ceil(r/32) groups = W' = 2G' pairs
 *                 (W' = 0 for the empty message), using k[0..4G').
 *   Equivalently: apply the fixed permutation pi that swaps the two middle
 *   words of every 32-byte group to the padded words AND to the key segment,
 *   then pair adjacent words as chainhash.h does -- for 32 | len the two
 *   hashes agree exactly under (k, m) -> (pi k, pi m) (test T8).  Pair
 *   counts are always even; a message of 1..16 bytes has 2 pairs, the second
 *   one being (0 + k_1)(0 + k_3) (a key constant, precomputed in setup()).
 * Everything else is unchanged from chainhash.h: the sub-block split S, the
 * three-key recurrence P_0 = z, P_i = a_i + (b_i + y)(P_{i-1} + u) over
 * GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1), the byte length XORed into
 * the a of the last pair, the integer-add input twist v = P_n + t_in, the
 * degree-5 circuit CIRCUITS[5] (3 multiplications, 5-wise independent
 * outputs), the key layout and derivation order (k[0..BLOCK_WORDS), u, y, z,
 * c[0..5), t_in = BLOCK_WORDS + 9 uniform words), and the collision bound
 * (p + 2)/2^64 for messages of at most p (sub-)block pairs.
 *
 * WHY.  A 16-byte NEON load puts two ADJACENT words into lanes 0 and 1, and
 * PMULL / PMULL2 multiply lane 0 x lane 0 / lane 1 x lane 1 of two registers;
 * so the adjacent pairing of chainhash.h needs one EXT per two pairs to line
 * the operands up (12 SIMD ops per 64 bytes: 4 EOR, 2 EXT, 4 PMULL, 2 EOR3),
 * while the strided pairing takes both operands straight from two loads
 * (10 ops: 4 EOR, 4 PMULL, 2 EOR3).  The PH loop is bound by SIMD issue
 * (4/cycle on M2), not by loads or by the recurrence, so this is the whole
 * gain: 56 -> 48 SIMD ops per 256-byte block.  On x86 (VPCLMULQDQ selects
 * either half of either operand) the adjacent pairing already needs no
 * shuffle, so the change is neutral there.
 *
 * PROOF.  Lemma "CLNH is 2^-64-XOR-universal on 128 bits" of the appendix
 * quantifies over uniform key segments and arbitrary word tuples of a given
 * pair count; a fixed permutation of the word positions, applied to the
 * data and the key alike, changes neither, so it and the stream lemma
 * (equal / different lengths, equal / different pair counts) apply verbatim
 * to the permuted tuples with the pair count w_t = 2 ceil(r_t / 32) in place
 * of ceil(r_t / 16).  Levels 2 and 3 are untouched.
 *
 * Evaluation schedule (same organisation as chainhash.h): constants folded
 * into reductions (reduce_add); a message of at most one sub-block takes a
 * loop-free leaf path whose key-only parts are constants of the key; the
 * multi-step path is out of line (tail call); blocks 0..n-2 run on the state
 * Q = P + u without length logic; the last block is peeled; sub-blocks of
 * <= CHAINHASH2_LAZY_WORDS words carry the recurrence state unreduced
 * (step_lazy, 8-cycle chain; default 16 as in chainhash.h -- define the
 * macro to 32 / 128 to try the lazy state on the shipped block sizes).
 * The input is never read outside [m, m + len): whole 64-byte and 32-byte
 * groups are loaded in place (so are the first 16 bytes of a partial group
 * of >= 16 bytes); the last 1..15 bytes of a partial group are read as the
 * 16 bytes ending at m + len and realigned by one TBL byte shift (indices
 * >= 16 read as zero = the padding); a message shorter than 16
 * bytes uses overlapping lane loads + one TBL gather.  No memcpy, no stack
 * copy.  A message of 9..16 bytes has two pair products; the loop-free
 * step folds them separately (reduce2_add) so that its latency equals the
 * one-pair case.
 *
 * Compile: clang++ -O3 -std=c++17 -march=native+crypto.  Self-contained
 * (does not include the framework headers; the scalar gfmul used at key
 * setup is the NEON multiply below).
 * *********************************************************************** */

#ifndef CHAINHASH2_H
#define CHAINHASH2_H

#include <arm_neon.h>
#include <cstddef>
#include <cstdint>
#include <cstring>

#ifndef CHAINHASH2_LAZY_WORDS
#define CHAINHASH2_LAZY_WORDS 16   // sub-blocks of at most this many words use the unreduced recurrence state
#endif

namespace chainhash2 {

/* splitmix64: deterministic key derivation from a 64-bit seed (same as chainhash.h). */
static inline uint64_t splitmix64(uint64_t& state) {
    uint64_t z = (state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* PMULL on the low halves / PMULL2 on the high halves, pinned by inline asm
 * (see chainhash.h for why: with the intrinsics clang routes lane-0 x lane-1
 * products and the recurrence state through general registers). */
#if defined(_MSC_VER) && !defined(__clang__)
static inline uint64x2_t pmull_lo(uint64x2_t a, uint64x2_t b) {
    return vreinterpretq_u64_p128(vmull_p64(vgetq_lane_p64(vreinterpretq_p64_u64(a), 0), vgetq_lane_p64(vreinterpretq_p64_u64(b), 0)));
}
static inline uint64x2_t pmull_hi(uint64x2_t a, uint64x2_t b) {
    return vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b)));
}
#else
static inline uint64x2_t pmull_lo(uint64x2_t a, uint64x2_t b) {   // lane0(a) * lane0(b) -> 128 bits
    uint64x2_t r; __asm__("pmull %0.1q, %1.1d, %2.1d" : "=w"(r) : "w"(a), "w"(b)); return r;
}
static inline uint64x2_t pmull_hi(uint64x2_t a, uint64x2_t b) {   // lane1(a) * lane1(b) -> 128 bits
    uint64x2_t r; __asm__("pmull2 %0.1q, %1.2d, %2.2d" : "=w"(r) : "w"(a), "w"(b)); return r;
}
#endif
static inline uint64x2_t xor3(uint64x2_t a, uint64x2_t b, uint64x2_t c) {
#if defined(__ARM_FEATURE_SHA3)
    return veor3q_u64(a, b, c);
#else
    return veorq_u64(veorq_u64(a, b), c);
#endif
}

/* Field arithmetic in NEON registers; every value lives in lane 0, lane 1 of
 * a state register is garbage that nothing reads.
 * Reduction: x^64 = 27 (= x^4 + x^3 + x + 1), applied twice via PMULL2. */
static inline uint64x2_t gf_rr() { return vdupq_n_u64(27); }
static inline uint64x2_t gf_reduce(uint64x2_t ab, uint64x2_t rr) {       // 128-bit product -> lane 0
    uint64x2_t xr = pmull_hi(ab, rr);
    uint64x2_t zr = pmull_hi(xr, rr);
    return xor3(ab, xr, zr);
}
/* reduce(ab) + add (lane 0); the addend overlaps the two folds (0 latency). */
static inline uint64x2_t reduce_add(uint64x2_t ab, uint64x2_t add, uint64x2_t rr) {
    uint64x2_t xr = pmull_hi(ab, rr);
    uint64x2_t zr = pmull_hi(xr, rr);
    return xor3(veorq_u64(ab, add), xr, zr);
}
/* reduce(ab1 + ab2) + add, with the two products folded SEPARATELY so that
 * neither waits for their sum: the loop-free small-key steps use it when a
 * message of 9..15 bytes has two pair products (the EOR that would join them
 * before the folds is off the chain; two extra PMULL2 and one extra EOR3). */
static inline uint64x2_t reduce2_add(uint64x2_t ab1, uint64x2_t ab2, uint64x2_t add, uint64x2_t rr) {
    uint64x2_t xr1 = pmull_hi(ab1, rr), xr2 = pmull_hi(ab2, rr);
    uint64x2_t zr1 = pmull_hi(xr1, rr), zr2 = pmull_hi(xr2, rr);
    uint64x2_t e = xor3(xor3(ab1, ab2, add), xr1, xr2);
    return xor3(zr1, zr2, e);
}
static inline uint64x2_t gfmul_v(uint64x2_t a, uint64x2_t b, uint64x2_t rr) {  // lane0(a) * lane0(b)
    return gf_reduce(pmull_lo(a, b), rr);
}
static inline uint64x2_t v64(uint64_t x) { return vcombine_u64(vcreate_u64(x), vcreate_u64(0)); }
/* Scalar GF(2^64) multiply (key setup and tests only). */
static inline uint64_t gfmul(uint64_t a, uint64_t b) {
    return vgetq_lane_u64(gfmul_v(v64(a), v64(b), gf_rr()), 0);
}

/* Only the degree-5 finalizer is shipped. */
static constexpr bool valid_degree(int K) { return K == 5; }
static constexpr int chain_mults(int K) { return K == 5 ? 3 : 0; }

/* ------------------------------------------------------------------ */
/* Key                                                                 */
/* ------------------------------------------------------------------ */
template <int BLOCK_WORDS = 32, int K = 5, int S = 1>
struct Key {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
                  "BLOCK_WORDS must be a positive multiple of 8*S "
                  "(two 32-byte groups = 4 accumulator products per inner iteration, per sub-block)");
    static_assert(valid_degree(K), "finalizer degree K must be 5 (the only shipped chain)");

    static constexpr int block_words = BLOCK_WORDS;
    static constexpr int block_bytes = 8 * BLOCK_WORDS;
    static constexpr int split = S;
    static constexpr int sub_words = BLOCK_WORDS / S;  // words per sub-block
    static constexpr int sub_bytes = 8 * sub_words;    // bytes per sub-block
    static constexpr int degree = K;
    static constexpr size_t random_key_bytes = 8 * (size_t)(BLOCK_WORDS + 3 + K + 1);

    alignas(16) uint64_t k[BLOCK_WORDS];  // PH level: word i of a (sub-)block is XORed with k[i]
    uint64_t u, y, z;                     // recurrence keys
    uint64_t c[K];                        // finalizer parameters
    uint64_t t_in;                        // input twist word

    /* Derived, message-independent values (setup()); not key material. */
    uint64x2_t UY;    // [u, y]
    uint64x2_t Yhi;   // [0, y]
    uint64x2_t ZUZU;  // [z + u, z + u]
    uint64x2_t YYZU;  // [y, y(z + u)]
    uint64x2_t TIN;   // [t_in, 0]
    uint64_t yzu;     // y (z + u):          S = 1, one pair-group of data:  P_1 = (a + len + yzu) + b (z + u)
    uint64_t yyzu_yu; // y y (z + u) + y u:  S = 2, fused double step:       P_2 = (len + yyzu_yu) + a y + b y(z+u)
    /* The same two constants with the key-only second pair (0 + k_1)(0 + k_3)
     * of a 1..8-byte message folded in ([ac, bc] = clmul64(k_1, k_3)):
     * a = a' + ac, b = b' + bc where (a', b') is the product of the first pair. */
    uint64_t yzu8;     // yzu + ac + bc (z + u)
    uint64_t yyzu_yu8; // yyzu_yu + ac y + bc y (z + u)

    void setup() {
        const uint64_t zu = z ^ u;
        UY = vcombine_u64(vcreate_u64(u), vcreate_u64(y));
        Yhi = vcombine_u64(vcreate_u64(0), vcreate_u64(y));
        ZUZU = vdupq_n_u64(zu);
        yzu = gfmul(y, zu);
        YYZU = vcombine_u64(vcreate_u64(y), vcreate_u64(yzu));
        TIN = vcombine_u64(vcreate_u64(t_in), vcreate_u64(0));
        yyzu_yu = gfmul(y, yzu) ^ gfmul(y, u);
        const uint64x2_t k13 = pmull_lo(v64(k[1]), v64(k[3]));   // (0 + k_1)(0 + k_3), unreduced 128 bits
        const uint64_t ac = vgetq_lane_u64(k13, 0), bc = vgetq_lane_u64(k13, 1);
        yzu8 = yzu ^ ac ^ gfmul(bc, zu);
        yyzu_yu8 = yyzu_yu ^ gfmul(ac, y) ^ gfmul(bc, yzu);
    }

    /* Derivation order from the seed: k[0..BLOCK_WORDS), u, y, z, c[0..K), t_in  (as chainhash.h). */
    static Key from_seed(uint64_t seed) {
        Key key;
        uint64_t s = seed;
        for (int i = 0; i < BLOCK_WORDS; i++) key.k[i] = splitmix64(s);
        key.u = splitmix64(s);
        key.y = splitmix64(s);
        key.z = splitmix64(s);
        for (int i = 0; i < K; i++) key.c[i] = splitmix64(s);
        key.t_in = splitmix64(s);
        key.setup();
        return key;
    }
};

/* ------------------------------------------------------------------ */
/* PH level primitives (strided pairing)                               */
/* ------------------------------------------------------------------ */

/* One 32-byte group: r0 = [w0, w1], r1 = [w2, w3] (any source), keys k[0..4):
 *   clmul64(w0 ^ k0, w2 ^ k2) ^ clmul64(w1 ^ k1, w3 ^ k3)
 * = pmull(t0, t1) ^ pmull2(t0, t1) with t0 = r0 ^ [k0, k1], t1 = r1 ^ [k2, k3]:
 * no shuffle on the data path. */
static inline __attribute__((always_inline)) uint64x2_t ph_group32(const uint64_t* __restrict k, uint64x2_t r0, uint64x2_t r1,
                                                                   uint64x2_t acc) {
    uint64x2_t t0 = veorq_u64(r0, vld1q_u64(k + 0));
    uint64x2_t t1 = veorq_u64(r1, vld1q_u64(k + 2));
    return xor3(acc, pmull_lo(t0, t1), pmull_hi(t0, t1));
}

/* Two 32-byte groups (64 bytes = 8 words = 4 pairs) at p with keys k[0..8),
 * into two independent accumulators.  Byte loads, no alignment assumption.
 * Reads exactly 64 bytes.  10 SIMD ops (4 EOR, 4 PMULL, 2 EOR3). */
static inline __attribute__((always_inline)) void ph_group(const uint64_t* __restrict k, const uint8_t* __restrict p, uint64x2_t& acc0,
                                                           uint64x2_t& acc1) {
    acc0 = ph_group32(k + 0, vreinterpretq_u64_u8(vld1q_u8(p + 0)),  vreinterpretq_u64_u8(vld1q_u8(p + 16)), acc0);
    acc1 = ph_group32(k + 4, vreinterpretq_u64_u8(vld1q_u8(p + 32)), vreinterpretq_u64_u8(vld1q_u8(p + 48)), acc1);
}

/* Full (sub-)block (8*WORDS bytes at blk, WORDS a multiple of 8). */
template <int WORDS>
static inline __attribute__((always_inline)) uint64x2_t ph_block(const uint64_t* __restrict k, const uint8_t* __restrict blk) {
    static_assert(WORDS > 0 && WORDS % 8 == 0, "ph_block: WORDS must be a positive multiple of 8");
    uint64x2_t acc0 = vdupq_n_u64(0), acc1 = vdupq_n_u64(0);
    for (int i = 0; i < WORDS; i += 8) ph_group(k + i, blk + 8 * i, acc0, acc1);
    return veorq_u64(acc0, acc1);
}

static inline __attribute__((always_inline)) uint64x2_t tbl(uint8x16_t v, uint8x16_t idx) {   // TBL: index >= 16 reads as 0
    return vreinterpretq_u64_u8(vqtbl1q_u8(v, idx));
}
static constexpr uint8_t kIota[16] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};

/* Byte-gather tables for a message of r < 16 bytes (as chainhash.h): out[i] =
 * t[r][i]-th byte of the lane-loaded vector (0xFF -> 0).  Layout:
 *   8 <= r <= 15: .d[0] = bytes 0..7, .d[1] = bytes r-8..r-1
 *   4 <= r <=  7: .s[0] = bytes 0..3, .s[1] = bytes r-4..r-1
 *   1 <= r <=  3: .b[0..2] = m[0], m[r/2], m[r-1] */
struct GatherTab {
    uint8_t t[16][16];
    constexpr GatherTab() : t() {
        for (int r = 0; r < 16; r++)
            for (int i = 0; i < 16; i++) {
                uint8_t v = 0xFF;
                if (r >= 8)      { if (i < 8) v = (uint8_t)i; else if (i < r) v = (uint8_t)(i + 16 - r); }
                else if (r >= 4) { if (i < 4) v = (uint8_t)i; else if (i < r) v = (uint8_t)(i + 8 - r); }
                else             { if (i < r) v = (uint8_t)i; }
                t[r][i] = v;
            }
    }
};
static constexpr GatherTab kGather{};

/* The whole message: r (1..15) bytes at m, zero-padded, as [w0, w1].  Reads
 * only [m, m + r), all loads straight into SIMD lanes. */
static inline __attribute__((always_inline)) uint64x2_t load_small(const uint8_t* m, size_t r) {
    uint8x16_t v = vdupq_n_u8(0);
    if (r >= 8) {
        v = vreinterpretq_u8_u64(vld1q_lane_u64(reinterpret_cast<const uint64_t*>(m), vreinterpretq_u64_u8(v), 0));
        v = vreinterpretq_u8_u64(vld1q_lane_u64(reinterpret_cast<const uint64_t*>(m + r - 8), vreinterpretq_u64_u8(v), 1));
    } else if (r >= 4) {
        v = vreinterpretq_u8_u32(vld1q_lane_u32(reinterpret_cast<const uint32_t*>(m), vreinterpretq_u32_u8(v), 0));
        v = vreinterpretq_u8_u32(vld1q_lane_u32(reinterpret_cast<const uint32_t*>(m + r - 4), vreinterpretq_u32_u8(v), 1));
    } else {
        v = vld1q_lane_u8(m, v, 0);
        v = vld1q_lane_u8(m + (r >> 1), v, 1);
        v = vld1q_lane_u8(m + r - 1, v, 2);
    }
    return tbl(v, vld1q_u8(kGather.t[r]));
}

/* Partial last (sub-)block: rem (1 .. 8*WORDS - 1) bytes at p, G' = ceil(rem/32)
 * groups = 2G' pairs, the final partial group zero-padded to 32 bytes.  Whole
 * 64-byte and 32-byte groups (and the first 16 bytes of a partial group of
 * more than 16 bytes) are loaded in place; the partial group's remaining
 * 1..16 bytes are read as the 16 bytes ENDING at p + rem and shifted right
 * with TBL (indices >= 16 read as zero = the padding).  PRECONDITION: the
 * 16 bytes ending at p + rem are readable, i.e. p + rem is the end of a
 * message of >= 16 bytes; nothing outside [p, p + rem) U [p + rem - 16, p + rem)
 * is read. */
template <int WORDS>
static inline __attribute__((always_inline)) uint64x2_t ph_tail(const uint64_t* __restrict k, const uint8_t* __restrict p, size_t rem) {
    uint64x2_t acc0 = vdupq_n_u64(0), acc1 = vdupq_n_u64(0);
    size_t pos = 0;  // bytes consumed; word index = pos / 8
    for (; pos + 64 <= rem; pos += 64) ph_group(k + pos / 8, p + pos, acc0, acc1);
    uint64x2_t acc = veorq_u64(acc0, acc1);
    size_t rest = rem - pos;  // 0..63
    if (rest > 32) {          // one whole group, then a partial one
        acc = ph_group32(k + pos / 8, vreinterpretq_u64_u8(vld1q_u8(p + pos)), vreinterpretq_u64_u8(vld1q_u8(p + pos + 16)), acc);
        pos += 32;
        rest -= 32;
    }
    if (rest > 16) {          // 17..32 bytes: [w0, w1] in place, [w2, w3] = the 16 bytes ending at p + rem, shifted
        const uint8x16_t b = vld1q_u8(p + rem - 16);
        const uint64x2_t r1 = tbl(b, vaddq_u8(vld1q_u8(kIota), vdupq_n_u8((uint8_t)(32 - rest))));
        acc = ph_group32(k + pos / 8, vreinterpretq_u64_u8(vld1q_u8(p + pos)), r1, acc);
    } else if (rest == 16) {  // exactly [w0, w1], in place; w2 = w3 = 0
        acc = ph_group32(k + pos / 8, vreinterpretq_u64_u8(vld1q_u8(p + pos)), vdupq_n_u64(0), acc);
    } else if (rest > 0) {    // 1..15 bytes: [w0, w1] = the 16 bytes ending at p + rem, shifted; w2 = w3 = 0
        const uint8x16_t a = vld1q_u8(p + rem - 16);
        const uint64x2_t r0 = tbl(a, vaddq_u8(vld1q_u8(kIota), vdupq_n_u8((uint8_t)(16 - rest))));
        acc = ph_group32(k + pos / 8, r0, vdupq_n_u64(0), acc);
    }
    return acc;
}

/* ------------------------------------------------------------------ */
/* Finalizer: the degree-5 circuit CIRCUITS[5] of website/js/char2.js  */
/* behind the integer-add input twist -- IDENTICAL to chainhash.h      */
/* (see its long comment for the rationale of the twist).              */
/*     y = x x;  z = (y + c0)(x + y + c1);  t = (x + c2)(z + c3);       */
/*   out = t + c4                                                      */
/* ------------------------------------------------------------------ */
template <int K>
static inline __attribute__((always_inline)) uint64x2_t chain_v(const uint64_t* c, uint64x2_t v) {   // v in lane 0
    static_assert(valid_degree(K), "chain: only K = 5 is shipped");
    const uint64x2_t rr = gf_rr();
    const uint64x2_t C0 = v64(c[0]), C1 = v64(c[1]), C2 = v64(c[2]), C3 = v64(c[3]), C4 = v64(c[4]);
    uint64x2_t ab = pmull_lo(v, v);                                            // x x, unreduced
    uint64x2_t xr = pmull_hi(ab, rr), zr = pmull_hi(xr, rr);
    uint64x2_t yc0  = xor3(veorq_u64(ab, C0), xr, zr);                         // y + c0
    uint64x2_t xyc1 = xor3(veorq_u64(ab, veorq_u64(v, C1)), xr, zr);           // x + y + c1
    uint64x2_t zc3  = reduce_add(pmull_lo(yc0, xyc1), C3, rr);                 // z + c3
    return reduce_add(pmull_lo(veorq_u64(v, C2), zc3), C4, rr);                // (x + c2)(z + c3) + c4
}
static inline __attribute__((always_inline)) uint64x2_t twist_v(uint64x2_t v, uint64_t t_in) {
    return vaddq_u64(v, v64(t_in));
}
template <int K>
static inline __attribute__((always_inline)) uint64_t chain(const uint64_t* c, uint64_t v) {
    return vgetq_lane_u64(chain_v<K>(c, v64(v)), 0);
}
template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64_t finalize(const Key<BLOCK_WORDS, K, S>& key, uint64_t v) {
    return vgetq_lane_u64(chain_v<K>(key.c, twist_v(v64(v), key.t_in)), 0);
}

/* ------------------------------------------------------------------ */
/* Recurrence step (as chainhash.h)                                    */
/* ------------------------------------------------------------------ */
/* On the state Q = P + u:  Q' = t[0] + t[1] Q  with t = [a + u, b + y]. */
static inline __attribute__((always_inline)) uint64x2_t step_q(uint64x2_t Q, uint64x2_t t, uint64x2_t rr) {
    return reduce_add(pmull_lo(vextq_u64(t, t, 1), Q), t, rr);
}
/* The same step on an UNREDUCED 128-bit state V (x^128 = 0x145 mod f): 8-cycle chain. */
static inline uint64x2_t gf_r2() { return vdupq_n_u64(0x145); }
static inline __attribute__((always_inline)) uint64x2_t step_lazy(uint64x2_t V, uint64x2_t t, uint64x2_t r2) {
    const uint64x2_t bb = vdupq_laneq_u64(t, 1);                              // [b + y, b + y]
    const uint64x2_t au = vcombine_u64(vget_low_u64(t), vdup_n_u64(0));      // [a + u, 0]
    const uint64x2_t p = pmull_lo(bb, V);
    const uint64x2_t q = pmull_hi(bb, V);
    return xor3(veorq_u64(p, au), vextq_u64(vdupq_n_u64(0), q, 1), pmull_hi(q, r2));
}

/* ------------------------------------------------------------------ */
/* HASH(m, len)                                                        */
/* ------------------------------------------------------------------ */
/* hash_small_v: len <= sub_bytes (every key <= 256 B / 512 B for the shipped
 * variants).  All data sits in sub-block 0 of the only block; sub-blocks
 * 1..S-1 are empty; no loop, no length bookkeeping.  A message of 1..8
 * bytes has the pairs (w0 + k0)(0 + k2) and (0 + k1)(0 + k3); the second
 * is a key constant folded into yzu8 / yyzu_yu8, so it costs nothing. */
template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64x2_t hash_small_v(const Key<BLOCK_WORDS, K, S>& key, const uint8_t* __restrict p, size_t len) {
    using key_t = Key<BLOCK_WORDS, K, S>;
    constexpr int SW = key_t::sub_words;
    constexpr bool FOLD8 = (S == 1 || S == 2);      // the loop-free steps below can absorb the key-only pair
    const uint64x2_t rr = gf_rr();
    const uint64_t cst_full = (S == 1) ? key.yzu : key.yyzu_yu;   // key-only constant of the loop-free step
    uint64x2_t acc;   // [a, b]  (for FOLD8 && len <= 8: the first pair only)
    uint64_t cst;
    if (len > 16) {
        acc = (len == 8 * (size_t)SW) ? ph_block<SW>(key.k, p) : ph_tail<SW>(key.k, p, len);
        cst = cst_full;
    } else if (len > 0) {
        // one zero-padded group: [w0, w1] (in place for 16 bytes, gathered below that), w2 = w3 = 0
        const uint64x2_t w01 = (len == 16) ? vreinterpretq_u64_u8(vld1q_u8(p)) : load_small(p, len);
        const uint64x2_t t0 = veorq_u64(w01, vld1q_u64(key.k));                  // [w0 + k0, w1 + k1]
        const uint64x2_t K23 = vld1q_u64(key.k + 2);                             // [k2, k3]
        const uint64x2_t pl = pmull_lo(t0, K23);                                 // (w0 + k0) k2
        if (FOLD8 && len <= 8) { acc = pl; cst = (S == 1) ? key.yzu8 : key.yyzu_yu8; }
        else if (FOLD8) {
            // 9..16 bytes, two pair products pl, ph: fold them separately (reduce2_add), so that the
            // step's latency is that of one pair
            const uint64x2_t ph = pmull_hi(t0, K23);                             // (w1 + k1) k3
            const uint64x2_t L = v64((uint64_t)len ^ cst_full);
            uint64x2_t P;
            if constexpr (S == 1) {
                P = reduce2_add(pmull_hi(pl, key.ZUZU), pmull_hi(ph, key.ZUZU), xor3(pl, ph, L), rr);
            } else {
                const uint64x2_t s1 = veorq_u64(pmull_lo(pl, key.YYZU), pmull_hi(pl, key.YYZU));
                const uint64x2_t s2 = veorq_u64(pmull_lo(ph, key.YYZU), pmull_hi(ph, key.YYZU));
                P = reduce2_add(s1, s2, L, rr);
            }
            return chain_v<K>(key.c, vaddq_u64(P, key.TIN));
        } else { acc = veorq_u64(pl, pmull_hi(t0, K23)); cst = cst_full; }
    } else {
        acc = vdupq_n_u64(0);
        cst = cst_full;
    }
    uint64x2_t P;  // P_S, lane 0
    if constexpr (S == 1) {
        // P_1 = a + len + (b + y)(z + u) = (a + len + y(z+u)) + b (z+u)
        P = reduce_add(pmull_hi(acc, key.ZUZU), veorq_u64(acc, v64((uint64_t)len ^ cst)), rr);
    } else if constexpr (S == 2) {
        // P_2 = len + y (P_1 + u) = (len + yu + yy(z+u)) + a y + b y(z+u)
        uint64x2_t pr = veorq_u64(pmull_lo(acc, key.YYZU), pmull_hi(acc, key.YYZU));
        P = reduce_add(pr, v64((uint64_t)len ^ cst), rr);
    } else {
        (void)cst;
        uint64x2_t Q = step_q(key.ZUZU, veorq_u64(acc, key.UY), rr);
        for (int i = 1; i + 1 < S; i++) Q = step_q(Q, key.UY, rr);
        P = step_q(Q, vsetq_lane_u64((uint64_t)len, key.Yhi, 0), rr);
    }
    return chain_v<K>(key.c, vaddq_u64(P, key.TIN));
}

template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64x2_t hash_multi_v(const Key<BLOCK_WORDS, K, S>& key, const uint8_t* __restrict p, size_t len) {
    using key_t = Key<BLOCK_WORDS, K, S>;
    constexpr size_t BB = (size_t)key_t::block_bytes;
    constexpr size_t SB = (size_t)key_t::sub_bytes;
    constexpr int SW = key_t::sub_words;
    constexpr bool LAZY = (SW <= CHAINHASH2_LAZY_WORDS);
    const uint64x2_t rr = gf_rr(), r2 = gf_r2();
    auto step = [&](uint64x2_t st, uint64x2_t t) {
        if constexpr (LAZY) return step_lazy(st, t, r2);
        else                return step_q(st, t, rr);
    };
    const size_t n = (len + BB - 1) / BB;  // >= 1 blocks (len > SB > 0)
    const uint64x2_t UY = key.UY;
    uint64x2_t st = LAZY ? vcombine_u64(vget_low_u64(key.ZUZU), vdup_n_u64(0)) : key.ZUZU;
    for (size_t j = 0; j + 1 < n; j++) {
        const uint8_t* blk = p + j * BB;
        for (int i = 0; i < S; i++) st = step(st, veorq_u64(ph_block<SW>(key.k + i * SW, blk + i * SB), UY));
    }
    const size_t off = (n - 1) * BB;
    const size_t rem = len - off;  // bytes of input in the last block: 1..BB
    for (int i = 0; i < S; i++) {
        const size_t soff = (size_t)i * SB;
        const size_t srem = (rem > soff) ? ((rem - soff < SB) ? rem - soff : SB) : 0;
        uint64x2_t acc;
        if (srem >= SB)     acc = ph_block<SW>(key.k + i * SW, p + off + soff);
        else if (srem > 0)  acc = ph_tail<SW>(key.k + i * SW, p + off + soff, srem);   // ends at p + len, len > SB >= 64
        else                acc = vdupq_n_u64(0);
        if (i + 1 < S) st = step(st, veorq_u64(acc, UY));
        else st = step(st, veorq_u64(acc, vsetq_lane_u64((uint64_t)len, key.Yhi, 0)));  // [a + len, b + y]: st = P_n
    }
    const uint64x2_t P = LAZY ? gf_reduce(st, rr) : st;
    return chain_v<K>(key.c, vaddq_u64(P, key.TIN));
}

template <int BLOCK_WORDS, int K, int S>
static __attribute__((noinline)) uint64_t hash_multi(const Key<BLOCK_WORDS, K, S>& key, const uint8_t* __restrict p, size_t len) {
    return vgetq_lane_u64(hash_multi_v(key, p, len), 0);
}

template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64_t hash(const Key<BLOCK_WORDS, K, S>& key, const void* data, size_t len) {
    const uint8_t* p = static_cast<const uint8_t*>(data);
    if (__builtin_expect(len > (size_t)Key<BLOCK_WORDS, K, S>::sub_bytes, 0)) return hash_multi(key, p, len);   // tail call
    return vgetq_lane_u64(hash_small_v(key, p, len), 0);
}

template <int BLOCK_WORDS = 32, int K = 5, int S = 1>
struct ChainHash {
    using key_t = Key<BLOCK_WORDS, K, S>;
    key_t key;
    ChainHash() = default;
    explicit ChainHash(uint64_t seed) : key(key_t::from_seed(seed)) {}
    void init(uint64_t seed) { key = key_t::from_seed(seed); }
    uint64_t operator()(const void* data, size_t len) const { return hash(key, data, len); }
};
using ChainHash256 = ChainHash<32, 5, 1>;
using ChainHash1k  = ChainHash<128, 5, 2>;

}  // namespace chainhash2

#endif  // CHAINHASH2_H
