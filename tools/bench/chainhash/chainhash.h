/* ***********************************************************************
 * ChainHash -- fast arm64 (NEON PMULL) implementation, header-only.
 *
 *   PH (8*BLOCK_WORDS-byte blocks, 2 independent PMULL accumulators (EOR3-fed);
 *       the last block is processed at PAIR granularity, see below)
 *     -> three-key injective GF(2^64) recurrence of sections/injective.tex
 *          P_0 = z,   P_i = a_i + (b_i + y)(P_{i-1} + u)
 *        with u, y, z three independent uniformly random field elements
 *     -> additive input twist  v = P_n + t_in  (INTEGER 64-bit addition,
 *        carries and all; t_in one more uniformly random key word; a fixed
 *        bijection of the finalizer input, see the finalizer comment)
 *     -> degree-5 finalizer with 5 uniformly random parameters c[0..5):
 *        the certified characteristic-2 circuit CIRCUITS[5] of
 *        website/js/char2.js (3 multiplications).  Its coefficient map
 *        c -> (lower coefficients of a monic degree-5 polynomial) is a
 *        bijection over EVERY field of characteristic 2: the decoder is
 *        unit pivots only, no square roots; see chain_v<5> below,
 *        verify5.py, exh5.c and T5 of test_chainhash.cpp.
 *
 * Blocks: n = max(1, ceil(len / (8*BLOCK_WORDS))).  Blocks 1..n-1 are full
 * (BLOCK_WORDS/2 pairs).  The last block holds r = len - (n-1)*8*BLOCK_WORDS
 * bytes and contributes only W' = ceil(r/16) pairs (W' = 0 for the empty
 * message), the final partial pair being zero-padded to 16 bytes; its PH
 * sum runs over exactly those W' pairs, using k[0..2W').  The recurrence,
 * a_n ^= len, the twist and the finalizer are unchanged.  The input is
 * never read outside [m, m + len): full 64-byte groups and whole 16-byte
 * pairs are loaded in place; the partial pair is loaded in place too --
 * as the 16 bytes ENDING at m + len realigned by a TBL byte shift when
 * len >= 16, and with overlapping lane loads + one TBL gather when the
 * whole message is shorter than 16 bytes (no stack copy, no memcpy).
 *
 * Sub-block split S (template parameter, default 1): every block is cut
 * into S contiguous sub-blocks of BLOCK_WORDS/S words (8*BLOCK_WORDS/S
 * bytes), and the PH sum of each sub-block is fed to the recurrence as its
 * own (a, b) pair, in order -- so a block costs S recurrence multiplications
 * and n*S steps are taken in total.  Sub-block i of a block uses the keys
 * k[i*BLOCK_WORDS/S ..).  In the last block the pairs of data belong to
 * whichever sub-block they fall in (the partial pair included); sub-blocks
 * beyond the data have an empty PH sum (a, b) = (0, 0) and still take their
 * recurrence step.  The length is XORed into the a of the LAST pair
 * (sub-block S-1 of block n).  S = 1 is exactly the function described
 * above.
 *
 * Shipped configurations:
 *   ChainHash<32, 5, 1>  (the defaults)  chainhash-256: 256-byte blocks,
 *                                        one recurrence step per block;
 *   ChainHash<128, 5, 2>                 chainhash-1k:  1 KB blocks, two
 *                                        sub-blocks (512 B) per block.
 * Key: BLOCK_WORDS + 9 uniformly random 64-bit words (k[0..BLOCK_WORDS),
 * u, y, z, c[0..5), t_in), i.e. 41 / 137 words for chainhash-256 /
 * chainhash-1k (17 for 64-byte blocks).  Beyond the PH layer a hash costs
 * n*S recurrence multiplications plus the 3 of the finalizer.  Guarantees
 * (appendix of the paper): two distinct messages of at most p (sub-)block
 * pairs collide with probability at most (p+2)/2^64, and the outputs are
 * 5-wise independent; the twist is a bijection of the finalizer input and
 * changes neither.
 *
 * Field: GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)  (reduction 27).
 * The multiply is the repo's 3-PMULL gf64_mult of
 * tools/bench/framework/multiplication_arm.h, but with the PMULL/PMULL2 forms
 * pinned by inline asm and every field element kept in lane 0 of a NEON
 * register: with the plain intrinsics clang emits DUP + PMULL2 per pair
 * product and moves the recurrence state through a general register,
 * which halves the throughput (37.8 -> 51.2 GB/s for 256-byte blocks).
 *
 * Evaluation schedule (the function is the one above; only the order of
 * the field operations is chosen for latency -- see the comments at
 * reduce_add, chain_v and hash):
 *   * every XOR that follows a multiply (finalizer constants, the a_i of a
 *     recurrence step) is folded into the product's reduction, where it
 *     overlaps the two PMULL2 folds and costs no latency;
 *   * a message of at most one sub-block (every key <= 256 B / 512 B for the
 *     shipped variants) takes a loop-free path in which the key-only parts
 *     of the recurrence are precomputed constants of the key: for S = 1
 *     P_1 = (a + len + y(z+u)) + b(z+u), one PMULL2 straight on the PH
 *     accumulator; for S = 2 the two steps (the second sub-block is empty)
 *     are the field identity P_2 = (len + yu + yy(z+u)) + a y + b y(z+u),
 *     two independent products and one reduction;
 *   * the key holds the vectors these paths need (setup()), so no value
 *     ever moves between general and SIMD registers inside hash();
 *   * the multi-step path (hash_multi_v) is out of line and reached by a
 *     tail call, so hash() is a leaf for every key that fits one sub-block;
 *     blocks 0..n-2 run without length logic on the state Q = P + u, the
 *     last block is peeled, and sub-blocks of <= 16 words (chain-bound)
 *     carry the recurrence state unreduced (step_lazy, 8-cycle chain).
 *
 * Compile: clang++ -O3 -std=c++17 -march=native+crypto   (Apple clang:
 * plain -march=native does NOT enable the PMULL 'aes' feature).
 *
 * NOTE: multiplication_arm.h pulls in framework/randomgen.h, which defines
 * non-inline globals; include this header from a single translation unit.
 *
 * Reference (bit-serial, no intrinsics): chainhash_ref.h.
 * *********************************************************************** */

#ifndef CHAINHASH_H
#define CHAINHASH_H

#include <arm_neon.h>
#include <cstddef>
#include <cstdint>
#include <cstring>
#include <iostream>  // framework/randomgen.h (pulled in below) uses cout without including it

#include "../framework/multiplication_arm.h"  // gf64_mult, from64, lower64

namespace chainhash {

/* splitmix64: deterministic key derivation from a 64-bit seed. */
static inline uint64_t splitmix64(uint64_t& state) {
    uint64_t z = (state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* GF(2^64) multiply: lower 64 bits of the repo's gf64_mult. */
static inline uint64_t gfmul(uint64_t a, uint64_t b) {
    return lower64(gf64_mult(from64(a), from64(b)));
}

/* PMULL on the low halves / PMULL2 on the high halves, as inline asm.  With
 * the intrinsics clang lowers a lane-0 x lane-1 product to DUP + PMULL2 and
 * routes the recurrence state through a general register (FMOV/DUP), which
 * doubles the SIMD op count of the block loop and adds ~10 cycles to every
 * dependent multiply.  The asm pins the instruction; the compiler still
 * schedules and allocates around it. */
#if defined(_MSC_VER) && !defined(__clang__)
static inline uint64x2_t pmull_lo(uint64x2_t a, uint64x2_t b) {   // no GNU asm on MSVC: intrinsics (slower lowering)
    return vreinterpretq_u64_p128(vmull_p64(vgetq_lane_p64(vreinterpretq_p64_u64(a), 0), vgetq_lane_p64(vreinterpretq_p64_u64(b), 0)));
}
static inline uint64x2_t pmull_hi(uint64x2_t a, uint64x2_t b) {
    return vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b)));
}
#define CHAINHASH_OPAQUE_PTR(p) ((void)0)
#else
static inline uint64x2_t pmull_lo(uint64x2_t a, uint64x2_t b) {   // lane0(a) * lane0(b) -> 128 bits
    uint64x2_t r; __asm__("pmull %0.1q, %1.1d, %2.1d" : "=w"(r) : "w"(a), "w"(b)); return r;
}
static inline uint64x2_t pmull_hi(uint64x2_t a, uint64x2_t b) {   // lane1(a) * lane1(b) -> 128 bits
    uint64x2_t r; __asm__("pmull2 %0.1q, %1.2d, %2.2d" : "=w"(r) : "w"(a), "w"(b)); return r;
}
/* Hides a pointer's provenance from the optimizer (see ld_word). */
#define CHAINHASH_OPAQUE_PTR(p) __asm__("" : "+r"(p))
#endif
static inline uint64x2_t xor3(uint64x2_t a, uint64x2_t b, uint64x2_t c) {
#if defined(__ARM_FEATURE_SHA3)
    return veor3q_u64(a, b, c);
#else
    return veorq_u64(veorq_u64(a, b), c);
#endif
}

/* The field arithmetic kept in NEON registers.  Every value lives in lane 0;
 * lane 1 of a state register is garbage that nothing reads (consumers take
 * lane 0, or the high half of a fresh 128-bit product).
 * Reduction: x^64 = 27 (= x^4 + x^3 + x + 1), applied twice via PMULL2. */
static inline uint64x2_t gf_rr() { return vdupq_n_u64(27); }
static inline uint64x2_t gf_reduce(uint64x2_t ab, uint64x2_t rr) {       // 128-bit product -> lane 0
    uint64x2_t xr = pmull_hi(ab, rr);
    uint64x2_t zr = pmull_hi(xr, rr);
    return xor3(ab, xr, zr);
}
/* reduce(ab) + add (lane 0).  The two PMULL2 folds depend only on lane 1 of
 * ab, so the EOR with `add` overlaps them and the addend costs no latency;
 * written out explicitly because clang cannot reassociate across the asm
 * PMULLs.  Every constant or data XOR that follows a multiply is folded in
 * this way (finalizer gates, recurrence steps). */
static inline uint64x2_t reduce_add(uint64x2_t ab, uint64x2_t add, uint64x2_t rr) {
    uint64x2_t xr = pmull_hi(ab, rr);
    uint64x2_t zr = pmull_hi(xr, rr);
    return xor3(veorq_u64(ab, add), xr, zr);
}
static inline uint64x2_t gfmul_v(uint64x2_t a, uint64x2_t b, uint64x2_t rr) {  // lane0(a) * lane0(b)
    return gf_reduce(pmull_lo(a, b), rr);
}
static inline uint64x2_t v64(uint64_t x) { return vcombine_u64(vcreate_u64(x), vcreate_u64(0)); }

/* Only the degree-5 finalizer is shipped. */
static constexpr bool valid_degree(int K) { return K == 5; }
/* Number of field multiplications of the degree-K chain. */
static constexpr int chain_mults(int K) { return K == 5 ? 3 : 0; }

/* ------------------------------------------------------------------ */
/* Key                                                                 */
/* ------------------------------------------------------------------ */
template <int BLOCK_WORDS = 32, int K = 5, int S = 1>
struct Key {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
                  "BLOCK_WORDS must be a positive multiple of 8*S "
                  "(2 accumulators, each fed two products per 64-byte group, per sub-block)");
    static_assert(valid_degree(K), "finalizer degree K must be 5 (the only shipped chain)");

    static constexpr int block_words = BLOCK_WORDS;
    static constexpr int block_bytes = 8 * BLOCK_WORDS;
    static constexpr int split = S;
    static constexpr int sub_words = BLOCK_WORDS / S;  // words per sub-block
    static constexpr int sub_bytes = 8 * sub_words;    // bytes per sub-block
    static constexpr int degree = K;
    /* random key material: k[], u, y, z, c[], t_in  (all uniform, unprocessed); independent of S.
     * BLOCK_WORDS + 3 + K + 1 = BLOCK_WORDS + 9 words. */
    static constexpr size_t random_key_bytes = 8 * (size_t)(BLOCK_WORDS + 3 + K + 1);

    alignas(16) uint64_t k[BLOCK_WORDS];  // PH level
    uint64_t u, y, z;                     // recurrence keys: P_0 = z, P_i = a_i + (b_i + y)(P_{i-1} + u)
    uint64_t c[K];                        // finalizer parameters
    uint64_t t_in;                        // input twist word: the finalizer is applied to P_n + t_in (integer add)

    /* Derived, message-independent values -- NOT key material, functions of
     * the words above (setup() fills them; from_seed calls it; a key filled
     * by hand must call setup() before hashing).  They keep hash() free of
     * general <-> SIMD register moves and hold the key-only parts of the
     * recurrence that the loop-free single-(sub-)block path uses. */
    uint64x2_t UY;    // [u, y]:           t = acc + UY = [a + u, b + y], the operand of a recurrence step
    uint64x2_t Yhi;   // [0, y]
    uint64x2_t ZUZU;  // [z + u, z + u]:   P_0 + u, as lane 0 (state) and as lane 1 (PMULL2 operand)
    uint64x2_t YYZU;  // [y, y(z + u)]:    multipliers of a and b in the fused double step (S = 2)
    uint64x2_t TIN;   // [t_in, 0]:        the twist, added to P_n by vaddq_u64
    uint64_t yzu;     // y (z + u):        single step   P_1 = (a + len + yzu) + b (z + u)
    uint64_t yyzu_yu; // y y (z + u) + y u: fused step   P_2 = (len + yyzu_yu) + a y + b yzu

    void setup() {
        const uint64_t zu = z ^ u;
        UY = vcombine_u64(vcreate_u64(u), vcreate_u64(y));
        Yhi = vcombine_u64(vcreate_u64(0), vcreate_u64(y));
        ZUZU = vdupq_n_u64(zu);
        yzu = gfmul(y, zu);
        YYZU = vcombine_u64(vcreate_u64(y), vcreate_u64(yzu));
        TIN = vcombine_u64(vcreate_u64(t_in), vcreate_u64(0));
        yyzu_yu = gfmul(y, yzu) ^ gfmul(y, u);
    }

    /* Derivation order from the seed: k[0..BLOCK_WORDS), u, y, z, c[0..K), t_in. */
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
/* PH level primitives                                                 */
/* ------------------------------------------------------------------ */

/* One 64-byte group (8 words = 4 pairs) at p with keys k[0..8), XORed into
 * two independent 128-bit accumulators (three-input XORs).  Byte loads: no alignment
 * assumption on p.  Reads exactly 64 bytes. */
static inline __attribute__((always_inline)) void ph_group(const uint64_t* __restrict k, const uint8_t* __restrict p, uint64x2_t& acc0,
                            uint64x2_t& acc1) {
    // (w[0]^k[0], w[1]^k[1]), ...
    uint64x2_t t0 = veorq_u64(vreinterpretq_u64_u8(vld1q_u8(p + 0)),  vld1q_u64(k + 0));
    uint64x2_t t1 = veorq_u64(vreinterpretq_u64_u8(vld1q_u8(p + 16)), vld1q_u64(k + 2));
    uint64x2_t t2 = veorq_u64(vreinterpretq_u64_u8(vld1q_u8(p + 32)), vld1q_u64(k + 4));
    uint64x2_t t3 = veorq_u64(vreinterpretq_u64_u8(vld1q_u8(p + 48)), vld1q_u64(k + 6));
    // e01 = (t0[1], t1[0]):  pmull(t0, e01) = t0[0] t0[1],  pmull2(e01, t1) = t1[0] t1[1]
    uint64x2_t e01 = vextq_u64(t0, t1, 1);
    uint64x2_t e23 = vextq_u64(t2, t3, 1);
    acc0 = xor3(acc0, pmull_lo(t0, e01), pmull_hi(e01, t1));   // pairs (0,1), (2,3)
    acc1 = xor3(acc1, pmull_lo(t2, e23), pmull_hi(e23, t3));   // pairs (4,5), (6,7)
}

/* Full (sub-)block (8*WORDS bytes at blk, WORDS a multiple of 8):
 *   XOR_{i < WORDS/2} clmul64(w[2i]^k[2i], w[2i+1]^k[2i+1]) */
template <int WORDS>
static inline __attribute__((always_inline)) uint64x2_t ph_block(const uint64_t* __restrict k, const uint8_t* __restrict blk) {
    static_assert(WORDS > 0 && WORDS % 8 == 0, "ph_block: WORDS must be a positive multiple of 8");
    uint64x2_t acc0 = vdupq_n_u64(0), acc1 = vdupq_n_u64(0);
    for (int i = 0; i < WORDS; i += 8) ph_group(k + i, blk + 8 * i, acc0, acc1);
    return veorq_u64(acc0, acc1);
}

/* A single pair (w0, w1) for the pair product: w = [w0, w1] and w1lo = [w1, *]
 * (the high word already in lane 0, so that clmul64(w0 ^ k0, w1 ^ k1) is
 * pmull_lo(w ^ k, w1lo ^ [k1, *]) with no EXT on the data path). */
struct PairW { uint64x2_t w, w1lo; };

/* 8 bytes at p into lane 0 (lane 1 zero), as a genuine second load: the
 * pointer is made opaque, otherwise clang merges it with an enclosing 16-byte
 * load and extracts the lane through a general register (~10 cycles). */
static inline __attribute__((always_inline)) uint64x2_t ld_word(const void* p) {
    const uint8_t* q = static_cast<const uint8_t*>(p);
    CHAINHASH_OPAQUE_PTR(q);
    return vreinterpretq_u64_u8(vcombine_u8(vld1_u8(q), vdup_n_u8(0)));
}
static inline __attribute__((always_inline)) uint64x2_t tbl(uint8x16_t v, uint8x16_t idx) {   // TBL: index >= 16 reads as 0
    return vreinterpretq_u64_u8(vqtbl1q_u8(v, idx));
}
static constexpr uint8_t kIota[16] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15};

/* The zero-padded partial pair made of the r (1..15) bytes ENDING at `end`,
 * read as the 16 bytes at end - 16 (which must be readable: the message has
 * >= 16 bytes ending there) and shifted right by 16 - r bytes with TBL --
 * indices >= 16 read as zero, which is exactly the padding.  Reads only
 * [end - 16, end).  The second TBL (shifted index) yields the high word in
 * lane 0 for the pair product; both TBLs run in parallel. */
static inline __attribute__((always_inline)) PairW load_partial_end(const uint8_t* end, size_t r) {
    uint8x16_t v = vld1q_u8(end - 16);
    uint8x16_t idx = vaddq_u8(vld1q_u8(kIota), vdupq_n_u8((uint8_t)(16 - r)));
    PairW pw;
    pw.w = tbl(v, idx);
    pw.w1lo = tbl(v, vextq_u8(idx, idx, 8));
    return pw;
}

/* Byte-gather tables for a message of r < 16 bytes: out[i] = t[r][i]-th byte
 * of the lane-loaded vector below (0xFF -> 0).  Layout of the loaded vector:
 *   8 <= r <= 15: lane .d[0] = bytes 0..7, lane .d[1] = bytes r-8..r-1
 *   4 <= r <=  7: lane .s[0] = bytes 0..3, lane .s[1] = bytes r-4..r-1
 *   1 <= r <=  3: bytes .b[0..2] = m[0], m[r/2], m[r-1]
 * (XXH3's three size classes: every load is in bounds and overlapping). */
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

/* The whole message: r (1..15) bytes at m, zero-padded to one pair.  Reads
 * only [m, m + r), all loads straight into SIMD lanes (no general register
 * on the data path); the gather index depends on r alone. */
static inline __attribute__((always_inline)) PairW load_small(const uint8_t* m, size_t r) {
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
    uint8x16_t idx = vld1q_u8(kGather.t[r]);
    PairW pw;
    pw.w = tbl(v, idx);
    pw.w1lo = tbl(v, vextq_u8(idx, idx, 8));
    return pw;
}

/* Pair product of a loaded pair with keys k[0..2):  clmul64(w0 ^ k0, w1 ^ k1). */
static inline __attribute__((always_inline)) uint64x2_t ph_pair_w(const uint64_t* __restrict k, PairW pw) {
    return pmull_lo(veorq_u64(pw.w, vld1q_u64(k)), veorq_u64(pw.w1lo, ld_word(k + 1)));
}
/* One whole pair (16 bytes) at p.  Reads exactly 16 bytes (as 16 + 8). */
static inline __attribute__((always_inline)) uint64x2_t ph_pair(const uint64_t* __restrict k, const uint8_t* __restrict p) {
    PairW pw;
    pw.w = vreinterpretq_u64_u8(vld1q_u8(p));
    pw.w1lo = ld_word(p + 8);
    return ph_pair_w(k, pw);
}

/* Partial last (sub-)block: rem < 8*WORDS bytes at p, W' = ceil(rem/16) pairs:
 *   XOR_{i < W'} clmul64(w[2i]^k[2i], w[2i+1]^k[2i+1]),
 * the final partial pair zero-padded to 16 bytes.  PRECONDITION: the 16
 * bytes ending at p + rem are readable (p + rem is the end of a message of
 * >= 16 bytes); then nothing outside [p + rem - 16, p + rem) U [p, p + rem)
 * is read: full 64-byte groups in place, whole 16-byte pairs in place, the
 * partial pair through load_partial_end. */
template <int WORDS>
static inline __attribute__((always_inline)) uint64x2_t ph_tail(const uint64_t* __restrict k, const uint8_t* __restrict p, size_t rem) {
    uint64x2_t acc0 = vdupq_n_u64(0), acc1 = vdupq_n_u64(0);
    size_t pos = 0;  // bytes consumed; word index = pos / 8
    for (; pos + 64 <= rem; pos += 64) ph_group(k + pos / 8, p + pos, acc0, acc1);
    uint64x2_t acc = veorq_u64(acc0, acc1);
    for (; pos + 16 <= rem; pos += 16) acc = veorq_u64(acc, ph_pair(k + pos / 8, p + pos));
    if (pos < rem) acc = veorq_u64(acc, ph_pair_w(k + pos / 8, load_partial_end(p + rem, rem - pos)));  // partial pair: 1..15 bytes
    return acc;
}

/* PH sum of a message of len <= 8*WORDS bytes that is the whole (sub-)block
 * (the single-(sub-)block path of hash): the block, a tail, one zero-padded
 * pair, or nothing.  Reads only [m, m + len). */
template <int WORDS>
static inline __attribute__((always_inline)) uint64x2_t ph_first(const uint64_t* __restrict k, const uint8_t* __restrict m, size_t len) {
    if (len >= 16) return len == 8 * (size_t)WORDS ? ph_block<WORDS>(k, m) : ph_tail<WORDS>(k, m, len);
    if (len > 0) return ph_pair_w(k, load_small(m, len));
    return vdupq_n_u64(0);
}

/* ------------------------------------------------------------------ */
/* Finalizer: the certified characteristic-2 degree-5 circuit           */
/* CIRCUITS[5] of website/js/char2.js, transcribed gate by gate         */
/* (x = the twisted input v, keys c[0..5)):                             */
/*     y = x x                                                          */
/*     z = (y + c0)(x + y + c1)                                         */
/*     t = (x + c2)(z + c3)                                             */
/*   out = t + c4                                                       */
/* 3 multiplications.  out is a MONIC polynomial of degree 5 in x whose */
/* lower coefficients are a bijection of (c0, .., c4) over EVERY field  */
/* of characteristic 2: with b = c0 + c1, d = c0 c1 the rows x^4 .. x^0 */
/* read 1 + c2, b + c2, c0 + c2 b, d + c3 + c0 c2, c4 + c2 (d + c3);    */
/* in the coordinates q = (c2, b, c0, c3, c4) every row is q_i + (a     */
/* polynomial in q_0..q_{i-1}), so the decoder is unit pivots only, no  */
/* square roots (verify5.py, exh5.c, T5 of test_chainhash.cpp).  Hence  */
/* the 5 parameters, drawn uniformly, give a uniformly random monic     */
/* quintic: collision probability exactly 2^-64 and 5-wise independent  */
/* outputs -- 5-wise is what linear probing provably needs (Pagh-Pagh-  */
/* Ruzic 2009; 4-wise is not enough, Patrascu-Thorup 2010).             */
/*                                                                      */
/* INPUT TWIST.  The circuit is applied to v = P + t_in with INTEGER    */
/* 64-bit addition (carries and all), t_in one more key word.  Reason:  */
/* over GF(2^64) squaring is GF(2)-linear, so v^e has GF(2)-degree      */
/* popcount(e) and any polynomial of degree <= 6 is only QUADRATIC in   */
/* the bits of v (7 = 111b is the first cubic exponent).  SMHasher3's   */
/* fixed-seed keysets (Zeroes, Sparse, Permutation, TwoBytes, Bitflip)  */
/* detect that: the untwisted degree-5 finalizer fails 22 of the 200    */
/* tests, although k-wise independence never asked for anything else.   */
/* Any bijection of the finalizer input keeps the 2^-64 bound and the   */
/* 5-wise independence exactly (distinct inputs stay distinct), and the */
/* carry chain of an integer add is not GF(2)-affine: bit i of v + t    */
/* has GF(2)-degree max(1, i-j0), j0 = t's lowest set bit; the          */
/* composite has GF(2)-degree 63 for all but 2^-64 of the keys c when   */
/* t_in is odd (appendix, proposition on the twisted finalizer).        */
/* Measured (M2 Pro, full SMHasher3): degree 5 + twist 200/200 at ~82 (~67 after (A7))  */
/* small-key cycles vs 95.7 for the former degree-7 circuit (4 mults);  */
/* degree 3 + twist still fails 17 of 200.  The twist is not a mixer:   */
/* it changes algebraic structure only, and its adequacy for a test     */
/* suite is empirical.  Do NOT add heuristic mixing here; raise the     */
/* degree or add provable structure instead.                            */
/* chain<5>(c, v) is the pure chain; finalize(key, v) adds t_in first.  */
/* ------------------------------------------------------------------ */
template <int K>
static inline __attribute__((always_inline)) uint64x2_t chain_v(const uint64_t* c, uint64x2_t v) {   // v in lane 0
    static_assert(valid_degree(K), "chain: only K = 5 is shipped");
    const uint64x2_t rr = gf_rr();
    const uint64x2_t C0 = v64(c[0]), C1 = v64(c[1]), C2 = v64(c[2]), C3 = v64(c[3]), C4 = v64(c[4]);
    /* Schedule: every addend is folded into the reduction of the product it
     * follows (reduce_add), and the square's two folds are shared by both
     * operands of the second gate, so the three multiplications are back to
     * back: 3 x (PMULL 3 + PMULL2 3 + PMULL2 3 + EOR3 2) = 33 cycles on M2. */
    uint64x2_t ab = pmull_lo(v, v);                                            // x x, unreduced
    uint64x2_t xr = pmull_hi(ab, rr), zr = pmull_hi(xr, rr);
    uint64x2_t yc0  = xor3(veorq_u64(ab, C0), xr, zr);                         // y + c0
    uint64x2_t xyc1 = xor3(veorq_u64(ab, veorq_u64(v, C1)), xr, zr);           // x + y + c1
    uint64x2_t zc3  = reduce_add(pmull_lo(yc0, xyc1), C3, rr);                 // z + c3 = (y + c0)(x + y + c1) + c3
    return reduce_add(pmull_lo(veorq_u64(v, C2), zc3), C4, rr);                // (x + c2)(z + c3) + c4
}

/* The input twist on a lane-0 value: lane 0 + t_in as a 64-bit integer.
 * vaddq_u64 adds per lane (no carry across lanes); lane 1 gets + 0 and stays
 * the garbage it was -- every consumer of the twisted value in chain_v is a
 * pmull_lo (lane 0 only) or a lane-0 extract, so lane 1 is never read. */
static inline __attribute__((always_inline)) uint64x2_t twist_v(uint64x2_t v, uint64_t t_in) {
    return vaddq_u64(v, v64(t_in));
}

template <int K>
static inline __attribute__((always_inline)) uint64_t chain(const uint64_t* c, uint64_t v) {
    return vgetq_lane_u64(chain_v<K>(c, v64(v)), 0);
}

/* finalize(key, v) = chain_K(c, v + t_in), the twist as an integer add. */
template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64_t finalize(const Key<BLOCK_WORDS, K, S>& key, uint64_t v) {
    return vgetq_lane_u64(chain_v<K>(key.c, twist_v(v64(v), key.t_in)), 0);
}

/* ------------------------------------------------------------------ */
/* Recurrence step                                                     */
/* ------------------------------------------------------------------ */
/* On the state Q = P + u:  Q_i = (a_i + u) + (b_i + y) Q_{i-1}, i.e.
 *   step_q(Q, t) = t[0] + t[1] Q   with t = [a + u, b + y] = acc + UY;
 * the very last step takes t = [a + len, b + y] (no u) and then yields P_n
 * itself.  The EXT that moves b + y to lane 0 is on the data side, off the
 * loop-carried chain PMULL 3 + PMULL2 3 + PMULL2 3 + EOR3 2 = 11 cycles. */
static inline __attribute__((always_inline)) uint64x2_t step_q(uint64x2_t Q, uint64x2_t t, uint64x2_t rr) {
    return reduce_add(pmull_lo(vextq_u64(t, t, 1), Q), t, rr);
}

/* The same step on an UNREDUCED state: V = V[0] + V[1] x^64 (a 128-bit
 * polynomial) represents the field element V mod f.  A state is only ever
 * multiplied by a 64-bit factor, and reduction is GF(2)-linear, so it can be
 * deferred to the end of the multi-step path: with bb = b + y in both lanes
 *   bb V = pmull(bb, V) + x^64 pmull2(bb, V) = p + [0, q0] + q1 x^128,
 *   x^128 = 27^2 = x^8 + x^6 + x^2 + 1 (0x145) mod f,
 *   V' = p + [a + u, 0] + [0, q0] + pmull2(q, [*, 0x145])       (degree < 128).
 * Loop-carried chain PMULL 3 + PMULL2 3 + EOR3 2 = 8 cycles instead of 11,
 * for two more SIMD ops per step; gf_reduce(V) at the end (8 cycles, once). */
static inline uint64x2_t gf_r2() { return vdupq_n_u64(0x145); }
static inline __attribute__((always_inline)) uint64x2_t step_lazy(uint64x2_t V, uint64x2_t t, uint64x2_t r2) {
    const uint64x2_t bb = vdupq_laneq_u64(t, 1);                              // [b + y, b + y]
    const uint64x2_t au = vcombine_u64(vget_low_u64(t), vdup_n_u64(0));      // [a + u, 0]
    const uint64x2_t p = pmull_lo(bb, V);                                     // (b + y) V[0]
    const uint64x2_t q = pmull_hi(bb, V);                                     // (b + y) V[1] = q0 + q1 x^64
    return xor3(veorq_u64(p, au), vextq_u64(vdupq_n_u64(0), q, 1), pmull_hi(q, r2));   // p + au + [0, q0] + q1 x^128
}

/* ------------------------------------------------------------------ */
/* HASH(m, len)                                                        */
/* ------------------------------------------------------------------ */
/* Two evaluation paths, each returning the finished hash in lane 0 of a
 * NEON register (lane 1 garbage, never read):
 *   hash_small_v  len <= sub_bytes: every key <= 256 B / 512 B for the
 *                 shipped variants.  All data sits in sub-block 0 of the
 *                 only block; sub-blocks 1..S-1 are empty.  No loop, no
 *                 length bookkeeping: the key-only parts of the S
 *                 recurrence steps are constants of the key (setup()).
 *   hash_multi_v  len > sub_bytes.  Blocks 0..n-2 are full and need no
 *                 length logic (state Q = P + u, step_q); the last block is
 *                 peeled and does the sub-block selects once, its final
 *                 step taking [a + len, b + y] and yielding P_n directly.
 * hash() below puts the multi-step path out of line and reaches it by a
 * tail call, so that the small-key path it inlines is a leaf: no frame, no
 * callee-saved spills, no stack instruction on any key that fits one
 * sub-block. */
template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64x2_t hash_small_v(const Key<BLOCK_WORDS, K, S>& key, const uint8_t* __restrict p, size_t len) {
    using key_t = Key<BLOCK_WORDS, K, S>;
    constexpr int SW = key_t::sub_words;            // words per sub-block
    const uint64x2_t rr = gf_rr();
    const uint64x2_t acc = ph_first<SW>(key.k, p, len);   // [a, b]
    uint64x2_t P;  // P_S, lane 0
    if constexpr (S == 1) {
        // P_1 = a + len + (b + y)(z + u) = (a + len + y(z+u)) + b (z+u): one PMULL2 on the accumulator
        P = reduce_add(pmull_hi(acc, key.ZUZU), veorq_u64(acc, v64((uint64_t)len ^ key.yzu)), rr);
    } else if constexpr (S == 2) {
        // P_2 = len + y (P_1 + u) = (len + yu + yy(z+u)) + a y + b y(z+u): two independent products, one reduction
        uint64x2_t pr = veorq_u64(pmull_lo(acc, key.YYZU), pmull_hi(acc, key.YYZU));
        P = reduce_add(pr, v64((uint64_t)len ^ key.yyzu_yu), rr);
    } else {
        uint64x2_t Q = step_q(key.ZUZU, veorq_u64(acc, key.UY), rr);        // sub-block 0
        for (int i = 1; i + 1 < S; i++) Q = step_q(Q, key.UY, rr);         // empty sub-blocks: (a, b) = (0, 0)
        P = step_q(Q, vsetq_lane_u64((uint64_t)len, key.Yhi, 0), rr);      // last, empty: a + len = len
    }
    return chain_v<K>(key.c, vaddq_u64(P, key.TIN));   // chain_K(c, P_S + t_in)
}

template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64x2_t hash_multi_v(const Key<BLOCK_WORDS, K, S>& key, const uint8_t* __restrict p, size_t len) {
    using key_t = Key<BLOCK_WORDS, K, S>;
    constexpr size_t BB = (size_t)key_t::block_bytes;
    constexpr size_t SB = (size_t)key_t::sub_bytes;
    constexpr int SW = key_t::sub_words;
    /* Recurrence state.  A sub-block of SW words costs ~1.5 SW + 7 SIMD ops
     * against a loop-carried chain of 11 cycles (step_q), so for SW <= 16
     * (128-byte sub-blocks) the loop is chain-bound and runs on the unreduced
     * state of step_lazy (8-cycle chain: +36% at 16 KB for 64-byte blocks);
     * the shipped 256 B / 512 B sub-blocks are bound by SIMD issue (56 ops per
     * 256 B block) and only pay the lazy form's two extra ops (-2% measured),
     * so they keep the direct step.  Same function either way. */
    constexpr bool LAZY = (SW <= 16);
    const uint64x2_t rr = gf_rr(), r2 = gf_r2();
    auto step = [&](uint64x2_t st, uint64x2_t t) {
        if constexpr (LAZY) return step_lazy(st, t, r2);
        else                return step_q(st, t, rr);
    };
    const size_t n = (len + BB - 1) / BB;  // >= 1 blocks (len > SB > 0)
    const uint64x2_t UY = key.UY;
    // st_0 = Q_0 = P_0 + u = z + u: lane 0 for step_q, the exact 128-bit polynomial [z + u, 0] for step_lazy
    uint64x2_t st = LAZY ? vcombine_u64(vget_low_u64(key.ZUZU), vdup_n_u64(0)) : key.ZUZU;
    for (size_t j = 0; j + 1 < n; j++) {
        const uint8_t* blk = p + j * BB;
        for (int i = 0; i < S; i++) st = step(st, veorq_u64(ph_block<SW>(key.k + i * SW, blk + i * SB), UY));
    }
    const size_t off = (n - 1) * BB;
    const size_t rem = len - off;  // bytes of input in the last block: 1..BB
    for (int i = 0; i < S; i++) {
        const size_t soff = (size_t)i * SB;                                       // sub-block start within the block
        const size_t srem = (rem > soff) ? ((rem - soff < SB) ? rem - soff : SB) : 0;  // bytes of input in this sub-block
        uint64x2_t acc;
        if (srem >= SB)     acc = ph_block<SW>(key.k + i * SW, p + off + soff);         // full sub-block
        else if (srem > 0)  acc = ph_tail<SW>(key.k + i * SW, p + off + soff, srem);    // W' = ceil(srem/16) pairs; len > SB >= 16
        else                acc = vdupq_n_u64(0);                                      // no data: empty PH sum
        if (i + 1 < S) st = step(st, veorq_u64(acc, UY));
        else st = step(st, veorq_u64(acc, vsetq_lane_u64((uint64_t)len, key.Yhi, 0)));  // [a + len, b + y] (no u): st = P_n
    }
    const uint64x2_t P = LAZY ? gf_reduce(st, rr) : st;   // P_n, lane 0
    return chain_v<K>(key.c, vaddq_u64(P, key.TIN));       // chain_K(c, P_n + t_in)
}

/* The out-of-line multi-step path. */
template <int BLOCK_WORDS, int K, int S>
static __attribute__((noinline)) uint64_t hash_multi(const Key<BLOCK_WORDS, K, S>& key, const uint8_t* __restrict p, size_t len) {
    return vgetq_lane_u64(hash_multi_v(key, p, len), 0);
}

/* hash(key, m, len): the 64-bit hash value.  (Storing lane 0 straight from
 * the NEON register instead of returning through a general register was
 * measured neutral on M2 -- 72.3 vs 72.6 cycles in the SMHasher3-style
 * store-and-reload loop -- so there is no separate output-buffer API.) */
template <int BLOCK_WORDS, int K, int S>
static inline __attribute__((always_inline)) uint64_t hash(const Key<BLOCK_WORDS, K, S>& key, const void* data, size_t len) {
    const uint8_t* p = static_cast<const uint8_t*>(data);
    if (__builtin_expect(len > (size_t)Key<BLOCK_WORDS, K, S>::sub_bytes, 0)) return hash_multi(key, p, len);   // tail call
    return vgetq_lane_u64(hash_small_v(key, p, len), 0);
}

/* Convenience functor.  Defaults = chainhash-256 (see the header comment):
 * 256-byte blocks, degree-5 finalizer behind the additive twist, S = 1.
 * ChainHash<128, 5, 2> is the 1 KB configuration (chainhash-1k). */
template <int BLOCK_WORDS = 32, int K = 5, int S = 1>
struct ChainHash {
    using key_t = Key<BLOCK_WORDS, K, S>;
    key_t key;
    ChainHash() = default;
    explicit ChainHash(uint64_t seed) : key(key_t::from_seed(seed)) {}
    void init(uint64_t seed) { key = key_t::from_seed(seed); }
    uint64_t operator()(const void* data, size_t len) const { return hash(key, data, len); }
};

/* The SMHasher3 registrations (hashes/chainhash.cpp of the SMHasher3 fork). */
using ChainHash256 = ChainHash<32, 5, 1>;   // chainhash-256  (the default)
using ChainHash1k  = ChainHash<128, 5, 2>;  // chainhash-1k

}  // namespace chainhash

#endif  // CHAINHASH_H
