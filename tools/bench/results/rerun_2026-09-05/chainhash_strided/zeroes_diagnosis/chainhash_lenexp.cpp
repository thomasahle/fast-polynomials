/*
 * ChainHash
 * Copyright (C) 2026  Thomas Dybdahl Ahle
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */
/*
 * ChainHash: a 64-bit hash over GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)
 * built from three layers, all carry-less:
 *
 *   1. PH / carry-less NH over 8*BLOCK_WORDS-byte blocks with the STRIDED
 *      word pairing.  The message is read as little-endian 64-bit words
 *      w[] and cut into 32-byte groups of four words; the words
 *      (w[4g], w[4g+1], w[4g+2], w[4g+3]) of group g form the two pairs
 *      (w[4g], w[4g+2]) and (w[4g+1], w[4g+3]), every word XORed with the
 *      key word of its OWN position.  Block j gives
 *        (a_j, b_j) = (lo64, hi64) of
 *           XOR_g [ clmul64(w[4g]   ^ k[4g],   w[4g+2] ^ k[4g+2])
 *                 ^ clmul64(w[4g+1] ^ k[4g+1], w[4g+3] ^ k[4g+3]) ].
 *      n = max(1, ceil(len / (8*BLOCK_WORDS))) blocks; blocks 1..n-1 are
 *      full, the last one holds r bytes and only G' = ceil(r/32) groups
 *      = 2G' pairs (its final partial group is zero-padded to 32 bytes;
 *      a message of 1..16 bytes has two pairs, the second being the key
 *      constant (0 ^ k[1])(0 ^ k[3]) when the message has at most 8
 *      bytes).  The byte length is XORed into a_n.
 *      Why strided: a 16-byte vector load holds two ADJACENT words, and
 *      the AArch64 PMULL / PMULL2 pair multiplies lane 0 x lane 0 / lane
 *      1 x lane 1 of two registers -- so the strided pairing takes both
 *      multiplicands straight from the two loads of a group (no EXT on
 *      the data path: 10 SIMD ops per 64 bytes instead of 12, +13% bulk
 *      throughput on Apple M2), while x86 PCLMULQDQ selects either half
 *      of either operand by its immediate and is neutral.  The two
 *      pairings are the same function up to a fixed permutation of the
 *      word positions applied to data and key alike, so the XOR-
 *      universality of PH (and the collision bound below) is unchanged.
 *      Sub-block split S (template parameter; S = 1 is the above): every
 *      block is cut into S contiguous sub-blocks of BLOCK_WORDS/S words
 *      (a whole number of groups), each with its own PH sum (a, b) over
 *      the groups of data it holds (sub-blocks beyond the data have
 *      (a, b) = (0, 0)), fed to the recurrence in order; the length goes
 *      into the a of the LAST pair.
 *   2. The three-key injective GF(2^64) recurrence over the (sub-)block
 *      digests, with u, y, z three independent uniform field elements:
 *        P_0 = z,   P_j = a_j + (b_j + y) * (P_{j-1} + u).
 *   3. An additive input twist followed by a degree-5 finalizer with 5
 *      uniformly random parameters c[]:
 *        v = P + t_in   (INTEGER 64-bit addition, t_in one more key word),
 *        h = f_c(v)     with f_c the certified characteristic-2 degree-5
 *      circuit (website/js/char2.js CIRCUITS[5] of the paper's repository),
 *      3 field multiplications.  f_c is a monic degree-5 polynomial in v
 *      whose lower coefficients are a bijection of c[] over every field of
 *      characteristic 2 (explicit decoder, unit pivots only), so the
 *      finalizer is a uniformly random monic quintic: collision probability
 *      exactly 2^-64 and 5-wise independent outputs.  The twist is a fixed
 *      bijection of the finalizer input and changes neither guarantee; it
 *      is there because over GF(2^64) every polynomial of degree <= 6 is
 *      only quadratic in the bits of its input (v^e has GF(2)-degree
 *      popcount(e)), which SMHasher3's fixed-seed window tests detect,
 *      while an integer add's carry chain is not GF(2)-affine.  See the
 *      finalizer comment below.
 *
 * The key (k[0..BLOCK_WORDS), u, y, z, c[0..5), t_in) is derived from the
 * 64-bit seed with splitmix64 in that order (BLOCK_WORDS + 9 words).  It
 * does not depend on S, and the pairing changes neither its size nor its
 * derivation.
 *
 * Shipped configurations:
 *   chainhash-256:  BLOCK_WORDS = 32  (256-byte blocks), S = 1
 *   chainhash-1k:   BLOCK_WORDS = 128 (1 KB blocks),     S = 2
 *
 * Reference implementation and analysis: T. D. Ahle, "Fast Evaluation of
 * Polynomials with Rational Preprocessing", bench/chainhash/chainhash_ref.h.
 *
 * Three carry-less multiply backends are provided and selected at compile
 * time: x86-64 PCLMULQDQ, AArch64 PMULL, and a portable bit-serial
 * fallback.  All three compute the identical function.  The portable
 * backend evaluates the definition above literally (one recurrence step
 * per sub-block, see ChainHash at the end); the two SIMD backends share a
 * register-resident evaluation that reorders the field operations for
 * latency without changing the function (same verification codes):
 *   * every XOR that follows a multiply (finalizer constants, the a of a
 *     recurrence step) is folded into that product's reduction, where it
 *     overlaps the reduction's two folds;
 *   * a message of at most one sub-block (every key <= 256 B / 512 B for
 *     the shipped variants) takes a loop-free path in which the key-only
 *     parts of the recurrence are constants of the key (chainhash_key_setup):
 *     for S = 1  P_1 = (a + len + y(z+u)) + b(z+u), one product on the PH
 *     accumulator; for S = 2 (the second sub-block is empty) the identity
 *     P_2 = (len + yu + yy(z+u)) + a y + b y(z+u), two independent products
 *     and one reduction; a message of at most 8 bytes folds its key-only
 *     second pair into those constants as well (yzu8 / yyzu_yu8), and one
 *     of 9..16 bytes reduces its two pair products separately, so that
 *     the step's latency is that of a single pair;
 *   * the key holds the word pairs those paths need, loaded straight into
 *     vector registers, so no value moves between general and vector
 *     registers inside the hash function;
 *   * the multi-block path is out of line and reached by a tail call, so
 *     the hash function is a leaf for every key that fits one sub-block;
 *     blocks 0..n-2 run without length logic on the state Q = P + u, and the
 *     last block is peeled;
 *   * on AArch64 the partial group of the last block is loaded in place
 *     with TBL byte shifts (no stack copy); the input is never read
 *     outside [in, in + len).
 */
#include "Platform.h"
#include "Hashlib.h"

//------------------------------------------------------------
// Backend selection.
//
//   CHAINHASH_IMPL_X86       x86-64 PCLMULQDQ (_mm_clmulepi64_si128)
//   CHAINHASH_IMPL_ARM       AArch64 PMULL.  Only used when the compiler
//                            advertises the AES/crypto feature
//                            (__ARM_FEATURE_AES / __ARM_FEATURE_CRYPTO) or
//                            SMHasher3 detected it (HAVE_ARM_AES).
//   CHAINHASH_IMPL_PORTABLE  bit-serial fallback; always compiles.
//
// Define CHAINHASH_FORCE_PORTABLE to select the fallback regardless of
// what the platform supports (used for cross-checking the backends).
#if !defined(CHAINHASH_FORCE_PORTABLE) && defined(HAVE_X86_64_CLMUL)
  #include "Intrinsics.h"
  #define CHAINHASH_IMPL_X86 1
  #define CHAINHASH_IMPL_STR "hwclmul"
#elif !defined(CHAINHASH_FORCE_PORTABLE) &&                       \
      (defined(__aarch64__) || defined(_M_ARM64)) &&               \
      (defined(__ARM_FEATURE_AES) || defined(__ARM_FEATURE_CRYPTO) || defined(HAVE_ARM_AES))
  #if defined(HAVE_ARM_NEON)
    #include "Intrinsics.h"
  #else
    #include <arm_neon.h>
  #endif
  #define CHAINHASH_IMPL_ARM 1
  #define CHAINHASH_IMPL_STR "hwpmull"
#else
  #define CHAINHASH_IMPL_PORTABLE 1
  #define CHAINHASH_IMPL_STR "portable"
#endif

//------------------------------------------------------------
// Key material.  k[] is the PH key; u, y, z the recurrence keys
// (P_0 = z, P_j = a_j + (b_j + y)(P_{j-1} + u)); c[] the finalizer
// parameters; t_in the input twist word.
//
// The remaining members are derived, message-independent values -- NOT key
// material, functions of the words above, filled by chainhash_key_setup().
// The SIMD backends load them straight into vector registers (so nothing
// moves between general and vector registers inside the hash function) and
// they hold the key-only parts of the recurrence that the loop-free
// single-sub-block path uses.  Word pairs are stored as (lane 0, lane 1).

template <int BLOCK_WORDS, int K>
struct chainhash_key {
    alignas(16) uint64_t k[BLOCK_WORDS];
    uint64_t u, y, z;
    uint64_t c[K];
    uint64_t t_in;
    // derived (chainhash_key_setup)
    alignas(16) uint64_t uy[2];    // [u, y]:            t = acc ^ uy = [a + u, b + y], the operand of a recurrence step
    alignas(16) uint64_t yhi[2];   // [0, y]
    alignas(16) uint64_t zuzu[2];  // [z + u, z + u]:    P_0 + u, as lane 0 (state) and as lane 1 (high-half multiplicand)
    alignas(16) uint64_t yyzu[2];  // [y, y (z + u)]:    multipliers of a and b in the fused double step (S = 2)
    alignas(16) uint64_t tin[2];   // [t_in, 0]:         the twist, added to P_n as a 64-bit integer
    uint64_t yzu;                  // y (z + u):         single step   P_1 = (a + len + yzu) + b (z + u)
    uint64_t yyzu_yu;              // y y (z + u) + y u: fused step    P_2 = (len + yyzu_yu) + a y + b y (z + u)
    // The same two constants with the key-only second pair (0 ^ k[1])(0 ^ k[3])
    // of a 1..8-byte message folded in ([ac, bc] = clmul64(k[1], k[3])):
    // a = a' + ac, b = b' + bc where (a', b') is the product of the first pair.
    uint64_t yzu8;                 // yzu + ac + bc (z + u)
    uint64_t yyzu_yu8;             // yyzu_yu + ac y + bc y (z + u)
};

// EXPERIMENT (lane E, 2026-09-05): injective length encoding len -> len * odd
// constant mod 2^64, so that the length term of the last pair is not confined
// to the low bits of the recurrence value (Zeroes delta-distribution test).
static FORCE_INLINE uint64_t chainhash_len_enc( size_t len ) {
    return ((uint64_t)len) * UINT64_C(0x9E3779B97F4A7C15);
}

static FORCE_INLINE uint64_t chainhash_splitmix64( uint64_t & state ) {
    uint64_t z = (state += UINT64_C(0x9E3779B97F4A7C15));

    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}

//------------------------------------------------------------
// Backend primitives.  Every backend provides
//
//   chainhash_v128                 a 128-bit two-word vector / accumulator
//   chainhash_v_zero()             all-zero vector
//   chainhash_v_xor(a, b), chainhash_v_xor3(a, b, c)
//   chainhash_v_load2(p)           the word pair p[0..2) (key material or
//        a derived pair of the key) as the vector [p[0], p[1]]
//   chainhash_v_loadwords<bswap>(p)
//        the 16 bytes at p as [w0, w1], w0, w1 the little-endian 64-bit
//        words at p, p + 8 (GET_U64<bswap>, so big-endian builds agree)
//   chainhash_v_load_end_padded<bswap>(end, r)
//        the r (1..16) bytes ENDING at end, zero-padded to 16 bytes, as
//        [w0, w1].  PRECONDITION on the PMULL backend: the 16 bytes ending
//        at end are readable (end is the end of a message of >= 16 bytes);
//        it then reads [end - 16, end) and nothing else
//   chainhash_v_load_small<bswap>(m, r)
//        a whole message of r (1..15) bytes at m, zero-padded, as [w0, w1];
//        reads only [m, m + r)
//   chainhash_v_clmul_ll(a, b)     lane0(a) * lane0(b), the unreduced
//        128-bit carry-less product
//   chainhash_v_clmul_hh(a, b)     lane1(a) * lane1(b), unreduced
//   chainhash_v_lo(v), chainhash_v_hi(v)
//        lane 0 / lane 1 as a uint64_t (key setup only)
//   chainhash_gf                   a field element of GF(2^64) held in a
//        register: lane 0 of a vector on the SIMD backends (lane 1 is
//        garbage that nothing reads), a uint64_t on the portable one.
//        Keeping the recurrence and the finalizer in vector registers
//        avoids a GPR<->SIMD round trip per multiply.
//   chainhash_gf_from(x) / chainhash_gf_to(v)
//        x in lane 0 / lane 0 out
//   chainhash_gf_xor(a, b), chainhash_gf_mul(a, b)
//        a * b in GF(2^64), reduction constant 27
//   chainhash_gf_mulraw(a, b)      lane0(a) * lane0(b), the unreduced
//        128-bit product (a chainhash_v128; = chainhash_v_clmul_ll)
//   chainhash_gf_reduce_add(ab, add)
//        reduce(ab) + add, the addend folded into the reduction (its XOR
//        overlaps the two folds, which depend only on the high half of ab)
//   chainhash_gf_reduce_add2(ab, add0, add1, o0, o1)
//        o0 = reduce(ab) + add0, o1 = reduce(ab) + add1, the folds shared
//   chainhash_gf_reduce2_add(ab1, ab2, add)
//        reduce(ab1 + ab2) + add with the two products folded SEPARATELY,
//        so that neither waits for their sum (the 9..16-byte small path)
//   chainhash_gf_addint(a, x)
//        the input twist: lane 0 of a plus x as a 64-bit INTEGER (carries
//        and all; lane 1 gets + 0 and stays unread garbage)
//
// The SIMD backends additionally provide, for the register-resident
// evaluation (chainhash_small_v / chainhash_multi below):
//
//   chainhash_v_add64(a, b)        per-lane 64-bit integer addition
//   chainhash_v_clmul_hl(a, b)     lane1(a) * lane0(b), unreduced
//
// The portable backend instead provides chainhash_gf_hi(x) (x in lane 1)
// and chainhash_recur(P, acc, Yhi, U), one literal recurrence step
// a + (b + y)(P + u) with (a, b) the two halves of acc.
//
// The pairing itself lives in chainhash_ph_group32 below, the same code on
// every backend: with r0 = [w0, w1] and r1 = [w2, w3] the two loads of a
// 32-byte group, t0 = r0 ^ [k0, k1], t1 = r1 ^ [k2, k3], the group's
// contribution is clmul_ll(t0, t1) ^ clmul_hh(t0, t1) -- on x86 two
// PCLMULQDQ with immediates 0x00 / 0x11, on AArch64 PMULL / PMULL2 on the
// two loaded registers, on the portable backend index arithmetic over the
// four words.

#if defined(CHAINHASH_IMPL_X86)

typedef __m128i chainhash_v128;

static FORCE_INLINE chainhash_v128 chainhash_v_zero( void ) {
    return _mm_setzero_si128();
}

static FORCE_INLINE chainhash_v128 chainhash_v_xor( chainhash_v128 a, chainhash_v128 b ) {
    return _mm_xor_si128(a, b);
}

static FORCE_INLINE chainhash_v128 chainhash_v_xor3( chainhash_v128 a, chainhash_v128 b, chainhash_v128 c ) {
    return _mm_xor_si128(_mm_xor_si128(a, b), c);
}

static FORCE_INLINE chainhash_v128 chainhash_v_load2( const uint64_t * p ) {
    return _mm_loadu_si128((const __m128i *)p);
}

static FORCE_INLINE chainhash_v128 chainhash_v_add64( chainhash_v128 a, chainhash_v128 b ) {
    return _mm_add_epi64(a, b);
}

template <bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_v_loadwords( const uint8_t * p ) {
    __m128i w = _mm_loadu_si128((const __m128i *)p);

    if (bswap) { w = mm_bswap64(w); }
    return w;
}

// The immediate of PCLMULQDQ selects the halves: bit 0 the half of the
// first operand, bit 4 the half of the second.
static FORCE_INLINE chainhash_v128 chainhash_v_clmul_ll( chainhash_v128 a, chainhash_v128 b ) {
    return _mm_clmulepi64_si128(a, b, 0x00);
}

static FORCE_INLINE chainhash_v128 chainhash_v_clmul_hh( chainhash_v128 a, chainhash_v128 b ) {
    return _mm_clmulepi64_si128(a, b, 0x11);
}

static FORCE_INLINE chainhash_v128 chainhash_v_clmul_hl( chainhash_v128 a, chainhash_v128 b ) {
    return _mm_clmulepi64_si128(a, b, 0x01);
}

static FORCE_INLINE uint64_t chainhash_v_lo( chainhash_v128 v ) {
    return (uint64_t)_mm_cvtsi128_si64(v);
}

static FORCE_INLINE uint64_t chainhash_v_hi( chainhash_v128 v ) {
    return (uint64_t)_mm_cvtsi128_si64(_mm_unpackhi_epi64(v, v));
}

// Field elements in lane 0 of an XMM register.  Reduction: one CLMUL for
// the product, two for the reduction (ab = x 2^64 + y;  xr = x*27 = z 2^64
// + t;  result = y ^ t ^ z*27); the immediate selects the high half, so no
// lane moves are needed.
typedef __m128i chainhash_gf;

static FORCE_INLINE chainhash_gf chainhash_gf_from( uint64_t x ) {
    return _mm_cvtsi64_si128((long long)x);
}

static FORCE_INLINE uint64_t chainhash_gf_to( chainhash_gf v ) {
    return (uint64_t)_mm_cvtsi128_si64(v);
}

static FORCE_INLINE chainhash_gf chainhash_gf_xor( chainhash_gf a, chainhash_gf b ) {
    return _mm_xor_si128(a, b);
}

// Twist: integer 64-bit addition of x to lane 0 (per-lane add, no carry
// across lanes; lane 1 + 0).
static FORCE_INLINE chainhash_gf chainhash_gf_addint( chainhash_gf a, uint64_t x ) {
    return _mm_add_epi64(a, _mm_cvtsi64_si128((long long)x));
}

static FORCE_INLINE chainhash_v128 chainhash_gf_mulraw( chainhash_gf a, chainhash_gf b ) {
    return _mm_clmulepi64_si128(a, b, 0x00);
}

static FORCE_INLINE chainhash_gf chainhash_gf_reduce_add( __m128i ab, chainhash_gf add ) {
    const __m128i r  = _mm_set_epi64x(0, 27);
    const __m128i xr = _mm_clmulepi64_si128(ab, r, 0x01);
    const __m128i zr = _mm_clmulepi64_si128(xr, r, 0x01);

    return _mm_xor_si128(_mm_xor_si128(_mm_xor_si128(ab, add), xr), zr);
}

static FORCE_INLINE void chainhash_gf_reduce_add2( __m128i ab, chainhash_gf add0, chainhash_gf add1,
        chainhash_gf & o0, chainhash_gf & o1 ) {
    const __m128i r  = _mm_set_epi64x(0, 27);
    const __m128i xr = _mm_clmulepi64_si128(ab, r, 0x01);
    const __m128i zr = _mm_clmulepi64_si128(xr, r, 0x01);
    const __m128i xz = _mm_xor_si128(xr, zr);

    o0 = _mm_xor_si128(_mm_xor_si128(ab, add0), xz);
    o1 = _mm_xor_si128(_mm_xor_si128(ab, add1), xz);
}

static FORCE_INLINE chainhash_gf chainhash_gf_reduce2_add( __m128i ab1, __m128i ab2, chainhash_gf add ) {
    const __m128i r   = _mm_set_epi64x(0, 27);
    const __m128i xr1 = _mm_clmulepi64_si128(ab1, r, 0x01);
    const __m128i xr2 = _mm_clmulepi64_si128(ab2, r, 0x01);
    const __m128i zr1 = _mm_clmulepi64_si128(xr1, r, 0x01);
    const __m128i zr2 = _mm_clmulepi64_si128(xr2, r, 0x01);
    const __m128i e   = _mm_xor_si128(_mm_xor_si128(_mm_xor_si128(ab1, ab2), add), _mm_xor_si128(xr1, xr2));

    return _mm_xor_si128(_mm_xor_si128(zr1, zr2), e);
}

static FORCE_INLINE chainhash_gf chainhash_gf_mul( chainhash_gf a, chainhash_gf b ) {
    return chainhash_gf_reduce_add(chainhash_gf_mulraw(a, b), _mm_setzero_si128());
}

#elif defined(CHAINHASH_IMPL_ARM)

typedef uint64x2_t chainhash_v128;

static FORCE_INLINE chainhash_v128 chainhash_v_zero( void ) {
    return vdupq_n_u64(0);
}

static FORCE_INLINE chainhash_v128 chainhash_v_xor( chainhash_v128 a, chainhash_v128 b ) {
    return veorq_u64(a, b);
}

static FORCE_INLINE chainhash_v128 chainhash_v_xor3( chainhash_v128 a, chainhash_v128 b, chainhash_v128 c ) {
#if defined(__ARM_FEATURE_SHA3)
    return veor3q_u64(a, b, c);
#else
    return veorq_u64(veorq_u64(a, b), c);
#endif
}

static FORCE_INLINE chainhash_v128 chainhash_v_load2( const uint64_t * p ) {
    return vld1q_u64(p);
}

static FORCE_INLINE chainhash_v128 chainhash_v_add64( chainhash_v128 a, chainhash_v128 b ) {
    return vaddq_u64(a, b);
}

template <bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_v_loadwords( const uint8_t * p ) {
    uint8x16_t w = vld1q_u8(p);

    if (bswap) { w = vrev64q_u8(w); }
    return vreinterpretq_u64_u8(w);
}

// PMULL on the low halves / PMULL2 on the high halves as inline asm: with
// the intrinsics clang lowers a lane-0 x lane-1 product to DUP + PMULL2 and
// routes the recurrence state through a general register (FMOV/DUP), which
// doubles the SIMD op count of the block loop and adds ~10 cycles to every
// dependent multiply.  The asm pins the instruction; the compiler still
// schedules and allocates around it.
#if defined(_MSC_VER) && !defined(__clang__)
// MSVC has no GNU inline asm; the intrinsics are correct, only slower with
// the DUP/PMULL2 lowering described above.
static FORCE_INLINE uint64x2_t chainhash_pmull_lo( uint64x2_t a, uint64x2_t b ) {
    return vreinterpretq_u64_p128(vmull_p64(vgetq_lane_p64(vreinterpretq_p64_u64(a), 0),
            vgetq_lane_p64(vreinterpretq_p64_u64(b), 0)));
}

static FORCE_INLINE uint64x2_t chainhash_pmull_hi( uint64x2_t a, uint64x2_t b ) {
    return vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b)));
}

#else
static FORCE_INLINE uint64x2_t chainhash_pmull_lo( uint64x2_t a, uint64x2_t b ) {
    uint64x2_t r;

    __asm__ ("pmull %0.1q, %1.1d, %2.1d" : "=w" (r) : "w" (a), "w" (b));
    return r;
}

static FORCE_INLINE uint64x2_t chainhash_pmull_hi( uint64x2_t a, uint64x2_t b ) {
    uint64x2_t r;

    __asm__ ("pmull2 %0.1q, %1.2d, %2.2d" : "=w" (r) : "w" (a), "w" (b));
    return r;
}

#endif

// PMULL / PMULL2 on the two loaded registers of a group: no shuffle on the
// data path (the whole point of the strided pairing).
static FORCE_INLINE chainhash_v128 chainhash_v_clmul_ll( chainhash_v128 a, chainhash_v128 b ) {
    return chainhash_pmull_lo(a, b);
}

static FORCE_INLINE chainhash_v128 chainhash_v_clmul_hh( chainhash_v128 a, chainhash_v128 b ) {
    return chainhash_pmull_hi(a, b);
}

// The EXT that brings lane 1 of a down is on a's side, off the dependency
// chain through b (the recurrence state).
static FORCE_INLINE chainhash_v128 chainhash_v_clmul_hl( chainhash_v128 a, chainhash_v128 b ) {
    return chainhash_pmull_lo(vextq_u64(a, a, 1), b);
}

static FORCE_INLINE uint64_t chainhash_v_lo( chainhash_v128 v ) {
    return vgetq_lane_u64(v, 0);
}

static FORCE_INLINE uint64_t chainhash_v_hi( chainhash_v128 v ) {
    return vgetq_lane_u64(v, 1);
}

alignas(16) static const uint8_t chainhash_iota[16] = {
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
};

// The zero-padded r (1..16) bytes ENDING at end, read as the 16 bytes at
// end - 16 (which must be readable: the message has >= 16 bytes ending
// there) and shifted right by 16 - r bytes with TBL -- indices >= 16 read
// as zero, which is exactly the padding.  Reads only [end - 16, end).  The
// byte swap of a big-endian build is applied to the assembled words.
template <bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_v_load_end_padded( const uint8_t * end, size_t r ) {
    const uint8x16_t v   = vld1q_u8(end - 16);
    const uint8x16_t idx = vaddq_u8(vld1q_u8(chainhash_iota), vdupq_n_u8((uint8_t)(16 - r)));
    uint8x16_t       w   = vqtbl1q_u8(v, idx);

    if (bswap) { w = vrev64q_u8(w); }
    return vreinterpretq_u64_u8(w);
}

// Byte-gather tables for a whole message of r < 16 bytes: out[i] = the
// t[r][i]-th byte of the lane-loaded vector of chainhash_v_load_small
// (0xFF -> 0).  Layout of that vector:
//   8 <= r <= 15: lane .d[0] = bytes 0..7, lane .d[1] = bytes r-8..r-1
//   4 <= r <=  7: lane .s[0] = bytes 0..3, lane .s[1] = bytes r-4..r-1
//   1 <= r <=  3: bytes .b[0..2] = m[0], m[r/2], m[r-1]
// (XXH3's three size classes: every load is in bounds and overlapping).
alignas(16) static const uint8_t chainhash_gather[16][16] = {
    { 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  0
    { 0x00, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  1
    { 0x00, 0x01, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  2
    { 0x00, 0x01, 0x02, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  3
    { 0x00, 0x01, 0x02, 0x03, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  4
    { 0x00, 0x01, 0x02, 0x03, 0x07, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  5
    { 0x00, 0x01, 0x02, 0x03, 0x06, 0x07, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  6
    { 0x00, 0x01, 0x02, 0x03, 0x05, 0x06, 0x07, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  7
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  8
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r =  9
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0E, 0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r = 10
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0D, 0x0E, 0x0F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF },  // r = 11
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0C, 0x0D, 0x0E, 0x0F, 0xFF, 0xFF, 0xFF, 0xFF },  // r = 12
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0xFF, 0xFF, 0xFF },  // r = 13
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0xFF, 0xFF },  // r = 14
    { 0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x0E, 0x0F, 0xFF },  // r = 15
};

// The whole message: r (1..15) bytes at m, zero-padded to [w0, w1].  Reads
// only [m, m + r), all loads straight into SIMD lanes; the gather index
// depends on r alone.
template <bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_v_load_small( const uint8_t * m, size_t r ) {
    uint8x16_t v = vdupq_n_u8(0);

    if (r >= 8) {
        v = vreinterpretq_u8_u64(vld1q_lane_u64((const uint64_t *)m,           vreinterpretq_u64_u8(v), 0));
        v = vreinterpretq_u8_u64(vld1q_lane_u64((const uint64_t *)(m + r - 8), vreinterpretq_u64_u8(v), 1));
    } else if (r >= 4) {
        v = vreinterpretq_u8_u32(vld1q_lane_u32((const uint32_t *)m,           vreinterpretq_u32_u8(v), 0));
        v = vreinterpretq_u8_u32(vld1q_lane_u32((const uint32_t *)(m + r - 4), vreinterpretq_u32_u8(v), 1));
    } else {
        v = vld1q_lane_u8(m,            v, 0);
        v = vld1q_lane_u8(m + (r >> 1), v, 1);
        v = vld1q_lane_u8(m + r - 1,    v, 2);
    }
    uint8x16_t w = vqtbl1q_u8(v, vld1q_u8(chainhash_gather[r]));
    if (bswap) { w = vrev64q_u8(w); }
    return vreinterpretq_u64_u8(w);
}

// Field elements in lane 0 of a NEON register.  Reduction: one PMULL for
// the product, two PMULL2 for the reduction (ab = x 2^64 + y;  xr = x*27
// = z 2^64 + t;  result = y ^ t ^ z*27).  The two PMULL2 folds depend only
// on lane 1 of ab, so an addend XORed into ab first costs no latency;
// written out explicitly because clang cannot reassociate across the asm
// PMULLs.
typedef uint64x2_t chainhash_gf;

static FORCE_INLINE chainhash_gf chainhash_gf_from( uint64_t x ) {
    return vcombine_u64(vcreate_u64(x), vcreate_u64(0));
}

static FORCE_INLINE uint64_t chainhash_gf_to( chainhash_gf v ) {
    return vgetq_lane_u64(v, 0);
}

static FORCE_INLINE chainhash_gf chainhash_gf_xor( chainhash_gf a, chainhash_gf b ) {
    return veorq_u64(a, b);
}

// Twist: integer 64-bit addition of x to lane 0 (per-lane add, no carry
// across lanes; lane 1 + 0).
static FORCE_INLINE chainhash_gf chainhash_gf_addint( chainhash_gf a, uint64_t x ) {
    return vaddq_u64(a, chainhash_gf_from(x));
}

static FORCE_INLINE chainhash_v128 chainhash_gf_mulraw( chainhash_gf a, chainhash_gf b ) {
    return chainhash_pmull_lo(a, b);
}

static FORCE_INLINE chainhash_gf chainhash_gf_reduce_add( uint64x2_t ab, chainhash_gf add ) {
    const uint64x2_t rr = vdupq_n_u64(27);
    const uint64x2_t xr = chainhash_pmull_hi(ab, rr);
    const uint64x2_t zr = chainhash_pmull_hi(xr, rr);

    return chainhash_v_xor3(veorq_u64(ab, add), xr, zr);
}

static FORCE_INLINE void chainhash_gf_reduce_add2( uint64x2_t ab, chainhash_gf add0, chainhash_gf add1,
        chainhash_gf & o0, chainhash_gf & o1 ) {
    const uint64x2_t rr = vdupq_n_u64(27);
    const uint64x2_t xr = chainhash_pmull_hi(ab, rr);
    const uint64x2_t zr = chainhash_pmull_hi(xr, rr);

    o0 = chainhash_v_xor3(veorq_u64(ab, add0), xr, zr);
    o1 = chainhash_v_xor3(veorq_u64(ab, add1), xr, zr);
}

static FORCE_INLINE chainhash_gf chainhash_gf_reduce2_add( uint64x2_t ab1, uint64x2_t ab2, chainhash_gf add ) {
    const uint64x2_t rr  = vdupq_n_u64(27);
    const uint64x2_t xr1 = chainhash_pmull_hi(ab1, rr), xr2 = chainhash_pmull_hi(ab2, rr);
    const uint64x2_t zr1 = chainhash_pmull_hi(xr1, rr), zr2 = chainhash_pmull_hi(xr2, rr);
    const uint64x2_t e   = chainhash_v_xor3(chainhash_v_xor3(ab1, ab2, add), xr1, xr2);

    return chainhash_v_xor3(zr1, zr2, e);
}

static FORCE_INLINE chainhash_gf chainhash_gf_mul( chainhash_gf a, chainhash_gf b ) {
    return chainhash_gf_reduce_add(chainhash_gf_mulraw(a, b), vdupq_n_u64(0));
}

#else // CHAINHASH_IMPL_PORTABLE

struct chainhash_v128 {
    uint64_t  lo;
    uint64_t  hi;
};

static FORCE_INLINE chainhash_v128 chainhash_v_zero( void ) {
    chainhash_v128 v = { 0, 0 };

    return v;
}

static FORCE_INLINE chainhash_v128 chainhash_v_xor( chainhash_v128 a, chainhash_v128 b ) {
    chainhash_v128 v = { a.lo ^ b.lo, a.hi ^ b.hi };

    return v;
}

static FORCE_INLINE chainhash_v128 chainhash_v_xor3( chainhash_v128 a, chainhash_v128 b, chainhash_v128 c ) {
    chainhash_v128 v = { a.lo ^ b.lo ^ c.lo, a.hi ^ b.hi ^ c.hi };

    return v;
}

static FORCE_INLINE chainhash_v128 chainhash_v_load2( const uint64_t * p ) {
    chainhash_v128 v = { p[0], p[1] };

    return v;
}

template <bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_v_loadwords( const uint8_t * p ) {
    chainhash_v128 v = { GET_U64<bswap>(p, 0), GET_U64<bswap>(p, 8) };

    return v;
}

// 64x64 -> 128 carry-less product, bit by bit.
static FORCE_INLINE chainhash_v128 chainhash_clmul_serial( uint64_t a, uint64_t b ) {
    chainhash_v128 r = { 0, 0 };

    for (int i = 0; i < 64; i++) {
        const uint64_t m = UINT64_C(0) - ((b >> i) & 1);
        r.lo ^= (a << i) & m;
        if (i > 0) { r.hi ^= (a >> (64 - i)) & m; }
    }
    return r;
}

// Index arithmetic: lane 0 x lane 0 and lane 1 x lane 1 of the two
// two-word halves [w0, w1], [w2, w3] of a group are the pairs (w0, w2)
// and (w1, w3).
static FORCE_INLINE chainhash_v128 chainhash_v_clmul_ll( chainhash_v128 a, chainhash_v128 b ) {
    return chainhash_clmul_serial(a.lo, b.lo);
}

static FORCE_INLINE chainhash_v128 chainhash_v_clmul_hh( chainhash_v128 a, chainhash_v128 b ) {
    return chainhash_clmul_serial(a.hi, b.hi);
}

static FORCE_INLINE uint64_t chainhash_v_lo( chainhash_v128 v ) { return v.lo; }
static FORCE_INLINE uint64_t chainhash_v_hi( chainhash_v128 v ) { return v.hi; }

// Reduce a 128-bit polynomial modulo x^64 + x^4 + x^3 + x + 1, bit by bit
// (from the top down: bit 64+i set  =>  XOR in (x^64 + 27) << i).
static FORCE_INLINE uint64_t chainhash_reduce_serial( chainhash_v128 r ) {
    for (int i = 63; i >= 0; i--) {
        if ((r.hi >> i) & 1) {
            r.hi ^= UINT64_C(1) << i;
            r.lo ^= UINT64_C(27) << i;
            if (i > 0) { r.hi ^= UINT64_C(27) >> (64 - i); }
        }
    }
    return r.lo;
}

static FORCE_INLINE uint64_t chainhash_gfmul( uint64_t a, uint64_t b ) {
    return chainhash_reduce_serial(chainhash_clmul_serial(a, b));
}

typedef uint64_t chainhash_gf;

static FORCE_INLINE chainhash_gf chainhash_gf_from( uint64_t x ) { return x; }
static FORCE_INLINE chainhash_gf chainhash_gf_hi( uint64_t x ) { return x; }
static FORCE_INLINE uint64_t chainhash_gf_to( chainhash_gf v ) { return v; }
static FORCE_INLINE chainhash_gf chainhash_gf_xor( chainhash_gf a, chainhash_gf b ) { return a ^ b; }
static FORCE_INLINE chainhash_gf chainhash_gf_mul( chainhash_gf a, chainhash_gf b ) { return chainhash_gfmul(a, b); }
static FORCE_INLINE chainhash_gf chainhash_gf_addint( chainhash_gf a, uint64_t x ) { return a + x; }

static FORCE_INLINE chainhash_v128 chainhash_gf_mulraw( chainhash_gf a, chainhash_gf b ) {
    return chainhash_clmul_serial(a, b);
}

static FORCE_INLINE chainhash_gf chainhash_gf_reduce_add( chainhash_v128 ab, chainhash_gf add ) {
    return chainhash_reduce_serial(ab) ^ add;
}

static FORCE_INLINE void chainhash_gf_reduce_add2( chainhash_v128 ab, chainhash_gf add0, chainhash_gf add1,
        chainhash_gf & o0, chainhash_gf & o1 ) {
    const uint64_t r = chainhash_reduce_serial(ab);

    o0 = r ^ add0;
    o1 = r ^ add1;
}

static FORCE_INLINE chainhash_gf chainhash_gf_reduce2_add( chainhash_v128 ab1, chainhash_v128 ab2, chainhash_gf add ) {
    return chainhash_reduce_serial(chainhash_v_xor(ab1, ab2)) ^ add;
}

static FORCE_INLINE chainhash_gf chainhash_recur( chainhash_gf P, chainhash_v128 acc, chainhash_gf Yhi, chainhash_gf U ) {
    return acc.lo ^ chainhash_gfmul(acc.hi ^ Yhi, P ^ U);
}

#endif

//------------------------------------------------------------
// Zero-padded partial loads on the backends without a byte-permute unit:
// a 16-byte zero-padded stack copy.  Reads exactly the r bytes.

#if !defined(CHAINHASH_IMPL_ARM)

template <bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_v_load_end_padded( const uint8_t * end, size_t r ) {
    alignas(16) uint8_t buf[16];

    memset(buf, 0, 16);
    memcpy(buf, end - r, r);
    return chainhash_v_loadwords<bswap>(buf);
}

template <bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_v_load_small( const uint8_t * m, size_t r ) {
    return chainhash_v_load_end_padded<bswap>(m + r, r);
}

#endif

//------------------------------------------------------------
// PH level (backend independent from here on): the strided pairing.

// One 32-byte group: r0 = [w0, w1], r1 = [w2, w3] (any source), keys k[0..4):
//   clmul64(w0 ^ k0, w2 ^ k2) ^ clmul64(w1 ^ k1, w3 ^ k3)
// = clmul_ll(t0, t1) ^ clmul_hh(t0, t1) with t0 = r0 ^ [k0, k1], t1 = r1 ^ [k2, k3].
static FORCE_INLINE chainhash_v128 chainhash_ph_group32( const uint64_t * k, chainhash_v128 r0, chainhash_v128 r1,
        chainhash_v128 acc ) {
    const chainhash_v128 t0 = chainhash_v_xor(r0, chainhash_v_load2(k + 0));
    const chainhash_v128 t1 = chainhash_v_xor(r1, chainhash_v_load2(k + 2));

    return chainhash_v_xor3(acc, chainhash_v_clmul_ll(t0, t1), chainhash_v_clmul_hh(t0, t1));
}

// Two 32-byte groups (64 bytes = 8 words = 4 pairs) at p with keys k[0..8),
// into two independent accumulators.  Two loads per group, straight into
// the multiplies.  Reads exactly 64 bytes.
template <bool bswap>
static FORCE_INLINE void chainhash_ph_group( const uint64_t * k, const uint8_t * p, chainhash_v128 & acc0,
        chainhash_v128 & acc1 ) {
    acc0 = chainhash_ph_group32(k + 0, chainhash_v_loadwords<bswap>(p +  0), chainhash_v_loadwords<bswap>(p + 16), acc0);
    acc1 = chainhash_ph_group32(k + 4, chainhash_v_loadwords<bswap>(p + 32), chainhash_v_loadwords<bswap>(p + 48), acc1);
}

// Full (sub-)block of 8*WORDS bytes at blk (WORDS a multiple of 8):
//   XOR_{g < WORDS/4} [ clmul64(w[4g] ^ k[4g], w[4g+2] ^ k[4g+2]) ^ clmul64(w[4g+1] ^ k[4g+1], w[4g+3] ^ k[4g+3]) ]
template <int WORDS, bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_ph_block( const uint64_t * k, const uint8_t * blk ) {
    chainhash_v128 acc0 = chainhash_v_zero(), acc1 = chainhash_v_zero();

    for (int i = 0; i < WORDS; i += 8) {
        chainhash_ph_group<bswap>(k + i, blk + 8 * i, acc0, acc1);
    }
    return chainhash_v_xor(acc0, acc1);
}

// Partial last (sub-)block: rem (1 .. 8*WORDS - 1) bytes at p, G' =
// ceil(rem/32) groups = 2G' pairs, the final partial group zero-padded to
// 32 bytes.  Whole 64-byte and 32-byte groups (and the first 16 bytes of a
// partial group of more than 16 bytes) are loaded in place; the partial
// group's remaining 1..16 bytes go through chainhash_v_load_end_padded --
// whose PMULL-backend precondition (16 readable bytes ending at p + rem)
// holds because p + rem is the end of a message of >= 16 bytes on every
// call below.
template <int WORDS, bool bswap>
static FORCE_INLINE chainhash_v128 chainhash_ph_tail( const uint64_t * k, const uint8_t * p, size_t rem ) {
    chainhash_v128 acc0 = chainhash_v_zero(), acc1 = chainhash_v_zero();
    size_t pos = 0; // bytes consumed; word index = pos / 8

    for (; pos + 64 <= rem; pos += 64) {
        chainhash_ph_group<bswap>(k + pos / 8, p + pos, acc0, acc1);
    }
    chainhash_v128 acc  = chainhash_v_xor(acc0, acc1);
    size_t         rest = rem - pos; // 0..63
    if (rest > 32) {                 // one whole group, then a partial one
        acc  = chainhash_ph_group32(k + pos / 8, chainhash_v_loadwords<bswap>(p + pos), chainhash_v_loadwords<bswap>(p + pos + 16), acc);
        pos += 32;
        rest -= 32;
    }
    if (rest > 16) {                 // 17..32 bytes: [w0, w1] in place, [w2, w3] = the last 1..16 bytes, zero-padded
        acc = chainhash_ph_group32(k + pos / 8, chainhash_v_loadwords<bswap>(p + pos),
                chainhash_v_load_end_padded<bswap>(p + rem, rest - 16), acc);
    } else if (rest == 16) {         // exactly [w0, w1], in place; w2 = w3 = 0
        acc = chainhash_ph_group32(k + pos / 8, chainhash_v_loadwords<bswap>(p + pos), chainhash_v_zero(), acc);
    } else if (rest > 0) {           // 1..15 bytes: [w0, w1] = those bytes, zero-padded; w2 = w3 = 0
        acc = chainhash_ph_group32(k + pos / 8, chainhash_v_load_end_padded<bswap>(p + rem, rest), chainhash_v_zero(), acc);
    }
    return acc;
}

//------------------------------------------------------------
// Finalizer: the certified characteristic-2 degree-5 circuit (CIRCUITS[5]
// of website/js/char2.js in the paper's repository), transcribed gate by
// gate with x = the twisted input v and keys c[0..5):
//     y = x x
//     z = (y + c0)(x + y + c1)
//     t = (x + c2)(z + c3)
//   out = t + c4
// 3 multiplications; a MONIC degree-5 polynomial in x whose lower
// coefficients are a bijection of (c0..c4) over EVERY field of
// characteristic 2: with b = c0 + c1, d = c0 c1 the rows x^4..x^0 read
// 1 + c2, b + c2, c0 + c2 b, d + c3 + c0 c2, c4 + c2 (d + c3); in the
// coordinates q = (c2, b, c0, c3, c4) every row is q_i + (a polynomial in
// q_0..q_{i-1}), so the decoder is unit pivots only, no square roots
// (bench/chainhash/verify5.py, exh5.c, T5 of test_chainhash.cpp).  Hence
// the 5 parameters, drawn uniformly, give a uniformly random monic quintic:
// collision probability exactly 2^-64 and 5-wise independent outputs --
// 5-wise is what linear probing provably needs (Pagh-Pagh-Ruzic 2009;
// 4-wise is not enough, Patrascu-Thorup 2010).
//
// INPUT TWIST.  The circuit is applied to v = P + t_in with INTEGER 64-bit
// addition (carries and all), t_in one more key word.  Reason: over
// GF(2^64) squaring is GF(2)-linear, so v^e has GF(2)-degree popcount(e)
// and any polynomial of degree <= 6 is only QUADRATIC in the bits of v
// (7 = 111b is the first cubic exponent).  SMHasher3's fixed-seed keysets
// (Zeroes, Sparse, Permutation, TwoBytes, Bitflip) detect that: the
// untwisted degree-5 finalizer fails 22 of the 200 tests, although k-wise
// independence never asked for anything else.  Any bijection of the
// finalizer input keeps the 2^-64 bound and the 5-wise independence
// exactly (distinct inputs stay distinct), and the carry chain of an
// integer add is not GF(2)-affine: bit i of v + t has GF(2)-degree
// max(1, i - j0), j0 = t's lowest set bit; the composite has GF(2)-degree
// 63 for all but 2^-64 of the keys c when t_in is odd (appendix of the
// paper, proposition on the twisted finalizer).  Measured (M2 Pro, full
// SMHasher3): degree 5 + twist 200/200 at 81.8 small-key cycles vs 95.7
// for the former degree-7 circuit (4 mults); degree 3 + twist still fails
// 17 of 200.  The twist is not a mixer: it changes algebraic structure
// only, and its adequacy for a test suite is empirical.  Do NOT add
// heuristic mixing here; raise the degree or add provable structure
// instead.  Same gate order as bench/chainhash/chainhash.h.
//
// Schedule: every addend is folded into the reduction of the product it
// follows, and the square's two folds are shared by both operands of the
// second gate, so the three multiplications run back to back.

template <int K>
struct chainhash_finalize;

template <>
struct chainhash_finalize<5> {
    static FORCE_INLINE chainhash_gf apply( const uint64_t * c, chainhash_gf v ) {
        const chainhash_gf   C0 = chainhash_gf_from(c[0]), C1 = chainhash_gf_from(c[1]), C2 = chainhash_gf_from(c[2]);
        const chainhash_gf   C3 = chainhash_gf_from(c[3]), C4 = chainhash_gf_from(c[4]);
        const chainhash_v128 xx = chainhash_gf_mulraw(v, v);                                       // x x, unreduced
        chainhash_gf yc0, xyc1;

        chainhash_gf_reduce_add2(xx, C0, chainhash_gf_xor(v, C1), yc0, xyc1);                      // y + c0,  x + y + c1
        const chainhash_gf zc3 = chainhash_gf_reduce_add(chainhash_gf_mulraw(yc0, xyc1), C3);      // (y + c0)(x + y + c1) + c3
        return chainhash_gf_reduce_add(chainhash_gf_mulraw(chainhash_gf_xor(v, C2), zc3), C4);     // (x + c2)(z + c3) + c4
    }
};

//------------------------------------------------------------
// Seeding: derive the key from the 64-bit seed, fill in the derived
// values, and stash it in thread-local storage; the hash function receives
// the pointer.  Derivation order: k[0..BLOCK_WORDS), u, y, z, c[0..K), t_in.

static FORCE_INLINE uint64_t chainhash_gfmul64( uint64_t a, uint64_t b ) {
    return chainhash_gf_to(chainhash_gf_mul(chainhash_gf_from(a), chainhash_gf_from(b)));
}

template <int BLOCK_WORDS, int K>
static void chainhash_key_setup( chainhash_key<BLOCK_WORDS, K> & key ) {
    const uint64_t zu  = key.z ^ key.u;
    const uint64_t yzu = chainhash_gfmul64(key.y, zu);

    key.uy[0]   = key.u;    key.uy[1]   = key.y;
    key.yhi[0]  = 0;        key.yhi[1]  = key.y;
    key.zuzu[0] = zu;       key.zuzu[1] = zu;
    key.yyzu[0] = key.y;    key.yyzu[1] = yzu;
    key.tin[0]  = key.t_in; key.tin[1]  = 0;
    key.yzu     = yzu;
    key.yyzu_yu = chainhash_gfmul64(key.y, yzu) ^ chainhash_gfmul64(key.y, key.u);
    // the key-only second pair (0 ^ k[1])(0 ^ k[3]) of a message of at most 8 bytes, unreduced
    const chainhash_v128 k13 = chainhash_gf_mulraw(chainhash_gf_from(key.k[1]), chainhash_gf_from(key.k[3]));
    const uint64_t       ac  = chainhash_v_lo(k13), bc = chainhash_v_hi(k13);
    key.yzu8     = yzu ^ ac ^ chainhash_gfmul64(bc, zu);
    key.yyzu_yu8 = key.yyzu_yu ^ chainhash_gfmul64(ac, key.y) ^ chainhash_gfmul64(bc, yzu);
}

template <int BLOCK_WORDS, int K>
static uintptr_t chainhash_seed_init( const seed_t seed ) {
    static thread_local chainhash_key<BLOCK_WORDS, K> key;
    uint64_t s = (uint64_t)seed;

    for (int i = 0; i < BLOCK_WORDS; i++) {
        key.k[i] = chainhash_splitmix64(s);
    }
    key.u = chainhash_splitmix64(s);
    key.y = chainhash_splitmix64(s);
    key.z = chainhash_splitmix64(s);
    for (int i = 0; i < K; i++) {
        key.c[i] = chainhash_splitmix64(s);
    }
    key.t_in = chainhash_splitmix64(s);
    chainhash_key_setup(key);
    return (uintptr_t)&key;
}

//------------------------------------------------------------
// The hash function ignores the seed value, because it uses a separate
// seeding function; the seed argument is the pointer returned by it.
//
// S = sub-block split: each block is processed as S contiguous sub-blocks
// of BLOCK_WORDS/S words (keys k[i*BLOCK_WORDS/S ..)), each giving its own
// (a, b) pair and recurrence step, in order.  In the last block the groups
// of data (the zero-padded partial group included) belong to whichever
// sub-block they fall in; sub-blocks beyond the data contribute (0, 0).
// The length goes into the a of the very last pair.  S = 1 is the
// one-pair-per-block function.

#if !defined(CHAINHASH_IMPL_PORTABLE)

// Recurrence step on the state Q = P + u:  Q_i = (a_i + u) + (b_i + y) Q_{i-1},
// i.e. step_q(Q, t) = t[0] + t[1] Q with t = [a + u, b + y] = acc ^ uy; the
// very last step takes t = [a + len, b + y] (no u) and then yields P_n
// itself.  The addend t is folded into the product's reduction.
static FORCE_INLINE chainhash_gf chainhash_step_q( chainhash_gf Q, chainhash_v128 t ) {
    return chainhash_gf_reduce_add(chainhash_v_clmul_hl(t, Q), t);
}

// len <= sub-block bytes: all data sits in sub-block 0 of the only block,
// sub-blocks 1..S-1 are empty.  No loop, no length bookkeeping: the
// key-only parts of the S recurrence steps are constants of the key.  A
// message of 1..8 bytes has the pairs (w0 + k0)(0 + k2) and (0 + k1)(0 + k3);
// the second is a key constant folded into yzu8 / yyzu_yu8, so it costs
// nothing.  A message of 9..16 bytes has two pair products; the loop-free
// step folds them separately (chainhash_gf_reduce2_add) so that its latency
// equals the one-pair case.  Returns the finished hash in lane 0.
template <int BLOCK_WORDS, int K, int S, bool bswap>
static FORCE_INLINE chainhash_gf chainhash_small_v( const chainhash_key<BLOCK_WORDS, K> * key, const uint8_t * p,
        const size_t len ) {
    constexpr int  SW       = BLOCK_WORDS / S;                                          // words per sub-block
    constexpr bool FOLD8    = (S == 1 || S == 2);                                       // the loop-free steps below absorb the key-only pair
    const uint64_t cst_full = (S == 1) ? key->yzu : key->yyzu_yu;                       // key-only constant of the loop-free step
    chainhash_v128 acc;                                                                 // [a, b]  (FOLD8 && len <= 8: the first pair only)
    uint64_t       cst;

    if (len > 16) {
        acc = (len == 8 * (size_t)SW) ? chainhash_ph_block<SW, bswap>(key->k, p) : chainhash_ph_tail<SW, bswap>(key->k, p, len);
        cst = cst_full;
    } else if (len > 0) {
        // one zero-padded group: [w0, w1] (in place for 16 bytes, gathered below that), w2 = w3 = 0
        const chainhash_v128 w01 = (len == 16) ? chainhash_v_loadwords<bswap>(p) : chainhash_v_load_small<bswap>(p, len);
        const chainhash_v128 t0  = chainhash_v_xor(w01, chainhash_v_load2(key->k));     // [w0 + k0, w1 + k1]
        const chainhash_v128 K23 = chainhash_v_load2(key->k + 2);                       // [k2, k3]
        const chainhash_v128 pl  = chainhash_v_clmul_ll(t0, K23);                       // (w0 + k0) k2
        if (FOLD8 && (len <= 8)) {
            acc = pl;
            cst = (S == 1) ? key->yzu8 : key->yyzu_yu8;
        } else if (FOLD8) {
            // 9..16 bytes, two pair products pl, ph: fold them separately, so that the step's latency is that of one pair
            const chainhash_v128 ph = chainhash_v_clmul_hh(t0, K23);                    // (w1 + k1) k3
            const chainhash_gf   L  = chainhash_gf_from(chainhash_len_enc(len) ^ cst_full);
            chainhash_gf P;
            if (S == 1) {
                const chainhash_v128 ZUZU = chainhash_v_load2(key->zuzu);
                P = chainhash_gf_reduce2_add(chainhash_v_clmul_hh(pl, ZUZU), chainhash_v_clmul_hh(ph, ZUZU), chainhash_v_xor3(pl, ph, L));
            } else {
                const chainhash_v128 YYZU = chainhash_v_load2(key->yyzu);
                const chainhash_v128 s1   = chainhash_v_xor(chainhash_v_clmul_ll(pl, YYZU), chainhash_v_clmul_hh(pl, YYZU));
                const chainhash_v128 s2   = chainhash_v_xor(chainhash_v_clmul_ll(ph, YYZU), chainhash_v_clmul_hh(ph, YYZU));
                P = chainhash_gf_reduce2_add(s1, s2, L);
            }
            return chainhash_finalize<K>::apply(key->c, chainhash_v_add64(P, chainhash_v_load2(key->tin)));
        } else {
            acc = chainhash_v_xor(pl, chainhash_v_clmul_hh(t0, K23));
            cst = cst_full;
        }
    } else {
        acc = chainhash_v_zero();
        cst = cst_full;
    }
    chainhash_gf P;                                                                     // P_S, lane 0
    if (S == 1) {
        // P_1 = a + len + (b + y)(z + u) = (a + len + y(z+u)) + b (z+u): one high-half product on the accumulator
        P = chainhash_gf_reduce_add(chainhash_v_clmul_hh(acc, chainhash_v_load2(key->zuzu)),
                chainhash_v_xor(acc, chainhash_gf_from(chainhash_len_enc(len) ^ cst)));
    } else if (S == 2) {
        // P_2 = len + y (P_1 + u) = (len + yu + yy(z+u)) + a y + b y(z+u): two independent products, one reduction
        const chainhash_v128 YYZU = chainhash_v_load2(key->yyzu);
        const chainhash_v128 pr   = chainhash_v_xor(chainhash_v_clmul_ll(acc, YYZU), chainhash_v_clmul_hh(acc, YYZU));
        P = chainhash_gf_reduce_add(pr, chainhash_gf_from(chainhash_len_enc(len) ^ cst));
    } else {
        const chainhash_v128 UY = chainhash_v_load2(key->uy);
        chainhash_gf Q = chainhash_step_q(chainhash_v_load2(key->zuzu), chainhash_v_xor(acc, UY)); // sub-block 0
        for (int i = 1; i + 1 < S; i++) {
            Q = chainhash_step_q(Q, UY);                                                        // empty: (a, b) = (0, 0)
        }
        P = chainhash_step_q(Q, chainhash_gf_xor(chainhash_v_load2(key->yhi), chainhash_gf_from(chainhash_len_enc(len)))); // last, empty
    }
    return chainhash_finalize<K>::apply(key->c, chainhash_v_add64(P, chainhash_v_load2(key->tin)));   // chain(c, P_S + t_in)
}

// len > sub-block bytes.  Blocks 0..n-2 are full and need no length logic
// (state Q = P + u); the last block is peeled and does the sub-block
// selects once, its final step taking [a + len, b + y] and yielding P_n
// directly.  Out of line and reached by a tail call, so that ChainHash
// below is a leaf (no frame, no callee-saved spills) on every key that
// fits one sub-block.
template <int BLOCK_WORDS, int K, int S, bool bswap>
static NEVER_INLINE void chainhash_multi( const chainhash_key<BLOCK_WORDS, K> * key, const uint8_t * p,
        const size_t len, void * out ) {
    constexpr size_t BB = 8 * (size_t)BLOCK_WORDS;               // bytes per block
    constexpr int    SW = BLOCK_WORDS / S;                        // words per sub-block
    constexpr size_t SB = 8 * (size_t)SW;                         // bytes per sub-block
    const size_t n = (len + BB - 1) / BB;                         // >= 1 blocks (len > SB > 0)
    const chainhash_v128 UY = chainhash_v_load2(key->uy);
    chainhash_gf Q = chainhash_v_load2(key->zuzu);                // Q_0 = P_0 + u = z + u (lane 0)

    for (size_t j = 0; j + 1 < n; j++) {
        const uint8_t * blk = p + j * BB;
        for (int i = 0; i < S; i++) {
            Q = chainhash_step_q(Q, chainhash_v_xor(chainhash_ph_block<SW, bswap>(key->k + i * SW, blk + i * SB), UY));
        }
    }
    const size_t off = (n - 1) * BB;
    const size_t rem = len - off;                                 // bytes of input in the last block: 1..BB
    for (int i = 0; i < S; i++) {
        const size_t soff = (size_t)i * SB;                                                  // sub-block start within the block
        const size_t srem = (rem > soff) ? ((rem - soff < SB) ? rem - soff : SB) : 0;         // bytes of input in this sub-block
        chainhash_v128 acc;
        if (srem >= SB) {
            acc = chainhash_ph_block<SW, bswap>(key->k + i * SW, p + off + soff);            // full sub-block
        } else if (srem > 0) {
            acc = chainhash_ph_tail<SW, bswap>(key->k + i * SW, p + off + soff, srem);       // ceil(srem/32) groups; ends at p + len, len > SB >= 64
        } else {
            acc = chainhash_v_zero();                                                        // no data: empty PH sum
        }
        if (i + 1 < S) {
            Q = chainhash_step_q(Q, chainhash_v_xor(acc, UY));
        } else {                                                                             // [a + len, b + y] (no u): Q = P_n
            Q = chainhash_step_q(Q, chainhash_v_xor(acc, chainhash_gf_xor(chainhash_v_load2(key->yhi), chainhash_gf_from(chainhash_len_enc(len)))));
        }
    }
    // Input twist (integer add of t_in, a fixed bijection), then the degree-K chain.
    const chainhash_gf v = chainhash_v_add64(Q, chainhash_v_load2(key->tin));
    PUT_U64<bswap>(chainhash_gf_to(chainhash_finalize<K>::apply(key->c, v)), (uint8_t *)out, 0);
}

template <int BLOCK_WORDS, int K, int S, bool bswap>
static void ChainHash( const void * in, const size_t len, const seed_t seed, void * out ) {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
            "BLOCK_WORDS must be a positive multiple of 8*S (two 32-byte groups per inner iteration, per sub-block)");
    static_assert(K == 5, "only the degree-5 finalizer is shipped");

    const chainhash_key<BLOCK_WORDS, K> * key = (const chainhash_key<BLOCK_WORDS, K> *)(uintptr_t)seed;
    const uint8_t * p = (const uint8_t *)in;
    constexpr size_t SB = 8 * (size_t)(BLOCK_WORDS / S);          // bytes per sub-block

    if (unlikely(len > SB)) {
        return chainhash_multi<BLOCK_WORDS, K, S, bswap>(key, p, len, out);   // tail call
    }
    PUT_U64<bswap>(chainhash_gf_to(chainhash_small_v<BLOCK_WORDS, K, S, bswap>(key, p, len)), (uint8_t *)out, 0);
}

#else // CHAINHASH_IMPL_PORTABLE: the definition, evaluated literally

template <int BLOCK_WORDS, int K, int S, bool bswap>
static void ChainHash( const void * in, const size_t len, const seed_t seed, void * out ) {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
            "BLOCK_WORDS must be a positive multiple of 8*S (two 32-byte groups per inner iteration, per sub-block)");
    static_assert(K == 5, "only the degree-5 finalizer is shipped");

    const chainhash_key<BLOCK_WORDS, K> * key = (const chainhash_key<BLOCK_WORDS, K> *)(uintptr_t)seed;
    const uint8_t * p = (const uint8_t *)in;
    const size_t BB   = 8 * (size_t)BLOCK_WORDS;
    constexpr int SW  = BLOCK_WORDS / S;                       // words per sub-block
    const size_t SB   = 8 * (size_t)SW;                        // bytes per sub-block (== BB for S = 1)
    const size_t n    = (len == 0) ? 1 : (len + BB - 1) / BB; // n = max(1, ceil(len/BB))
    const chainhash_v128 lenv = { chainhash_len_enc(len), 0 };          // (len, 0): XORed into the a of the last pair

    const chainhash_gf Yhi = chainhash_gf_hi(key->y);
    const chainhash_gf U   = chainhash_gf_from(key->u);
    chainhash_gf P = chainhash_gf_from(key->z); // P_0 = z
    for (size_t j = 0; j < n; j++) {
        const size_t off = j * BB;
        const size_t rem = len - off; // bytes of input in this block (0 only if len == 0)
        for (int i = 0; i < S; i++) {
            const size_t soff = (size_t)i * SB;                                          // sub-block start within the block
            const size_t srem = (rem > soff) ? ((rem - soff < SB) ? rem - soff : SB) : 0; // bytes of input in this sub-block
            chainhash_v128 acc;
            if (srem >= SB) {
                acc = chainhash_ph_block<SW, bswap>(key->k + i * SW, p + off + soff);      // full sub-block
            } else if (srem > 0) {
                acc = chainhash_ph_tail<SW, bswap>(key->k + i * SW, p + off + soff, srem); // ceil(srem/32) groups
            } else {
                acc = chainhash_v_zero();                                                 // no data: empty PH sum
            }
            if ((j + 1 == n) && (i + 1 == S)) {                                          // length into the last pair's a
                acc = chainhash_v_xor(acc, lenv);
            }
            P = chainhash_recur(P, acc, Yhi, U);                                         // P_m = a_m + (b_m + y)(P_{m-1} + u)
        }
    }

    // Input twist (integer add of t_in, a fixed bijection), then the degree-K chain.
    const chainhash_gf v = chainhash_gf_addint(P, key->t_in);
    const uint64_t     h = chainhash_gf_to(chainhash_finalize<K>::apply(key->c, v));
    PUT_U64<bswap>(h, (uint8_t *)out, 0);
}

#endif

//------------------------------------------------------------
#if defined(CHAINHASH_IMPL_PORTABLE)
  #define CHAINHASH_IMPL_FLAGS   \
        FLAG_IMPL_MULTIPLY_64_64 | \
        FLAG_IMPL_LICENSE_BSD    | \
        FLAG_IMPL_VERY_SLOW
#else
  #define CHAINHASH_IMPL_FLAGS   \
        FLAG_IMPL_MULTIPLY_64_64 | \
        FLAG_IMPL_LICENSE_BSD
#endif

REGISTER_FAMILY(chainhash,
   $.src_status = HashFamilyInfo::SRC_ACTIVE
 );

REGISTER_HASH(chainhash_256_lenexp,
   $.desc       = "ChainHash (GF(2^64) carry-less PH with strided word pairing + three-key injective chain + degree-5 finalizer behind an additive twist), 256-byte blocks",
   $.impl       = CHAINHASH_IMPL_STR,
   $.hash_flags =
         FLAG_HASH_CLMUL_BASED,
   $.impl_flags =
         CHAINHASH_IMPL_FLAGS,
   $.bits = 64,
   $.verification_LE = 0xBFC38A57,
   $.verification_BE = 0xC84FA5C3,
   $.seedfn          = chainhash_seed_init<32, 5>,
   $.hashfn_native   = ChainHash<32, 5, 1, false>,
   $.hashfn_bswap    = ChainHash<32, 5, 1, true>
 );

REGISTER_HASH(chainhash_1k_lenexp,
   $.desc       = "ChainHash (GF(2^64) carry-less PH with strided word pairing + three-key injective chain + degree-5 finalizer behind an additive twist), 1024-byte blocks, 2 sub-blocks per block",
   $.impl       = CHAINHASH_IMPL_STR,
   $.hash_flags =
         FLAG_HASH_CLMUL_BASED,
   $.impl_flags =
         CHAINHASH_IMPL_FLAGS,
   $.bits = 64,
   $.verification_LE = 0x710CF02B,
   $.verification_BE = 0x1AB98587,
   $.seedfn          = chainhash_seed_init<128, 5>,
   $.hashfn_native   = ChainHash<128, 5, 2, false>,
   $.hashfn_bswap    = ChainHash<128, 5, 2, true>
 );
