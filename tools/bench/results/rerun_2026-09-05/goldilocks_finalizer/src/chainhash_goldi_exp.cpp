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
 * EXPERIMENTAL (goldilocks_finalizer, 2026-09-05): ChainHash with a
 * finalizer over the Goldilocks prime field F_p, p = 2^64 - 2^32 + 1,
 * instead of the characteristic-2 degree-5 circuit.  Derived from
 * hashes/chainhash.cpp (branch mr/chainhash) by derive_exp.py of the
 * experiment directory; PH and recurrence levels unchanged; every identifier
 * renamed (chg_ prefix, family chainhash_goldi) so that both files link into
 * one binary.  Registrations:
 *   chainhash-g4-256  256-byte blocks, S = 1, finalizer G4 (Motzkin's quartic,
 *                     2 multiplications, 4-wise independent)
 *   chainhash-g5-256  256-byte blocks, S = 1, finalizer G5 (the paper's
 *                     degree-5 scheme, 3 multiplications, 5-wise independent)
 *   chainhash-g5-1k   1 KB blocks, S = 2, finalizer G5
 * Finalizer input: x = P_n folded into F_p by one conditional subtraction
 * (v >= p -> v - p); no twist.  Keys g[] uniform in F_p by rejection sampling
 * of further splitmix64 words, appended after t_in (c[], t_in unused by G4/G5).
 * Reference: goldi_ref.py / chainhash_goldi.h of the experiment directory.
 *
 * ChainHash: a 64-bit hash over GF(2^64) = GF(2)[x]/(x^64 + x^4 + x^3 + x + 1)
 * built from three layers, all carry-less:
 *
 *   1. PH / carry-less NH over 8*BLOCK_WORDS-byte blocks.  Block j gives
 *        (a_j, b_j) = (lo64, hi64) of XOR_i clmul64(w[2i] ^ k[2i], w[2i+1] ^ k[2i+1])
 *      where the w[] are little-endian 64-bit words of the message.
 *      n = max(1, ceil(len / (8*BLOCK_WORDS))) blocks; blocks 1..n-1 are
 *      full, the last one holds r bytes and only W' = ceil(r/16) pairs
 *      (its final partial pair is zero-padded to 16 bytes).  The byte
 *      length is XORed into a_n.
 *      Sub-block split S (template parameter; S = 1 is the above): every
 *      block is cut into S contiguous sub-blocks of BLOCK_WORDS/S words,
 *      each with its own PH sum (a, b) over the pairs of data it holds
 *      (sub-blocks beyond the data have (a, b) = (0, 0)), fed to the
 *      recurrence in order; the length goes into the a of the LAST pair.
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
 * does not depend on S.
 *
 * Shipped configurations:
 *   chainhash-256:  BLOCK_WORDS = 32  (256-byte blocks), S = 1
 *   chainhash-1k:   BLOCK_WORDS = 128 (1 KB blocks),     S = 2
 *
 * Reference implementation and analysis: T. D. Ahle, "Fast Evaluation of
 * Polynomials with Rational Preprocessing", bench/chainhash/chg_ref.h.
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
 *     parts of the recurrence are constants of the key (chg_key_setup):
 *     for S = 1  P_1 = (a + len + y(z+u)) + b(z+u), one product on the PH
 *     accumulator; for S = 2 (the second sub-block is empty) the identity
 *     P_2 = (len + yu + yy(z+u)) + a y + b y(z+u), two independent products
 *     and one reduction;
 *   * the key holds the word pairs those paths need, loaded straight into
 *     vector registers, so no value moves between general and vector
 *     registers inside the hash function;
 *   * the multi-block path is out of line and reached by a tail call, so
 *     the hash function is a leaf for every key that fits one sub-block;
 *     blocks 0..n-2 run without length logic on the state Q = P + u, and the
 *     last block is peeled;
 *   * on AArch64 the partial pair of the last block is loaded in place with
 *     TBL byte shifts (no stack copy); the input is never read outside
 *     [in, in + len).
 */
#include "Platform.h"
#include "Hashlib.h"

//------------------------------------------------------------
// Backend selection.
//
//   CHG_IMPL_X86       x86-64 PCLMULQDQ (_mm_clmulepi64_si128)
//   CHG_IMPL_ARM       AArch64 PMULL.  Only used when the compiler
//                            advertises the AES/crypto feature
//                            (__ARM_FEATURE_AES / __ARM_FEATURE_CRYPTO) or
//                            SMHasher3 detected it (HAVE_ARM_AES).
//   CHG_IMPL_PORTABLE  bit-serial fallback; always compiles.
//
// Define CHG_FORCE_PORTABLE to select the fallback regardless of
// what the platform supports (used for cross-checking the backends).
#if !defined(CHG_FORCE_PORTABLE) && defined(HAVE_X86_64_CLMUL)
  #include "Intrinsics.h"
  #define CHG_IMPL_X86 1
  #define CHG_IMPL_STR "hwclmul"
#elif !defined(CHG_FORCE_PORTABLE) &&                       \
      (defined(__aarch64__) || defined(_M_ARM64)) &&               \
      (defined(__ARM_FEATURE_AES) || defined(__ARM_FEATURE_CRYPTO) || defined(HAVE_ARM_AES))
  #if defined(HAVE_ARM_NEON)
    #include "Intrinsics.h"
  #else
    #include <arm_neon.h>
  #endif
  #define CHG_IMPL_ARM 1
  #define CHG_IMPL_STR "hwpmull"
#else
  #define CHG_IMPL_PORTABLE 1
  #define CHG_IMPL_STR "portable"
#endif

//------------------------------------------------------------
// Key material.  k[] is the PH key; u, y, z the recurrence keys
// (P_0 = z, P_j = a_j + (b_j + y)(P_{j-1} + u)); c[] the finalizer
// parameters; t_in the input twist word.
//
// The remaining members are derived, message-independent values -- NOT key
// material, functions of the words above, filled by chg_key_setup().
// The SIMD backends load them straight into vector registers (so nothing
// moves between general and vector registers inside the hash function) and
// they hold the key-only parts of the recurrence that the loop-free
// single-sub-block path uses.  Word pairs are stored as (lane 0, lane 1).

template <int BLOCK_WORDS, int K>
struct chg_key {
    alignas(16) uint64_t k[BLOCK_WORDS];
    uint64_t u, y, z;
    uint64_t c[K];
    uint64_t t_in;
    uint64_t g[5];                 // G4 / G5 finalizer parameters, uniform in F_p (4 or 5 used)
    uint64_t ng[5];                // derived: p - g[i], the subtraction-form addition operands
    // derived (chg_key_setup)
    alignas(16) uint64_t uy[2];    // [u, y]:            t = acc ^ uy = [a + u, b + y], the operand of a recurrence step
    alignas(16) uint64_t yhi[2];   // [0, y]
    alignas(16) uint64_t zuzu[2];  // [z + u, z + u]:    P_0 + u, as lane 0 (state) and as lane 1 (high-half multiplicand)
    alignas(16) uint64_t yyzu[2];  // [y, y (z + u)]:    multipliers of a and b in the fused double step (S = 2)
    alignas(16) uint64_t tin[2];   // [t_in, 0]:         the twist, added to P_n as a 64-bit integer
    uint64_t yzu;                  // y (z + u):         single step   P_1 = (a + len + yzu) + b (z + u)
    uint64_t yyzu_yu;              // y y (z + u) + y u: fused step    P_2 = (len + yyzu_yu) + a y + b y (z + u)
};

static FORCE_INLINE uint64_t chg_splitmix64( uint64_t & state ) {
    uint64_t z = (state += UINT64_C(0x9E3779B97F4A7C15));

    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}

//------------------------------------------------------------
// Goldilocks prime field F_p, p = 2^64 - 2^32 + 1 (scalar), and the two
// experimental finalizers.  Verbatim goldi_field.h of the experiment
// (checked against Python big-int arithmetic on 10^6 inputs).
enum { CHG_FIN_CHAR2 = 0, CHG_FIN_G4 = 1, CHG_FIN_G5 = 2 };

#define CHG_GL_P   UINT64_C(0xFFFFFFFF00000001)
#define CHG_GL_EPS UINT64_C(0x00000000FFFFFFFF)
#if defined(__has_builtin)
#  if __has_builtin(__builtin_unpredictable)
#    define CHG_GL_UNPRED(c) __builtin_unpredictable(c)
#  endif
#endif
#ifndef CHG_GL_UNPRED
#  define CHG_GL_UNPRED(c) (c)
#endif

/* Any 64-bit value -> [0, p): one conditional subtraction. */
static FORCE_INLINE uint64_t chg_gl_fold(uint64_t v) { return CHG_GL_UNPRED(v >= CHG_GL_P) ? v - CHG_GL_P : v; }

/* a + b mod p, a arbitrary, b canonical with nb = p - b precomputed; result non-canonical. */
static FORCE_INLINE uint64_t chg_gl_add_nb(uint64_t a, uint64_t b, uint64_t nb) {
    const uint64_t r = a - nb;                 /* == a + b - p (mod 2^64) */
    return CHG_GL_UNPRED(a < nb) ? a + b : r;      /* a < nb: a + b < p, no overflow */
}
static FORCE_INLINE uint64_t chg_gl_add(uint64_t a, uint64_t b) { return chg_gl_add_nb(a, b, CHG_GL_P - b); }

/* reduce(lo + 2^64 hi) mod p for any 128-bit input; result in [0, 2^64). */
static FORCE_INLINE uint64_t chg_gl_reduce128(uint64_t lo, uint64_t hi) {
    const uint64_t hi_hi = hi >> 32, hi_lo = hi & CHG_GL_EPS;
    const uint64_t d  = lo - hi_hi;
    const uint64_t t0 = CHG_GL_UNPRED(lo < hi_hi) ? d - CHG_GL_EPS : d;   /* borrow: == lo - hi_hi + p */
    const uint64_t t1 = (hi_lo << 32) - hi_lo;                    /* hi_lo * EPS */
    const uint64_t s  = t0 + t1;
    return CHG_GL_UNPRED(s < t0) ? s + CHG_GL_EPS : s;                    /* carry: 2^64 == EPS, no second overflow */
}

#if defined(__SIZEOF_INT128__)
static FORCE_INLINE uint64_t chg_gl_mul(uint64_t a, uint64_t b) {               /* a b mod p, any a, b */
    const unsigned __int128 x = (unsigned __int128)a * b;
    return chg_gl_reduce128((uint64_t)x, (uint64_t)(x >> 64));
}
static FORCE_INLINE uint64_t chg_gl_mul_add(uint64_t a, uint64_t b, uint64_t c) { /* a b + c mod p, any a, b, c */
    const unsigned __int128 x = (unsigned __int128)a * b + c;         /* <= 2^128 - 2^64: no overflow */
    return chg_gl_reduce128((uint64_t)x, (uint64_t)(x >> 64));
}
#else
/* 32-bit-limb fallback (no __int128): schoolbook 64x64 -> 128. */
static FORCE_INLINE void chg_gl_mul64_128(uint64_t a, uint64_t b, uint64_t* lo, uint64_t* hi) {
    const uint64_t a0 = (uint32_t)a, a1 = a >> 32, b0 = (uint32_t)b, b1 = b >> 32;
    const uint64_t p00 = a0 * b0, p01 = a0 * b1, p10 = a1 * b0, p11 = a1 * b1;
    const uint64_t mid = (p00 >> 32) + (uint32_t)p01 + (uint32_t)p10;
    *lo = (mid << 32) | (uint32_t)p00;
    *hi = p11 + (p01 >> 32) + (p10 >> 32) + (mid >> 32);
}
static FORCE_INLINE uint64_t chg_gl_mul(uint64_t a, uint64_t b) { uint64_t lo, hi; chg_gl_mul64_128(a, b, &lo, &hi); return chg_gl_reduce128(lo, hi); }
static FORCE_INLINE uint64_t chg_gl_mul_add(uint64_t a, uint64_t b, uint64_t c) {
    uint64_t lo, hi; chg_gl_mul64_128(a, b, &lo, &hi);
    const uint64_t s = lo + c; hi += (s < lo); return chg_gl_reduce128(s, hi);
}
#endif

/* ---- the two finalizers (x canonical, keys canonical, nb[i] = p - key[i]) ----
 * G4  Motzkin's quartic:  y = x (x + b0) + b1,  out = y (y + x + b2) + b3
 *     2 multiplications; out = x^4 + (2 b0 + 1) x^3 + (b0^2 + b0 + 2 b1 + b2) x^2
 *     + (2 b0 b1 + b1 + b0 b2) x + (b1^2 + b1 b2 + b3): a bijection of
 *     (b0..b3) whenever 2 is invertible (check_bijections.py).
 * G5  the paper's degree-5 scheme with integer preprocessing:
 *     out = (x + c2) ((x^2 + c4)(x^2 + x + c3) + c1) + c0,  3 multiplications;
 *     out = x^5 + (c2 + 1) x^4 + (c2 + c3 + c4) x^3 + (c4 + c2 (c3 + c4)) x^2
 *     + (c1 + c3 c4 + c2 c4) x + (c0 + c2 (c1 + c3 c4)): unit pivots, a
 *     bijection over Z and hence over every field (check_bijections.py).
 * Schedule: the sums that involve only x and a key (x + b2, x + c3, x + c2) are
 * computed off the critical path and folded so they can serve as the canonical
 * operand of a later addition; every addition that follows a multiply is fused
 * into that multiply's reduction (chg_gl_mul_add). */
static FORCE_INLINE uint64_t chg_gl_fin_g4(const uint64_t* b, const uint64_t* nb, uint64_t x) {
    const uint64_t xb2 = chg_gl_fold(chg_gl_add_nb(x, b[2], nb[2]));                      /* x + b2, canonical (off path) */
    const uint64_t y   = chg_gl_mul_add(x, chg_gl_add_nb(x, b[0], nb[0]), b[1]);          /* x (x + b0) + b1 */
    return chg_gl_fold(chg_gl_mul_add(y, chg_gl_add_nb(y, xb2, CHG_GL_P - xb2), b[3]));           /* y (y + x + b2) + b3 */
}
static FORCE_INLINE uint64_t chg_gl_fin_g5(const uint64_t* c, const uint64_t* nc, uint64_t x) {
    const uint64_t xc3 = chg_gl_fold(chg_gl_add_nb(x, c[3], nc[3]));                      /* x + c3, canonical (off path) */
    const uint64_t xc2 = chg_gl_add_nb(x, c[2], nc[2]);                               /* x + c2 (off path; a multiplicand may be non-canonical) */
    const uint64_t x2  = chg_gl_mul(x, x);
    const uint64_t f   = chg_gl_add_nb(x2, c[4], nc[4]);                              /* x^2 + c4 */
    const uint64_t g   = chg_gl_add_nb(x2, xc3, CHG_GL_P - xc3);                          /* x^2 + x + c3 */
    const uint64_t t   = chg_gl_mul_add(f, g, c[1]);                                  /* (x^2 + c4)(x^2 + x + c3) + c1 */
    return chg_gl_fold(chg_gl_mul_add(xc2, t, c[0]));                                     /* (x + c2) t + c0 */
}

/* Uniform element of F_p from a splitmix64 stream: rejection sampling
 * (a 64-bit word is rejected with probability (2^32 - 1)/2^64). */
static FORCE_INLINE uint64_t chg_gl_splitmix64(uint64_t* state) {
    uint64_t z = (*state += UINT64_C(0x9E3779B97F4A7C15));
    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}
static FORCE_INLINE uint64_t chg_gl_uniform(uint64_t* state) {
    uint64_t v;
    do { v = chg_gl_splitmix64(state); } while (v >= CHG_GL_P);
    return v;
}

//------------------------------------------------------------
// Backend primitives.  Every backend provides
//
//   chg_v128                 a 128-bit accumulator type
//   chg_v_zero()             all-zero accumulator
//   chg_v_xor(a, b)
//   chg_v_loadpair<bswap>(p, k)
//        (w0 ^ k[0], w1 ^ k[1]) with w0, w1 the little-endian 64-bit words
//        at p, p + 8 (GET_U64<bswap>, so big-endian builds agree)
//   chg_v_clmulpair(t)       clmul64(lane0(t), lane1(t)), unreduced
//   chg_ph_group<bswap>(k, p, acc0, acc1)
//        four pairs XORed into two accumulators (reads exactly 64 bytes)
//   chg_ph_pair<bswap>(k, p)
//        the pair product of the whole 16-byte pair at p (reads exactly
//        16 bytes)
//   chg_ph_partial_end<bswap>(k, end, r)
//        the pair product of the r (1..15) bytes ENDING at end, zero-padded
//        to 16 bytes.  PRECONDITION on the PMULL backend: the 16 bytes
//        ending at end are readable (end is the end of a message of >= 16
//        bytes); it then reads [end - 16, end) and nothing else
//   chg_ph_small<bswap>(k, m, r)
//        the pair product of a whole message of r (1..15) bytes at m,
//        zero-padded; reads only [m, m + r)
//   chg_gf                   a field element of GF(2^64) held in a
//        register: lane 0 of a vector on the SIMD backends (lane 1 is
//        garbage that nothing reads), a uint64_t on the portable one.
//        Keeping the recurrence and the finalizer in vector registers
//        avoids a GPR<->SIMD round trip per multiply.
//   chg_gf_from(x) / chg_gf_to(v)
//        x in lane 0 / lane 0 out
//   chg_gf_xor(a, b), chg_gf_mul(a, b)
//        a * b in GF(2^64), reduction constant 27
//   chg_gf_mulraw(a, b)      lane0(a) * lane0(b), the unreduced
//        128-bit product (a chg_v128)
//   chg_gf_reduce_add(ab, add)
//        reduce(ab) + add, the addend folded into the reduction (its XOR
//        overlaps the two folds, which depend only on the high half of ab)
//   chg_gf_reduce_add2(ab, add0, add1, o0, o1)
//        o0 = reduce(ab) + add0, o1 = reduce(ab) + add1, the folds shared
//   chg_gf_addint(a, x)
//        the input twist: lane 0 of a plus x as a 64-bit INTEGER (carries
//        and all; lane 1 gets + 0 and stays unread garbage)
//
// The SIMD backends additionally provide, for the register-resident
// evaluation (chg_small_v / chg_multi below):
//
//   chg_v_load2(p)           the 16-byte-aligned word pair p[0..2)
//        as the vector [p[0], p[1]]
//   chg_v_add64(a, b)        per-lane 64-bit integer addition
//   chg_v_clmul_hh(a, b)     lane1(a) * lane1(b), unreduced
//   chg_v_clmul_hl(a, b)     lane1(a) * lane0(b), unreduced
//
// The portable backend instead provides chg_gf_hi(x) (x in lane 1)
// and chg_recur(P, acc, Yhi, U), one literal recurrence step
// a + (b + y)(P + u) with (a, b) the two halves of acc.

#if defined(CHG_IMPL_X86)

typedef __m128i chg_v128;

static FORCE_INLINE chg_v128 chg_v_zero( void ) {
    return _mm_setzero_si128();
}

static FORCE_INLINE chg_v128 chg_v_xor( chg_v128 a, chg_v128 b ) {
    return _mm_xor_si128(a, b);
}

static FORCE_INLINE chg_v128 chg_v_load2( const uint64_t * p ) {
    return _mm_load_si128((const __m128i *)p);
}

static FORCE_INLINE chg_v128 chg_v_add64( chg_v128 a, chg_v128 b ) {
    return _mm_add_epi64(a, b);
}

template <bool bswap>
static FORCE_INLINE chg_v128 chg_v_loadpair( const uint8_t * p, const uint64_t * k ) {
    __m128i w = _mm_loadu_si128((const __m128i *)p);

    if (bswap) { w = mm_bswap64(w); }
    return _mm_xor_si128(w, _mm_loadu_si128((const __m128i *)k));
}

// The immediate of PCLMULQDQ selects the halves: bit 0 the half of the
// first operand, bit 4 the half of the second.
static FORCE_INLINE chg_v128 chg_v_clmulpair( chg_v128 t ) {
    return _mm_clmulepi64_si128(t, t, 0x10);
}

static FORCE_INLINE chg_v128 chg_v_clmul_hh( chg_v128 a, chg_v128 b ) {
    return _mm_clmulepi64_si128(a, b, 0x11);
}

static FORCE_INLINE chg_v128 chg_v_clmul_hl( chg_v128 a, chg_v128 b ) {
    return _mm_clmulepi64_si128(a, b, 0x01);
}

template <bool bswap>
static FORCE_INLINE void chg_ph_group( const uint64_t * k, const uint8_t * p, chg_v128 & acc0,
        chg_v128 & acc1 ) {
    acc0 = chg_v_xor(acc0, chg_v_xor(chg_v_clmulpair(chg_v_loadpair<bswap>(p +  0, k + 0)),
                                                 chg_v_clmulpair(chg_v_loadpair<bswap>(p + 16, k + 2))));
    acc1 = chg_v_xor(acc1, chg_v_xor(chg_v_clmulpair(chg_v_loadpair<bswap>(p + 32, k + 4)),
                                                 chg_v_clmulpair(chg_v_loadpair<bswap>(p + 48, k + 6))));
}

// Field elements in lane 0 of an XMM register.  Reduction: one CLMUL for
// the product, two for the reduction (ab = x 2^64 + y;  xr = x*27 = z 2^64
// + t;  result = y ^ t ^ z*27); the immediate selects the high half, so no
// lane moves are needed.
typedef __m128i chg_gf;

static FORCE_INLINE chg_gf chg_gf_from( uint64_t x ) {
    return _mm_cvtsi64_si128((long long)x);
}

static FORCE_INLINE uint64_t chg_gf_to( chg_gf v ) {
    return (uint64_t)_mm_cvtsi128_si64(v);
}

static FORCE_INLINE chg_gf chg_gf_xor( chg_gf a, chg_gf b ) {
    return _mm_xor_si128(a, b);
}

// Twist: integer 64-bit addition of x to lane 0 (per-lane add, no carry
// across lanes; lane 1 + 0).
static FORCE_INLINE chg_gf chg_gf_addint( chg_gf a, uint64_t x ) {
    return _mm_add_epi64(a, _mm_cvtsi64_si128((long long)x));
}

static FORCE_INLINE chg_v128 chg_gf_mulraw( chg_gf a, chg_gf b ) {
    return _mm_clmulepi64_si128(a, b, 0x00);
}

static FORCE_INLINE chg_gf chg_gf_reduce_add( __m128i ab, chg_gf add ) {
    const __m128i r  = _mm_set_epi64x(0, 27);
    const __m128i xr = _mm_clmulepi64_si128(ab, r, 0x01);
    const __m128i zr = _mm_clmulepi64_si128(xr, r, 0x01);

    return _mm_xor_si128(_mm_xor_si128(_mm_xor_si128(ab, add), xr), zr);
}

static FORCE_INLINE void chg_gf_reduce_add2( __m128i ab, chg_gf add0, chg_gf add1,
        chg_gf & o0, chg_gf & o1 ) {
    const __m128i r  = _mm_set_epi64x(0, 27);
    const __m128i xr = _mm_clmulepi64_si128(ab, r, 0x01);
    const __m128i zr = _mm_clmulepi64_si128(xr, r, 0x01);
    const __m128i xz = _mm_xor_si128(xr, zr);

    o0 = _mm_xor_si128(_mm_xor_si128(ab, add0), xz);
    o1 = _mm_xor_si128(_mm_xor_si128(ab, add1), xz);
}

static FORCE_INLINE chg_gf chg_gf_mul( chg_gf a, chg_gf b ) {
    return chg_gf_reduce_add(chg_gf_mulraw(a, b), _mm_setzero_si128());
}

#elif defined(CHG_IMPL_ARM)

typedef uint64x2_t chg_v128;

static FORCE_INLINE chg_v128 chg_v_zero( void ) {
    return vdupq_n_u64(0);
}

static FORCE_INLINE chg_v128 chg_v_xor( chg_v128 a, chg_v128 b ) {
    return veorq_u64(a, b);
}

static FORCE_INLINE chg_v128 chg_v_load2( const uint64_t * p ) {
    return vld1q_u64(p);
}

static FORCE_INLINE chg_v128 chg_v_add64( chg_v128 a, chg_v128 b ) {
    return vaddq_u64(a, b);
}

template <bool bswap>
static FORCE_INLINE chg_v128 chg_v_loadpair( const uint8_t * p, const uint64_t * k ) {
    uint8x16_t w = vld1q_u8(p);

    if (bswap) { w = vrev64q_u8(w); }
    return veorq_u64(vreinterpretq_u64_u8(w), vld1q_u64(k));
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
static FORCE_INLINE uint64x2_t chg_pmull_lo( uint64x2_t a, uint64x2_t b ) {
    return vreinterpretq_u64_p128(vmull_p64(vgetq_lane_p64(vreinterpretq_p64_u64(a), 0),
            vgetq_lane_p64(vreinterpretq_p64_u64(b), 0)));
}

static FORCE_INLINE uint64x2_t chg_pmull_hi( uint64x2_t a, uint64x2_t b ) {
    return vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b)));
}

  #define CHG_OPAQUE_PTR(p) ((void)0)
#else
static FORCE_INLINE uint64x2_t chg_pmull_lo( uint64x2_t a, uint64x2_t b ) {
    uint64x2_t r;

    __asm__ ("pmull %0.1q, %1.1d, %2.1d" : "=w" (r) : "w" (a), "w" (b));
    return r;
}

static FORCE_INLINE uint64x2_t chg_pmull_hi( uint64x2_t a, uint64x2_t b ) {
    uint64x2_t r;

    __asm__ ("pmull2 %0.1q, %1.2d, %2.2d" : "=w" (r) : "w" (a), "w" (b));
    return r;
}

// Hides a pointer's provenance from the optimizer (see chg_ldword).
  #define CHG_OPAQUE_PTR(p) __asm__ ("" : "+r" (p))
#endif

static FORCE_INLINE uint64x2_t chg_xor3( uint64x2_t a, uint64x2_t b, uint64x2_t c ) {
#if defined(__ARM_FEATURE_SHA3)
    return veor3q_u64(a, b, c);
#else
    return veorq_u64(veorq_u64(a, b), c);
#endif
}

static FORCE_INLINE chg_v128 chg_v_clmulpair( chg_v128 t ) {
    return chg_pmull_lo(t, vextq_u64(t, t, 1));
}

static FORCE_INLINE chg_v128 chg_v_clmul_hh( chg_v128 a, chg_v128 b ) {
    return chg_pmull_hi(a, b);
}

// The EXT that brings lane 1 of a down is on a's side, off the dependency
// chain through b (the recurrence state).
static FORCE_INLINE chg_v128 chg_v_clmul_hl( chg_v128 a, chg_v128 b ) {
    return chg_pmull_lo(vextq_u64(a, a, 1), b);
}

// Four pairs: e01 = (t0[1], t1[0]) makes pmull(t0, e01) = t0[0] t0[1] and
// pmull2(e01, t1) = t1[0] t1[1], one EXT per two pairs and no DUPs.
template <bool bswap>
static FORCE_INLINE void chg_ph_group( const uint64_t * k, const uint8_t * p, chg_v128 & acc0,
        chg_v128 & acc1 ) {
    const uint64x2_t t0  = chg_v_loadpair<bswap>(p +  0, k + 0);
    const uint64x2_t t1  = chg_v_loadpair<bswap>(p + 16, k + 2);
    const uint64x2_t t2  = chg_v_loadpair<bswap>(p + 32, k + 4);
    const uint64x2_t t3  = chg_v_loadpair<bswap>(p + 48, k + 6);
    const uint64x2_t e01 = vextq_u64(t0, t1, 1);
    const uint64x2_t e23 = vextq_u64(t2, t3, 1);

    acc0 = chg_xor3(acc0, chg_pmull_lo(t0, e01), chg_pmull_hi(e01, t1));
    acc1 = chg_xor3(acc1, chg_pmull_lo(t2, e23), chg_pmull_hi(e23, t3));
}

// Single pairs are multiplied as pmull(w ^ [k0, *], w1lo ^ [k1, *]) with
// w = [w0, w1] and w1lo = [w1, *] loaded separately: the high word already
// sits in lane 0, so there is no EXT on the data path.

// 8 bytes at p into lane 0 (lane 1 zero), as a genuine second load: the
// pointer is made opaque, otherwise clang merges it with an enclosing
// 16-byte load and extracts the lane through a general register.
template <bool bswap>
static FORCE_INLINE uint64x2_t chg_ldword( const void * p ) {
    const uint8_t * q = (const uint8_t *)p;

    CHG_OPAQUE_PTR(q);
    uint8x16_t w = vcombine_u8(vld1_u8(q), vdup_n_u8(0));
    if (bswap) { w = vrev64q_u8(w); }
    return vreinterpretq_u64_u8(w);
}

struct chg_pairw {
    uint64x2_t  w;     // [w0, w1]
    uint64x2_t  w1lo;  // [w1, *]
};

// The pair whose 16 bytes are v permuted by the TBL index idx (an index
// >= 16 reads as zero: the padding); the second TBL, with the index
// rotated by 8, yields the high word in lane 0.  Both TBLs run in parallel.
// The byte swap of a big-endian build is applied to the assembled words.
template <bool bswap>
static FORCE_INLINE chg_pairw chg_pairw_tbl( uint8x16_t v, uint8x16_t idx ) {
    uint8x16_t w  = vqtbl1q_u8(v, idx);
    uint8x16_t w1 = vqtbl1q_u8(v, vextq_u8(idx, idx, 8));

    if (bswap) { w = vrev64q_u8(w); w1 = vrev64q_u8(w1); }
    chg_pairw pw = { vreinterpretq_u64_u8(w), vreinterpretq_u64_u8(w1) };
    return pw;
}

// clmul64(w0 ^ k[0], w1 ^ k[1])
static FORCE_INLINE uint64x2_t chg_ph_pair_w( const uint64_t * k, chg_pairw pw ) {
    return chg_pmull_lo(veorq_u64(pw.w, vld1q_u64(k)), veorq_u64(pw.w1lo, chg_ldword<false>(k + 1)));
}

// One whole pair at p.  Reads exactly 16 bytes (as 16 + 8).
template <bool bswap>
static FORCE_INLINE chg_v128 chg_ph_pair( const uint64_t * k, const uint8_t * p ) {
    uint8x16_t w = vld1q_u8(p);

    if (bswap) { w = vrev64q_u8(w); }
    chg_pairw pw = { vreinterpretq_u64_u8(w), chg_ldword<bswap>(p + 8) };
    return chg_ph_pair_w(k, pw);
}

alignas(16) static const uint8_t chg_iota[16] = {
    0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
};

// The zero-padded partial pair made of the r (1..15) bytes ENDING at end,
// read as the 16 bytes at end - 16 (which must be readable: the message
// has >= 16 bytes ending there) and shifted right by 16 - r bytes with TBL
// -- indices >= 16 read as zero, which is exactly the padding.  Reads only
// [end - 16, end).
template <bool bswap>
static FORCE_INLINE chg_v128 chg_ph_partial_end( const uint64_t * k, const uint8_t * end, size_t r ) {
    const uint8x16_t v   = vld1q_u8(end - 16);
    const uint8x16_t idx = vaddq_u8(vld1q_u8(chg_iota), vdupq_n_u8((uint8_t)(16 - r)));

    return chg_ph_pair_w(k, chg_pairw_tbl<bswap>(v, idx));
}

// Byte-gather tables for a whole message of r < 16 bytes: out[i] = the
// t[r][i]-th byte of the lane-loaded vector of chg_ph_small (0xFF ->
// 0).  Layout of that vector:
//   8 <= r <= 15: lane .d[0] = bytes 0..7, lane .d[1] = bytes r-8..r-1
//   4 <= r <=  7: lane .s[0] = bytes 0..3, lane .s[1] = bytes r-4..r-1
//   1 <= r <=  3: bytes .b[0..2] = m[0], m[r/2], m[r-1]
// (XXH3's three size classes: every load is in bounds and overlapping).
alignas(16) static const uint8_t chg_gather[16][16] = {
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

// The whole message: r (1..15) bytes at m, zero-padded to one pair.  Reads
// only [m, m + r), all loads straight into SIMD lanes; the gather index
// depends on r alone.
template <bool bswap>
static FORCE_INLINE chg_v128 chg_ph_small( const uint64_t * k, const uint8_t * m, size_t r ) {
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
    return chg_ph_pair_w(k, chg_pairw_tbl<bswap>(v, vld1q_u8(chg_gather[r])));
}

// Field elements in lane 0 of a NEON register.  Reduction: one PMULL for
// the product, two PMULL2 for the reduction (ab = x 2^64 + y;  xr = x*27
// = z 2^64 + t;  result = y ^ t ^ z*27).  The two PMULL2 folds depend only
// on lane 1 of ab, so an addend XORed into ab first costs no latency;
// written out explicitly because clang cannot reassociate across the asm
// PMULLs.
typedef uint64x2_t chg_gf;

static FORCE_INLINE chg_gf chg_gf_from( uint64_t x ) {
    return vcombine_u64(vcreate_u64(x), vcreate_u64(0));
}

static FORCE_INLINE uint64_t chg_gf_to( chg_gf v ) {
    return vgetq_lane_u64(v, 0);
}

static FORCE_INLINE chg_gf chg_gf_xor( chg_gf a, chg_gf b ) {
    return veorq_u64(a, b);
}

// Twist: integer 64-bit addition of x to lane 0 (per-lane add, no carry
// across lanes; lane 1 + 0).
static FORCE_INLINE chg_gf chg_gf_addint( chg_gf a, uint64_t x ) {
    return vaddq_u64(a, chg_gf_from(x));
}

static FORCE_INLINE chg_v128 chg_gf_mulraw( chg_gf a, chg_gf b ) {
    return chg_pmull_lo(a, b);
}

static FORCE_INLINE chg_gf chg_gf_reduce_add( uint64x2_t ab, chg_gf add ) {
    const uint64x2_t rr = vdupq_n_u64(27);
    const uint64x2_t xr = chg_pmull_hi(ab, rr);
    const uint64x2_t zr = chg_pmull_hi(xr, rr);

    return chg_xor3(veorq_u64(ab, add), xr, zr);
}

static FORCE_INLINE void chg_gf_reduce_add2( uint64x2_t ab, chg_gf add0, chg_gf add1,
        chg_gf & o0, chg_gf & o1 ) {
    const uint64x2_t rr = vdupq_n_u64(27);
    const uint64x2_t xr = chg_pmull_hi(ab, rr);
    const uint64x2_t zr = chg_pmull_hi(xr, rr);

    o0 = chg_xor3(veorq_u64(ab, add0), xr, zr);
    o1 = chg_xor3(veorq_u64(ab, add1), xr, zr);
}

static FORCE_INLINE chg_gf chg_gf_mul( chg_gf a, chg_gf b ) {
    return chg_gf_reduce_add(chg_gf_mulraw(a, b), vdupq_n_u64(0));
}

#else // CHG_IMPL_PORTABLE

struct chg_v128 {
    uint64_t  lo;
    uint64_t  hi;
};

static FORCE_INLINE chg_v128 chg_v_zero( void ) {
    chg_v128 v = { 0, 0 };

    return v;
}

static FORCE_INLINE chg_v128 chg_v_xor( chg_v128 a, chg_v128 b ) {
    chg_v128 v = { a.lo ^ b.lo, a.hi ^ b.hi };

    return v;
}

template <bool bswap>
static FORCE_INLINE chg_v128 chg_v_loadpair( const uint8_t * p, const uint64_t * k ) {
    chg_v128 v = { GET_U64<bswap>(p, 0) ^ k[0], GET_U64<bswap>(p, 8) ^ k[1] };

    return v;
}

// 64x64 -> 128 carry-less product, bit by bit.
static FORCE_INLINE chg_v128 chg_clmul_serial( uint64_t a, uint64_t b ) {
    chg_v128 r = { 0, 0 };

    for (int i = 0; i < 64; i++) {
        const uint64_t m = UINT64_C(0) - ((b >> i) & 1);
        r.lo ^= (a << i) & m;
        if (i > 0) { r.hi ^= (a >> (64 - i)) & m; }
    }
    return r;
}

static FORCE_INLINE chg_v128 chg_v_clmulpair( chg_v128 t ) {
    return chg_clmul_serial(t.lo, t.hi);
}

// Reduce a 128-bit polynomial modulo x^64 + x^4 + x^3 + x + 1, bit by bit
// (from the top down: bit 64+i set  =>  XOR in (x^64 + 27) << i).
static FORCE_INLINE uint64_t chg_reduce_serial( chg_v128 r ) {
    for (int i = 63; i >= 0; i--) {
        if ((r.hi >> i) & 1) {
            r.hi ^= UINT64_C(1) << i;
            r.lo ^= UINT64_C(27) << i;
            if (i > 0) { r.hi ^= UINT64_C(27) >> (64 - i); }
        }
    }
    return r.lo;
}

static FORCE_INLINE uint64_t chg_gfmul( uint64_t a, uint64_t b ) {
    return chg_reduce_serial(chg_clmul_serial(a, b));
}

template <bool bswap>
static FORCE_INLINE void chg_ph_group( const uint64_t * k, const uint8_t * p, chg_v128 & acc0,
        chg_v128 & acc1 ) {
    acc0 = chg_v_xor(acc0, chg_v_clmulpair(chg_v_loadpair<bswap>(p +  0, k + 0)));
    acc1 = chg_v_xor(acc1, chg_v_clmulpair(chg_v_loadpair<bswap>(p + 16, k + 2)));
    acc0 = chg_v_xor(acc0, chg_v_clmulpair(chg_v_loadpair<bswap>(p + 32, k + 4)));
    acc1 = chg_v_xor(acc1, chg_v_clmulpair(chg_v_loadpair<bswap>(p + 48, k + 6)));
}

typedef uint64_t chg_gf;

static FORCE_INLINE chg_gf chg_gf_from( uint64_t x ) { return x; }
static FORCE_INLINE chg_gf chg_gf_hi( uint64_t x ) { return x; }
static FORCE_INLINE uint64_t chg_gf_to( chg_gf v ) { return v; }
static FORCE_INLINE chg_gf chg_gf_xor( chg_gf a, chg_gf b ) { return a ^ b; }
static FORCE_INLINE chg_gf chg_gf_mul( chg_gf a, chg_gf b ) { return chg_gfmul(a, b); }
static FORCE_INLINE chg_gf chg_gf_addint( chg_gf a, uint64_t x ) { return a + x; }

static FORCE_INLINE chg_v128 chg_gf_mulraw( chg_gf a, chg_gf b ) {
    return chg_clmul_serial(a, b);
}

static FORCE_INLINE chg_gf chg_gf_reduce_add( chg_v128 ab, chg_gf add ) {
    return chg_reduce_serial(ab) ^ add;
}

static FORCE_INLINE void chg_gf_reduce_add2( chg_v128 ab, chg_gf add0, chg_gf add1,
        chg_gf & o0, chg_gf & o1 ) {
    const uint64_t r = chg_reduce_serial(ab);

    o0 = r ^ add0;
    o1 = r ^ add1;
}

static FORCE_INLINE chg_gf chg_recur( chg_gf P, chg_v128 acc, chg_gf Yhi, chg_gf U ) {
    return acc.lo ^ chg_gfmul(acc.hi ^ Yhi, P ^ U);
}

#endif

//------------------------------------------------------------
// Whole and partial pairs on the backends without a byte-permute unit:
// one loadpair for a whole pair, a 16-byte zero-padded stack copy for the
// partial pair.  Reads exactly the bytes of the pair.

#if !defined(CHG_IMPL_ARM)

template <bool bswap>
static FORCE_INLINE chg_v128 chg_ph_pair( const uint64_t * k, const uint8_t * p ) {
    return chg_v_clmulpair(chg_v_loadpair<bswap>(p, k));
}

template <bool bswap>
static FORCE_INLINE chg_v128 chg_ph_partial_end( const uint64_t * k, const uint8_t * end, size_t r ) {
    alignas(16) uint8_t buf[16];

    memset(buf, 0, 16);
    memcpy(buf, end - r, r);
    return chg_v_clmulpair(chg_v_loadpair<bswap>(buf, k));
}

template <bool bswap>
static FORCE_INLINE chg_v128 chg_ph_small( const uint64_t * k, const uint8_t * m, size_t r ) {
    return chg_ph_partial_end<bswap>(k, m + r, r);
}

#endif

//------------------------------------------------------------
// PH level (backend independent from here on)

// Full (sub-)block of 8*WORDS bytes at blk (WORDS a multiple of 8):
//   XOR_{i < WORDS/2} clmul64(w[2i] ^ k[2i], w[2i+1] ^ k[2i+1])
template <int WORDS, bool bswap>
static FORCE_INLINE chg_v128 chg_ph_block( const uint64_t * k, const uint8_t * blk ) {
    chg_v128 acc0 = chg_v_zero(), acc1 = chg_v_zero();

    for (int i = 0; i < WORDS; i += 8) {
        chg_ph_group<bswap>(k + i, blk + 8 * i, acc0, acc1);
    }
    return chg_v_xor(acc0, acc1);
}

// Partial last (sub-)block: rem < 8*WORDS bytes at p, W' = ceil(rem/16)
// pairs, the final partial pair zero-padded to 16 bytes.  Full 64-byte
// groups in place, then whole 16-byte pairs in place, then the partial
// pair through chg_ph_partial_end -- whose PMULL-backend
// precondition (16 readable bytes ending at p + rem) holds because p + rem
// is the end of a message of >= 16 bytes on every call below.
template <int WORDS, bool bswap>
static FORCE_INLINE chg_v128 chg_ph_tail( const uint64_t * k, const uint8_t * p, size_t rem ) {
    chg_v128 acc0 = chg_v_zero(), acc1 = chg_v_zero();
    size_t pos = 0; // bytes consumed; word index = pos / 8

    for (; pos + 64 <= rem; pos += 64) {
        chg_ph_group<bswap>(k + pos / 8, p + pos, acc0, acc1);
    }
    chg_v128 acc = chg_v_xor(acc0, acc1);
    for (; pos + 16 <= rem; pos += 16) {
        acc = chg_v_xor(acc, chg_ph_pair<bswap>(k + pos / 8, p + pos));
    }
    if (pos < rem) {
        acc = chg_v_xor(acc, chg_ph_partial_end<bswap>(k + pos / 8, p + rem, rem - pos)); // 1..15 bytes
    }
    return acc;
}

// PH sum of a message of len <= 8*WORDS bytes that is the whole
// (sub-)block: the block, a tail, one zero-padded pair, or nothing.  Reads
// only [m, m + len).
template <int WORDS, bool bswap>
static FORCE_INLINE chg_v128 chg_ph_first( const uint64_t * k, const uint8_t * m, size_t len ) {
    if (len >= 16) {
        return (len == 8 * (size_t)WORDS) ? chg_ph_block<WORDS, bswap>(k, m) : chg_ph_tail<WORDS, bswap>(k, m, len);
    }
    if (len > 0) {
        return chg_ph_small<bswap>(k, m, len);
    }
    return chg_v_zero();
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
struct chg_finalize;

template <>
struct chg_finalize<5> {
    static FORCE_INLINE chg_gf apply( const uint64_t * c, chg_gf v ) {
        const chg_gf   C0 = chg_gf_from(c[0]), C1 = chg_gf_from(c[1]), C2 = chg_gf_from(c[2]);
        const chg_gf   C3 = chg_gf_from(c[3]), C4 = chg_gf_from(c[4]);
        const chg_v128 xx = chg_gf_mulraw(v, v);                                       // x x, unreduced
        chg_gf yc0, xyc1;

        chg_gf_reduce_add2(xx, C0, chg_gf_xor(v, C1), yc0, xyc1);                      // y + c0,  x + y + c1
        const chg_gf zc3 = chg_gf_reduce_add(chg_gf_mulraw(yc0, xyc1), C3);      // (y + c0)(x + y + c1) + c3
        return chg_gf_reduce_add(chg_gf_mulraw(chg_gf_xor(v, C2), zc3), C4);     // (x + c2)(z + c3) + c4
    }
};

//------------------------------------------------------------
// Seeding: derive the key from the 64-bit seed, fill in the derived
// values, and stash it in thread-local storage; the hash function receives
// the pointer.  Derivation order: k[0..BLOCK_WORDS), u, y, z, c[0..K), t_in.

template <int BLOCK_WORDS, int K>
static void chg_key_setup( chg_key<BLOCK_WORDS, K> & key ) {
    const uint64_t zu  = key.z ^ key.u;
    const uint64_t yzu = chg_gf_to(chg_gf_mul(chg_gf_from(key.y), chg_gf_from(zu)));

    key.uy[0]   = key.u;    key.uy[1]   = key.y;
    key.yhi[0]  = 0;        key.yhi[1]  = key.y;
    key.zuzu[0] = zu;       key.zuzu[1] = zu;
    key.yyzu[0] = key.y;    key.yyzu[1] = yzu;
    key.tin[0]  = key.t_in; key.tin[1]  = 0;
    key.yzu     = yzu;
    key.yyzu_yu = chg_gf_to(chg_gf_mul(chg_gf_from(key.y), chg_gf_from(yzu))) ^
                  chg_gf_to(chg_gf_mul(chg_gf_from(key.y), chg_gf_from(key.u)));
}

template <int BLOCK_WORDS, int K, int FIN>
static uintptr_t chg_seed_init( const seed_t seed ) {
    static thread_local chg_key<BLOCK_WORDS, K> key;
    uint64_t s = (uint64_t)seed;

    for (int i = 0; i < BLOCK_WORDS; i++) {
        key.k[i] = chg_splitmix64(s);
    }
    key.u = chg_splitmix64(s);
    key.y = chg_splitmix64(s);
    key.z = chg_splitmix64(s);
    for (int i = 0; i < K; i++) {
        key.c[i] = chg_splitmix64(s);
    }
    key.t_in = chg_splitmix64(s);
    for (int i = 0; i < 5; i++) { key.g[i] = 0; key.ng[i] = CHG_GL_P; }
    for (int i = 0; i < (FIN == CHG_FIN_G4 ? 4 : FIN == CHG_FIN_G5 ? 5 : 0); i++) {
        key.g[i]  = chg_gl_uniform(&s);
        key.ng[i] = CHG_GL_P - key.g[i];
    }
    chg_key_setup(key);
    return (uintptr_t)&key;
}

//------------------------------------------------------------
// The hash function ignores the seed value, because it uses a separate
// seeding function; the seed argument is the pointer returned by it.
//
// S = sub-block split: each block is processed as S contiguous sub-blocks
// of BLOCK_WORDS/S words (keys k[i*BLOCK_WORDS/S ..)), each giving its own
// (a, b) pair and recurrence step, in order.  In the last block the pairs
// of data (the zero-padded partial pair included) belong to whichever
// sub-block they fall in; sub-blocks beyond the data contribute (0, 0).
// The length goes into the a of the very last pair.  S = 1 is the
// one-pair-per-block function.

// The selected finalizer on the chain value P_n: the 64-bit hash.
//   CHAR2: the shipped twist + degree-5 circuit (backend-specific below);
//   G4 / G5: lane 0 out, fold into F_p, scalar circuit (backend independent).
template <int FIN>
struct chg_fin;

template <>
struct chg_fin<CHG_FIN_G4> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gl_fin_g4(key->g, key->ng, chg_gl_fold(chg_gf_to(P)));
    }
};

template <>
struct chg_fin<CHG_FIN_G5> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gl_fin_g5(key->g, key->ng, chg_gl_fold(chg_gf_to(P)));
    }
};

#if !defined(CHG_IMPL_PORTABLE)

template <>
struct chg_fin<CHG_FIN_CHAR2> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gf_to(chg_finalize<K>::apply(key->c, chg_v_add64(P, chg_v_load2(key->tin))));   // chain(c, P + t_in)
    }
};

// Recurrence step on the state Q = P + u:  Q_i = (a_i + u) + (b_i + y) Q_{i-1},
// i.e. step_q(Q, t) = t[0] + t[1] Q with t = [a + u, b + y] = acc ^ uy; the
// very last step takes t = [a + len, b + y] (no u) and then yields P_n
// itself.  The addend t is folded into the product's reduction.
static FORCE_INLINE chg_gf chg_step_q( chg_gf Q, chg_v128 t ) {
    return chg_gf_reduce_add(chg_v_clmul_hl(t, Q), t);
}

// len <= sub-block bytes: all data sits in sub-block 0 of the only block,
// sub-blocks 1..S-1 are empty.  No loop, no length bookkeeping: the
// key-only parts of the S recurrence steps are constants of the key.
// Returns the finished hash in lane 0.
template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static FORCE_INLINE uint64_t chg_small_v( const chg_key<BLOCK_WORDS, K> * key, const uint8_t * p,
        const size_t len ) {
    constexpr int SW = BLOCK_WORDS / S;                                                 // words per sub-block
    const chg_v128 acc = chg_ph_first<SW, bswap>(key->k, p, len);         // [a, b]
    chg_gf P;                                                                     // P_S, lane 0

    if (S == 1) {
        // P_1 = a + len + (b + y)(z + u) = (a + len + y(z+u)) + b (z+u): one high-half product on the accumulator
        P = chg_gf_reduce_add(chg_v_clmul_hh(acc, chg_v_load2(key->zuzu)),
                chg_v_xor(acc, chg_gf_from((uint64_t)len ^ key->yzu)));
    } else if (S == 2) {
        // P_2 = len + y (P_1 + u) = (len + yu + yy(z+u)) + a y + b y(z+u): two independent products, one reduction
        const chg_v128 YYZU = chg_v_load2(key->yyzu);
        const chg_v128 pr   = chg_v_xor(chg_gf_mulraw(acc, YYZU), chg_v_clmul_hh(acc, YYZU));
        P = chg_gf_reduce_add(pr, chg_gf_from((uint64_t)len ^ key->yyzu_yu));
    } else {
        const chg_v128 UY = chg_v_load2(key->uy);
        chg_gf Q = chg_step_q(chg_v_load2(key->zuzu), chg_v_xor(acc, UY)); // sub-block 0
        for (int i = 1; i + 1 < S; i++) {
            Q = chg_step_q(Q, UY);                                                        // empty: (a, b) = (0, 0)
        }
        P = chg_step_q(Q, chg_gf_xor(chg_v_load2(key->yhi), chg_gf_from((uint64_t)len))); // last, empty
    }
    return chg_fin<FIN>::apply(key, P);   // the selected finalizer on P_S
}

// len > sub-block bytes.  Blocks 0..n-2 are full and need no length logic
// (state Q = P + u); the last block is peeled and does the sub-block
// selects once, its final step taking [a + len, b + y] and yielding P_n
// directly.  Out of line and reached by a tail call, so that ChainHash
// below is a leaf (no frame, no callee-saved spills) on every key that
// fits one sub-block.
template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static NEVER_INLINE void chg_multi( const chg_key<BLOCK_WORDS, K> * key, const uint8_t * p,
        const size_t len, void * out ) {
    constexpr size_t BB = 8 * (size_t)BLOCK_WORDS;               // bytes per block
    constexpr int    SW = BLOCK_WORDS / S;                        // words per sub-block
    constexpr size_t SB = 8 * (size_t)SW;                         // bytes per sub-block
    const size_t n = (len + BB - 1) / BB;                         // >= 1 blocks (len > SB > 0)
    const chg_v128 UY = chg_v_load2(key->uy);
    chg_gf Q = chg_v_load2(key->zuzu);                // Q_0 = P_0 + u = z + u (lane 0)

    for (size_t j = 0; j + 1 < n; j++) {
        const uint8_t * blk = p + j * BB;
        for (int i = 0; i < S; i++) {
            Q = chg_step_q(Q, chg_v_xor(chg_ph_block<SW, bswap>(key->k + i * SW, blk + i * SB), UY));
        }
    }
    const size_t off = (n - 1) * BB;
    const size_t rem = len - off;                                 // bytes of input in the last block: 1..BB
    for (int i = 0; i < S; i++) {
        const size_t soff = (size_t)i * SB;                                                  // sub-block start within the block
        const size_t srem = (rem > soff) ? ((rem - soff < SB) ? rem - soff : SB) : 0;         // bytes of input in this sub-block
        chg_v128 acc;
        if (srem >= SB) {
            acc = chg_ph_block<SW, bswap>(key->k + i * SW, p + off + soff);            // full sub-block
        } else if (srem > 0) {
            acc = chg_ph_tail<SW, bswap>(key->k + i * SW, p + off + soff, srem);       // W' = ceil(srem/16) pairs; ends at p + len, len > SB >= 16
        } else {
            acc = chg_v_zero();                                                        // no data: empty PH sum
        }
        if (i + 1 < S) {
            Q = chg_step_q(Q, chg_v_xor(acc, UY));
        } else {                                                                             // [a + len, b + y] (no u): Q = P_n
            Q = chg_step_q(Q, chg_v_xor(acc, chg_gf_xor(chg_v_load2(key->yhi), chg_gf_from((uint64_t)len))));
        }
    }
    PUT_U64<bswap>(chg_fin<FIN>::apply(key, Q), (uint8_t *)out, 0);   // the selected finalizer on P_n
}

template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static void ChainHashG( const void * in, const size_t len, const seed_t seed, void * out ) {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
            "BLOCK_WORDS must be a positive multiple of 8*S (4 pairs per inner iteration, per sub-block)");
    static_assert(K == 5, "only the degree-5 finalizer is shipped");
    static_assert(FIN == CHG_FIN_CHAR2 || FIN == CHG_FIN_G4 || FIN == CHG_FIN_G5, "FIN must be CHAR2, G4 or G5");

    const chg_key<BLOCK_WORDS, K> * key = (const chg_key<BLOCK_WORDS, K> *)(uintptr_t)seed;
    const uint8_t * p = (const uint8_t *)in;
    constexpr size_t SB = 8 * (size_t)(BLOCK_WORDS / S);          // bytes per sub-block

    if (unlikely(len > SB)) {
        return chg_multi<BLOCK_WORDS, K, S, FIN, bswap>(key, p, len, out);   // tail call
    }
    PUT_U64<bswap>(chg_small_v<BLOCK_WORDS, K, S, FIN, bswap>(key, p, len), (uint8_t *)out, 0);
}

#else // CHG_IMPL_PORTABLE: the definition, evaluated literally

template <>
struct chg_fin<CHG_FIN_CHAR2> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gf_to(chg_finalize<K>::apply(key->c, chg_gf_addint(P, key->t_in)));   // chain(c, P + t_in)
    }
};

template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static void ChainHashG( const void * in, const size_t len, const seed_t seed, void * out ) {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
            "BLOCK_WORDS must be a positive multiple of 8*S (4 pairs per inner iteration, per sub-block)");
    static_assert(K == 5, "only the degree-5 finalizer is shipped");

    const chg_key<BLOCK_WORDS, K> * key = (const chg_key<BLOCK_WORDS, K> *)(uintptr_t)seed;
    const uint8_t * p = (const uint8_t *)in;
    const size_t BB   = 8 * (size_t)BLOCK_WORDS;
    constexpr int SW  = BLOCK_WORDS / S;                       // words per sub-block
    const size_t SB   = 8 * (size_t)SW;                        // bytes per sub-block (== BB for S = 1)
    const size_t n    = (len == 0) ? 1 : (len + BB - 1) / BB; // n = max(1, ceil(len/BB))
    // (len, 0) as a canonical little-endian pair, loaded through loadpair<false> with a zero key
    alignas(16) uint8_t  lenpad[16];
    alignas(16) const uint64_t zeropad[2] = { 0, 0 };
    PUT_U64<false>((uint64_t)len, lenpad, 0);
    PUT_U64<false>(UINT64_C(0), lenpad, 8);

    const chg_gf Yhi = chg_gf_hi(key->y);
    const chg_gf U   = chg_gf_from(key->u);
    chg_gf P = chg_gf_from(key->z); // P_0 = z
    for (size_t j = 0; j < n; j++) {
        const size_t off = j * BB;
        const size_t rem = len - off; // bytes of input in this block (0 only if len == 0)
        for (int i = 0; i < S; i++) {
            const size_t soff = (size_t)i * SB;                                          // sub-block start within the block
            const size_t srem = (rem > soff) ? ((rem - soff < SB) ? rem - soff : SB) : 0; // bytes of input in this sub-block
            chg_v128 acc;
            if (srem >= SB) {
                acc = chg_ph_block<SW, bswap>(key->k + i * SW, p + off + soff);      // full sub-block
            } else if (srem > 0) {
                acc = chg_ph_tail<SW, bswap>(key->k + i * SW, p + off + soff, srem); // W' = ceil(srem/16) pairs
            } else {
                acc = chg_v_zero();                                                 // no data: empty PH sum
            }
            if ((j + 1 == n) && (i + 1 == S)) {                                          // length into the last pair's a
                acc = chg_v_xor(acc, chg_v_loadpair<false>((const uint8_t *)&lenpad[0], &zeropad[0]));
            }
            P = chg_recur(P, acc, Yhi, U);                                         // P_m = a_m + (b_m + y)(P_{m-1} + u)
        }
    }

    PUT_U64<bswap>(chg_fin<FIN>::apply(key, P), (uint8_t *)out, 0);   // the selected finalizer on P_n
}

#endif

//------------------------------------------------------------
#if defined(CHG_IMPL_PORTABLE)
  #define CHG_IMPL_FLAGS   \
        FLAG_IMPL_MULTIPLY_64_64 | \
        FLAG_IMPL_LICENSE_BSD    | \
        FLAG_IMPL_VERY_SLOW
#else
  #define CHG_IMPL_FLAGS   \
        FLAG_IMPL_MULTIPLY_64_64 | \
        FLAG_IMPL_LICENSE_BSD
#endif

REGISTER_FAMILY(chainhash_goldi,
   $.src_status = HashFamilyInfo::SRC_ACTIVE
 );

REGISTER_HASH(chainhash_g4_256,
   $.desc       = "ChainHash EXPERIMENT: carry-less PH + three-key injective chain + Goldilocks-field Motzkin quartic finalizer (2 mults, 4-wise), 256-byte blocks",
   $.impl       = CHG_IMPL_STR,
   $.hash_flags =
         FLAG_HASH_CLMUL_BASED,
   $.impl_flags =
         CHG_IMPL_FLAGS,
   $.bits = 64,
   $.verification_LE = 0xA3577E75,
   $.verification_BE = 0xAE143AED,
   $.seedfn          = chg_seed_init<32, 5, CHG_FIN_G4>,
   $.hashfn_native   = ChainHashG<32, 5, 1, CHG_FIN_G4, false>,
   $.hashfn_bswap    = ChainHashG<32, 5, 1, CHG_FIN_G4, true>
 );

REGISTER_HASH(chainhash_g5_256,
   $.desc       = "ChainHash EXPERIMENT: carry-less PH + three-key injective chain + Goldilocks-field degree-5 finalizer (3 mults, 5-wise), 256-byte blocks",
   $.impl       = CHG_IMPL_STR,
   $.hash_flags =
         FLAG_HASH_CLMUL_BASED,
   $.impl_flags =
         CHG_IMPL_FLAGS,
   $.bits = 64,
   $.verification_LE = 0xF89E636F,
   $.verification_BE = 0x229C22B5,
   $.seedfn          = chg_seed_init<32, 5, CHG_FIN_G5>,
   $.hashfn_native   = ChainHashG<32, 5, 1, CHG_FIN_G5, false>,
   $.hashfn_bswap    = ChainHashG<32, 5, 1, CHG_FIN_G5, true>
 );

REGISTER_HASH(chainhash_g5_1k,
   $.desc       = "ChainHash EXPERIMENT: carry-less PH + three-key injective chain + Goldilocks-field degree-5 finalizer (3 mults, 5-wise), 1024-byte blocks, 2 sub-blocks per block",
   $.impl       = CHG_IMPL_STR,
   $.hash_flags =
         FLAG_HASH_CLMUL_BASED,
   $.impl_flags =
         CHG_IMPL_FLAGS,
   $.bits = 64,
   $.verification_LE = 0xC8B38421,
   $.verification_BE = 0x6024310F,
   $.seedfn          = chg_seed_init<128, 5, CHG_FIN_G5>,
   $.hashfn_native   = ChainHashG<128, 5, 2, CHG_FIN_G5, false>,
   $.hashfn_bswap    = ChainHashG<128, 5, 2, CHG_FIN_G5, true>
 );
