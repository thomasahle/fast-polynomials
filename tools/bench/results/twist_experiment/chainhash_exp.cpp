/*
 * ChainHash -- EXPERIMENTAL finalizer variants (degree 3/5/7, integer-add twists)
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
 *   3. A degree-7 finalizer with 7 uniformly random parameters c[]: the
 *      certified characteristic-2 degree-7 circuit (website/js/char2.js
 *      CIRCUITS[7] of the paper's repository), 4 field multiplications.
 *      It is a monic degree-7 polynomial in P whose lower coefficients
 *      are a bijection of c[] over every GF(2^k) (explicit decoder with
 *      unit pivots and two square roots), so the finalizer is a uniformly
 *      random monic degree-7 polynomial.
 *
 * The key (k[0..BLOCK_WORDS), u, y, z, c[0..7)) is derived from the 64-bit
 * seed with splitmix64 in that order.  It does not depend on S.
 *
 * Shipped configurations (of chainhash.cpp; this file registers the
 * experimental chainhash-exp-* variants, all BLOCK_WORDS = 32, S = 1):
 *   chainhash-256:  BLOCK_WORDS = 32  (256-byte blocks), S = 1
 *   chainhash-1k:   BLOCK_WORDS = 128 (1 KB blocks),     S = 2
 *
 * Reference implementation and analysis: T. D. Ahle, "Fast Evaluation of
 * Polynomials with Rational Preprocessing", bench/chainhash/chainhash_ref.h.
 *
 * Three carry-less multiply backends are provided and selected at compile
 * time: x86-64 PCLMULQDQ, AArch64 PMULL, and a portable bit-serial
 * fallback.  All three compute the identical function.
 *
 * ---------------------------------------------------------------------
 * THIS FILE (chainhash_exp.cpp) is an EXPERIMENT, not a shipped hash.
 * It is a copy of chainhash.cpp (identifiers prefixed chx_ to avoid any
 * ODR clash) whose finalizer degree K is a template parameter in {3,5,7}
 * and which can compose the finalizer with two fixed bijections:
 *
 *   TWIST_IN :  v  <-  v + t_in   (INTEGER 64-bit addition, carries and
 *               all, on lane 0) before the GF(2^64) finalizer;
 *   TWIST_OUT:  h  <-  h + t_out  (integer addition) after it.
 *
 * t_in and t_out are two further splitmix64 words derived AFTER c[], so
 * the K = 7 no-twist instance is bit-identical to chainhash-256.  Any
 * bijection of the finalizer input or output preserves k-wise
 * independence exactly, while the integer carries raise the GF(2)-degree
 * of the composite map (over GF(2^64) a degree <= 6 polynomial in v is
 * only quadratic in the bits of v, which is what the untwisted degree-3
 * and degree-5 finalizers failed SMHasher3 on).
 *
 * The degree-3 and degree-5 finalizers are the certified char-2 circuits
 * CIRCUITS[3] and CIRCUITS[5] of website/js/char2.js (paper repository),
 * both with unitriangular (hence bijective) coefficient maps:
 *   K = 3 (2 mults, 3 keys):  y = x x;  z = (x + c0)(x + y + c1);  out = z + c2
 *   K = 5 (3 mults, 5 keys):  y = x x;  z = (y + c0)(x + y + c1);
 *                             t = (x + c2)(z + c3);  out = t + c4
 * ---------------------------------------------------------------------
 */
#include "Platform.h"
#include "Hashlib.h"

//------------------------------------------------------------
// Backend selection.
//
//   CHX_IMPL_X86       x86-64 PCLMULQDQ (_mm_clmulepi64_si128)
//   CHX_IMPL_ARM       AArch64 PMULL (vmull_p64).  Only used when the
//                            compiler advertises the AES/crypto feature
//                            (__ARM_FEATURE_AES / __ARM_FEATURE_CRYPTO) or
//                            SMHasher3 detected it (HAVE_ARM_AES).
//   CHX_IMPL_PORTABLE  bit-serial fallback; always compiles.
//
// Define CHX_FORCE_PORTABLE to select the fallback regardless of
// what the platform supports (used for cross-checking the backends).
#if !defined(CHX_FORCE_PORTABLE) && defined(HAVE_X86_64_CLMUL)
  #include "Intrinsics.h"
  #define CHX_IMPL_X86 1
  #define CHX_IMPL_STR "hwclmul"
#elif !defined(CHX_FORCE_PORTABLE) &&                       \
      (defined(__aarch64__) || defined(_M_ARM64)) &&               \
      (defined(__ARM_FEATURE_AES) || defined(__ARM_FEATURE_CRYPTO) || defined(HAVE_ARM_AES))
  #if defined(HAVE_ARM_NEON)
    #include "Intrinsics.h"
  #else
    #include <arm_neon.h>
  #endif
  #define CHX_IMPL_ARM 1
  #define CHX_IMPL_STR "hwpmull"
#else
  #define CHX_IMPL_PORTABLE 1
  #define CHX_IMPL_STR "portable"
#endif

//------------------------------------------------------------
// Key material.  k[] is the PH key; u, y, z the recurrence keys
// (P_0 = z, P_j = a_j + (b_j + y)(P_{j-1} + u)); c[] the finalizer parameters.

template <int BLOCK_WORDS, int K>
struct chx_key {
    alignas(16) uint64_t k[BLOCK_WORDS];
    uint64_t u, y, z;
    uint64_t c[K];
    uint64_t tin, tout;   // twist words, derived after c[] (unused unless TWIST_IN / TWIST_OUT)
};

static FORCE_INLINE uint64_t chx_splitmix64( uint64_t & state ) {
    uint64_t z = (state += UINT64_C(0x9E3779B97F4A7C15));

    z = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
    z = (z ^ (z >> 27)) * UINT64_C(0x94D049BB133111EB);
    return z ^ (z >> 31);
}

//------------------------------------------------------------
// Backend primitives.  Every backend provides
//
//   chx_v128                 a 128-bit accumulator type
//   chx_v_zero()             all-zero accumulator
//   chx_v_xor(a, b)
//   chx_v_loadpair<bswap>(p, k)
//        (w0 ^ k[0], w1 ^ k[1]) with w0, w1 the little-endian 64-bit words
//        at p, p + 8 (GET_U64<bswap>, so big-endian builds agree)
//   chx_v_clmulpair(t)       clmul64(lane0(t), lane1(t)), unreduced
//   chx_ph_group<bswap>(k, p, acc0, acc1)
//        four pairs XORed into two accumulators
//   chx_gf                   a field element of GF(2^64) held in a
//        register: lane 0 of a vector on the SIMD backends (lane 1 is
//        garbage that nothing reads), a uint64_t on the portable one.
//        Keeping the recurrence and the finalizer in vector registers
//        avoids a GPR<->SIMD round trip per multiply.
//   chx_gf_from(x) / chx_gf_to(v) / chx_gf_hi(x)
//        x in lane 0 / lane 0 out / x in lane 1 (lane 0 zero)
//   chx_gf_xor(a, b), chx_gf_mul(a, b)
//        a * b in GF(2^64), reduction constant 27
//   chx_recur(P, acc, Yhi, U)
//        one recurrence step: a + (b + y)(P + u) with (a, b) the two
//        halves of the accumulator acc, Yhi = gf_hi(y), U = gf_from(u)

#if defined(CHX_IMPL_X86)

typedef __m128i chx_v128;

static FORCE_INLINE chx_v128 chx_v_zero( void ) {
    return _mm_setzero_si128();
}

static FORCE_INLINE chx_v128 chx_v_xor( chx_v128 a, chx_v128 b ) {
    return _mm_xor_si128(a, b);
}

template <bool bswap>
static FORCE_INLINE chx_v128 chx_v_loadpair( const uint8_t * p, const uint64_t * k ) {
    __m128i w = _mm_loadu_si128((const __m128i *)p);

    if (bswap) { w = mm_bswap64(w); }
    return _mm_xor_si128(w, _mm_loadu_si128((const __m128i *)k));
}

static FORCE_INLINE chx_v128 chx_v_clmulpair( chx_v128 t ) {
    return _mm_clmulepi64_si128(t, t, 0x10);
}

static FORCE_INLINE uint64_t chx_v_lo( chx_v128 v ) {
    return (uint64_t)_mm_cvtsi128_si64(v);
}

static FORCE_INLINE uint64_t chx_v_hi( chx_v128 v ) {
    return (uint64_t)_mm_cvtsi128_si64(_mm_srli_si128(v, 8));
}

template <bool bswap>
static FORCE_INLINE void chx_ph_group( const uint64_t * k, const uint8_t * p, chx_v128 & acc0,
        chx_v128 & acc1 ) {
    acc0 = chx_v_xor(acc0, chx_v_xor(chx_v_clmulpair(chx_v_loadpair<bswap>(p +  0, k + 0)),
                                                 chx_v_clmulpair(chx_v_loadpair<bswap>(p + 16, k + 2))));
    acc1 = chx_v_xor(acc1, chx_v_xor(chx_v_clmulpair(chx_v_loadpair<bswap>(p + 32, k + 4)),
                                                 chx_v_clmulpair(chx_v_loadpair<bswap>(p + 48, k + 6))));
}

// Field elements in lane 0 of an XMM register.  Reduction: one CLMUL for
// the product, two for the reduction (ab = x 2^64 + y;  xr = x*27 = z 2^64
// + t;  result = y ^ t ^ z*27); the immediate selects the high half, so no
// lane moves are needed.
typedef __m128i chx_gf;

static FORCE_INLINE chx_gf chx_gf_from( uint64_t x ) {
    return _mm_cvtsi64_si128((long long)x);
}

static FORCE_INLINE chx_gf chx_gf_hi( uint64_t x ) {
    return _mm_set_epi64x((long long)x, 0);
}

static FORCE_INLINE uint64_t chx_gf_to( chx_gf v ) {
    return (uint64_t)_mm_cvtsi128_si64(v);
}

static FORCE_INLINE chx_gf chx_gf_xor( chx_gf a, chx_gf b ) {
    return _mm_xor_si128(a, b);
}

// Twist: integer 64-bit addition of x to lane 0 (carries and all).
static FORCE_INLINE chx_gf chx_gf_addint( chx_gf a, uint64_t x ) {
    return _mm_add_epi64(a, _mm_cvtsi64_si128((long long)x));
}

static FORCE_INLINE chx_gf chx_gf_reduce( __m128i ab ) {
    const __m128i r  = _mm_set_epi64x(0, 27);
    const __m128i xr = _mm_clmulepi64_si128(ab, r, 0x01);
    const __m128i zr = _mm_clmulepi64_si128(xr, r, 0x01);

    return _mm_xor_si128(_mm_xor_si128(ab, xr), zr);
}

static FORCE_INLINE chx_gf chx_gf_mul( chx_gf a, chx_gf b ) {
    return chx_gf_reduce(_mm_clmulepi64_si128(a, b, 0x00));
}

// (a, b) = acc;  t = (a, b + y);  P' = a + (b + y)(P + u)  (lane 0)
static FORCE_INLINE chx_gf chx_recur( chx_gf P, chx_v128 acc, chx_gf Yhi, chx_gf U ) {
    const __m128i t  = _mm_xor_si128(acc, Yhi);
    const __m128i ab = _mm_clmulepi64_si128(t, _mm_xor_si128(P, U), 0x01);   // hi(t) * lo(P + u)

    return _mm_xor_si128(chx_gf_reduce(ab), t);
}

#elif defined(CHX_IMPL_ARM)

typedef uint64x2_t chx_v128;

static FORCE_INLINE chx_v128 chx_v_zero( void ) {
    return vdupq_n_u64(0);
}

static FORCE_INLINE chx_v128 chx_v_xor( chx_v128 a, chx_v128 b ) {
    return veorq_u64(a, b);
}

template <bool bswap>
static FORCE_INLINE chx_v128 chx_v_loadpair( const uint8_t * p, const uint64_t * k ) {
    uint8x16_t w = vld1q_u8(p);

    if (bswap) { w = vrev64q_u8(w); }
    return veorq_u64(vreinterpretq_u64_u8(w), vld1q_u64(k));
}

static FORCE_INLINE chx_v128 chx_v_clmulpair( chx_v128 t ) {
    const poly64x2_t pt = vreinterpretq_p64_u64(t);

    return vreinterpretq_u64_p128(vmull_p64(vgetq_lane_p64(pt, 0), vgetq_lane_p64(pt, 1)));
}

static FORCE_INLINE uint64_t chx_v_lo( chx_v128 v ) {
    return vgetq_lane_u64(v, 0);
}

static FORCE_INLINE uint64_t chx_v_hi( chx_v128 v ) {
    return vgetq_lane_u64(v, 1);
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
static FORCE_INLINE uint64x2_t chx_pmull_lo( uint64x2_t a, uint64x2_t b ) {
    return vreinterpretq_u64_p128(vmull_p64(vgetq_lane_p64(vreinterpretq_p64_u64(a), 0),
            vgetq_lane_p64(vreinterpretq_p64_u64(b), 0)));
}

static FORCE_INLINE uint64x2_t chx_pmull_hi( uint64x2_t a, uint64x2_t b ) {
    return vreinterpretq_u64_p128(vmull_high_p64(vreinterpretq_p64_u64(a), vreinterpretq_p64_u64(b)));
}
#else
static FORCE_INLINE uint64x2_t chx_pmull_lo( uint64x2_t a, uint64x2_t b ) {
    uint64x2_t r;

    __asm__ ("pmull %0.1q, %1.1d, %2.1d" : "=w" (r) : "w" (a), "w" (b));
    return r;
}

static FORCE_INLINE uint64x2_t chx_pmull_hi( uint64x2_t a, uint64x2_t b ) {
    uint64x2_t r;

    __asm__ ("pmull2 %0.1q, %1.2d, %2.2d" : "=w" (r) : "w" (a), "w" (b));
    return r;
}
#endif

static FORCE_INLINE uint64x2_t chx_xor3( uint64x2_t a, uint64x2_t b, uint64x2_t c ) {
#if defined(__ARM_FEATURE_SHA3)
    return veor3q_u64(a, b, c);
#else
    return veorq_u64(veorq_u64(a, b), c);
#endif
}

// Four pairs: e01 = (t0[1], t1[0]) makes pmull(t0, e01) = t0[0] t0[1] and
// pmull2(e01, t1) = t1[0] t1[1], one EXT per two pairs and no DUPs.
template <bool bswap>
static FORCE_INLINE void chx_ph_group( const uint64_t * k, const uint8_t * p, chx_v128 & acc0,
        chx_v128 & acc1 ) {
    const uint64x2_t t0  = chx_v_loadpair<bswap>(p +  0, k + 0);
    const uint64x2_t t1  = chx_v_loadpair<bswap>(p + 16, k + 2);
    const uint64x2_t t2  = chx_v_loadpair<bswap>(p + 32, k + 4);
    const uint64x2_t t3  = chx_v_loadpair<bswap>(p + 48, k + 6);
    const uint64x2_t e01 = vextq_u64(t0, t1, 1);
    const uint64x2_t e23 = vextq_u64(t2, t3, 1);

    acc0 = chx_xor3(acc0, chx_pmull_lo(t0, e01), chx_pmull_hi(e01, t1));
    acc1 = chx_xor3(acc1, chx_pmull_lo(t2, e23), chx_pmull_hi(e23, t3));
}

// Field elements in lane 0 of a NEON register.  Reduction: one PMULL for
// the product, two PMULL2 for the reduction (ab = x 2^64 + y;  xr = x*27
// = z 2^64 + t;  result = y ^ t ^ z*27).
typedef uint64x2_t chx_gf;

static FORCE_INLINE chx_gf chx_gf_from( uint64_t x ) {
    return vcombine_u64(vcreate_u64(x), vcreate_u64(0));
}

static FORCE_INLINE chx_gf chx_gf_hi( uint64_t x ) {
    return vcombine_u64(vcreate_u64(0), vcreate_u64(x));
}

static FORCE_INLINE uint64_t chx_gf_to( chx_gf v ) {
    return vgetq_lane_u64(v, 0);
}

static FORCE_INLINE chx_gf chx_gf_xor( chx_gf a, chx_gf b ) {
    return veorq_u64(a, b);
}

// Twist: integer 64-bit addition of x to lane 0 (carries and all); lane 1 gets + 0.
static FORCE_INLINE chx_gf chx_gf_addint( chx_gf a, uint64_t x ) {
    return vaddq_u64(a, chx_gf_from(x));
}

static FORCE_INLINE chx_gf chx_gf_reduce( uint64x2_t ab ) {
    const uint64x2_t rr = vdupq_n_u64(27);
    const uint64x2_t xr = chx_pmull_hi(ab, rr);
    const uint64x2_t zr = chx_pmull_hi(xr, rr);

    return chx_xor3(ab, xr, zr);
}

static FORCE_INLINE chx_gf chx_gf_mul( chx_gf a, chx_gf b ) {
    return chx_gf_reduce(chx_pmull_lo(a, b));
}

// (a, b) = acc;  t = (a, b + y);  P' = a + (b + y)(P + u)  (lane 0)
static FORCE_INLINE chx_gf chx_recur( chx_gf P, chx_v128 acc, chx_gf Yhi, chx_gf U ) {
    const uint64x2_t t  = veorq_u64(acc, Yhi);
    const uint64x2_t ab = chx_pmull_lo(vextq_u64(t, t, 1), veorq_u64(P, U));   // (b + y)(P + u)

    return veorq_u64(chx_gf_reduce(ab), t);
}

#else // CHX_IMPL_PORTABLE

struct chx_v128 {
    uint64_t  lo;
    uint64_t  hi;
};

static FORCE_INLINE chx_v128 chx_v_zero( void ) {
    chx_v128 v = { 0, 0 };

    return v;
}

static FORCE_INLINE chx_v128 chx_v_xor( chx_v128 a, chx_v128 b ) {
    chx_v128 v = { a.lo ^ b.lo, a.hi ^ b.hi };

    return v;
}

template <bool bswap>
static FORCE_INLINE chx_v128 chx_v_loadpair( const uint8_t * p, const uint64_t * k ) {
    chx_v128 v = { GET_U64<bswap>(p, 0) ^ k[0], GET_U64<bswap>(p, 8) ^ k[1] };

    return v;
}

// 64x64 -> 128 carry-less product, bit by bit.
static FORCE_INLINE chx_v128 chx_clmul_serial( uint64_t a, uint64_t b ) {
    chx_v128 r = { 0, 0 };

    for (int i = 0; i < 64; i++) {
        const uint64_t m = UINT64_C(0) - ((b >> i) & 1);
        r.lo ^= (a << i) & m;
        if (i > 0) { r.hi ^= (a >> (64 - i)) & m; }
    }
    return r;
}

static FORCE_INLINE chx_v128 chx_v_clmulpair( chx_v128 t ) {
    return chx_clmul_serial(t.lo, t.hi);
}

static FORCE_INLINE uint64_t chx_v_lo( chx_v128 v ) {
    return v.lo;
}

static FORCE_INLINE uint64_t chx_v_hi( chx_v128 v ) {
    return v.hi;
}

// Reduce a 128-bit polynomial modulo x^64 + x^4 + x^3 + x + 1, bit by bit
// (from the top down: bit 64+i set  =>  XOR in (x^64 + 27) << i).
static FORCE_INLINE uint64_t chx_reduce_serial( chx_v128 r ) {
    for (int i = 63; i >= 0; i--) {
        if ((r.hi >> i) & 1) {
            r.hi ^= UINT64_C(1) << i;
            r.lo ^= UINT64_C(27) << i;
            if (i > 0) { r.hi ^= UINT64_C(27) >> (64 - i); }
        }
    }
    return r.lo;
}

static FORCE_INLINE uint64_t chx_gfmul( uint64_t a, uint64_t b ) {
    return chx_reduce_serial(chx_clmul_serial(a, b));
}

template <bool bswap>
static FORCE_INLINE void chx_ph_group( const uint64_t * k, const uint8_t * p, chx_v128 & acc0,
        chx_v128 & acc1 ) {
    acc0 = chx_v_xor(acc0, chx_v_clmulpair(chx_v_loadpair<bswap>(p +  0, k + 0)));
    acc1 = chx_v_xor(acc1, chx_v_clmulpair(chx_v_loadpair<bswap>(p + 16, k + 2)));
    acc0 = chx_v_xor(acc0, chx_v_clmulpair(chx_v_loadpair<bswap>(p + 32, k + 4)));
    acc1 = chx_v_xor(acc1, chx_v_clmulpair(chx_v_loadpair<bswap>(p + 48, k + 6)));
}

typedef uint64_t chx_gf;

static FORCE_INLINE chx_gf chx_gf_from( uint64_t x ) { return x; }
static FORCE_INLINE chx_gf chx_gf_hi( uint64_t x ) { return x; }
static FORCE_INLINE uint64_t chx_gf_to( chx_gf v ) { return v; }
static FORCE_INLINE chx_gf chx_gf_xor( chx_gf a, chx_gf b ) { return a ^ b; }
static FORCE_INLINE chx_gf chx_gf_addint( chx_gf a, uint64_t x ) { return a + x; }   // twist: integer add
static FORCE_INLINE chx_gf chx_gf_mul( chx_gf a, chx_gf b ) { return chx_gfmul(a, b); }

static FORCE_INLINE chx_gf chx_recur( chx_gf P, chx_v128 acc, chx_gf Yhi, chx_gf U ) {
    return acc.lo ^ chx_gfmul(acc.hi ^ Yhi, P ^ U);
}

#endif

//------------------------------------------------------------
// PH level (backend independent from here on)

// Full block of 8*BLOCK_WORDS bytes at blk:
//   XOR_{i < BLOCK_WORDS/2} clmul64(w[2i] ^ k[2i], w[2i+1] ^ k[2i+1])
template <int BLOCK_WORDS, bool bswap>
static FORCE_INLINE chx_v128 chx_ph_block( const uint64_t * k, const uint8_t * blk ) {
    chx_v128 acc0 = chx_v_zero(), acc1 = chx_v_zero();

    for (int i = 0; i < BLOCK_WORDS; i += 8) {
        chx_ph_group<bswap>(k + i, blk + 8 * i, acc0, acc1);
    }
    return chx_v_xor(acc0, acc1);
}

// Partial last block: rem < 8*BLOCK_WORDS bytes at p, W' = ceil(rem/16)
// pairs, the final partial pair zero-padded to 16 bytes.  Reads exactly
// rem bytes of p: full 64-byte groups in place, then whole 16-byte pairs
// in place, then the partial pair via a 16-byte stack copy.
template <int BLOCK_WORDS, bool bswap>
static FORCE_INLINE chx_v128 chx_ph_tail( const uint64_t * k, const uint8_t * p, size_t rem ) {
    chx_v128 acc0 = chx_v_zero(), acc1 = chx_v_zero();
    size_t pos = 0; // bytes consumed; word index = pos / 8

    for (; pos + 64 <= rem; pos += 64) {
        chx_ph_group<bswap>(k + pos / 8, p + pos, acc0, acc1);
    }
    chx_v128 acc = chx_v_xor(acc0, acc1);
    for (; pos + 16 <= rem; pos += 16) {
        acc = chx_v_xor(acc, chx_v_clmulpair(chx_v_loadpair<bswap>(p + pos, k + pos / 8)));
    }
    if (pos < rem) {
        alignas(16) uint8_t buf[16];
        memset(buf, 0, 16);
        memcpy(buf, p + pos, rem - pos);
        acc = chx_v_xor(acc, chx_v_clmulpair(chx_v_loadpair<bswap>(buf, k + pos / 8)));
    }
    return acc;
}

//------------------------------------------------------------
// Finalizer: the certified characteristic-2 degree-7 circuit (CIRCUITS[7]
// of website/js/char2.js in the paper's repository), transcribed gate by
// gate with x = the input v and keys c[0..7):
//     y = x (x + c0)
//     z = (x + c1)(y + c2)
//     t = z (z + c3)
//     u = (x + c4)(y + t + c5)
//   out = u + c6
// 4 multiplications; a MONIC degree-7 polynomial in x whose lower
// coefficients are a bijection of (c0..c6) over every GF(2^k) (rows x^6..x^0
// read c4, (c0+c1)^2, c3 + .., (c2+c0c1)^2 + .., c1 + .., c5 + .., c6 + ..;
// the site's decoder inverts them top-down with unit pivots and two square
// roots).  Same gate order as bench/chainhash/chainhash.h.

template <int K>
struct chx_finalize;

template <>
struct chx_finalize<7> {
    static FORCE_INLINE chx_gf apply( const uint64_t * c, chx_gf v ) {
        const chx_gf C0 = chx_gf_from(c[0]), C1 = chx_gf_from(c[1]), C2 = chx_gf_from(c[2]);
        const chx_gf C3 = chx_gf_from(c[3]), C4 = chx_gf_from(c[4]), C5 = chx_gf_from(c[5]);
        const chx_gf C6 = chx_gf_from(c[6]);
        const chx_gf y  = chx_gf_mul(v, chx_gf_xor(v, C0));                                    // x (x + c0)
        const chx_gf z  = chx_gf_mul(chx_gf_xor(v, C1), chx_gf_xor(y, C2));              // (x + c1)(y + c2)
        const chx_gf t  = chx_gf_mul(z, chx_gf_xor(z, C3));                                    // z (z + c3)
        const chx_gf u  = chx_gf_mul(chx_gf_xor(v, C4), chx_gf_xor(chx_gf_xor(y, t), C5)); // (x + c4)(y + t + c5)

        return chx_gf_xor(u, C6);
    }
};

// Degree-5 finalizer: CIRCUITS[5] of website/js/char2.js (= the first three
// gates of its COMMON6 prefix), transcribed gate by gate with x = v:
//     y = x x
//     z = (y + c0)(x + y + c1)
//     t = (x + c2)(z + c3)
//   out = t + c4
// 3 multiplications; MONIC degree 5 with a unitriangular coefficient map
// (rows x^4..x^0: 1 + c2, c0 + c1 + c2, c0 + c2(c0 + c1), c0c1 + c3 + c0c2,
// c2(c0c1 + c3) + c4), so (c0..c4) <-> lower coefficients is a bijection.

template <>
struct chx_finalize<5> {
    static FORCE_INLINE chx_gf apply( const uint64_t * c, chx_gf v ) {
        const chx_gf C0 = chx_gf_from(c[0]), C1 = chx_gf_from(c[1]), C2 = chx_gf_from(c[2]);
        const chx_gf C3 = chx_gf_from(c[3]), C4 = chx_gf_from(c[4]);
        const chx_gf y  = chx_gf_mul(v, v);                                                                 // x x
        const chx_gf z  = chx_gf_mul(chx_gf_xor(y, C0), chx_gf_xor(chx_gf_xor(v, y), C1));                  // (y + c0)(x + y + c1)
        const chx_gf t  = chx_gf_mul(chx_gf_xor(v, C2), chx_gf_xor(z, C3));                                 // (x + c2)(z + c3)

        return chx_gf_xor(t, C4);
    }
};

// Degree-3 finalizer: CIRCUITS[3] of website/js/char2.js:
//     y = x x
//     z = (x + c0)(x + y + c1)
//   out = z + c2
// 2 multiplications; MONIC degree 3, rows x^2..x^0: 1 + c0, c0 + c1,
// c0c1 + c2 (unitriangular, hence bijective).

template <>
struct chx_finalize<3> {
    static FORCE_INLINE chx_gf apply( const uint64_t * c, chx_gf v ) {
        const chx_gf C0 = chx_gf_from(c[0]), C1 = chx_gf_from(c[1]), C2 = chx_gf_from(c[2]);
        const chx_gf y  = chx_gf_mul(v, v);                                                                 // x x
        const chx_gf z  = chx_gf_mul(chx_gf_xor(v, C0), chx_gf_xor(chx_gf_xor(v, y), C1));                  // (x + c0)(x + y + c1)

        return chx_gf_xor(z, C2);
    }
};

//------------------------------------------------------------
// Seeding: derive the key from the 64-bit seed and stash it in
// thread-local storage; the hash function receives the pointer.
// Derivation order: k[0..BLOCK_WORDS), u, y, z, c[0..K), then the two twist
// words t_in, t_out (so the K = 7 untwisted key equals chainhash.cpp's).

template <int BLOCK_WORDS, int K>
static uintptr_t chx_seed_init( const seed_t seed ) {
    static thread_local chx_key<BLOCK_WORDS, K> key;
    uint64_t s = (uint64_t)seed;

    for (int i = 0; i < BLOCK_WORDS; i++) {
        key.k[i] = chx_splitmix64(s);
    }
    key.u = chx_splitmix64(s);
    key.y = chx_splitmix64(s);
    key.z = chx_splitmix64(s);
    for (int i = 0; i < K; i++) {
        key.c[i] = chx_splitmix64(s);
    }
    key.tin  = chx_splitmix64(s);
    key.tout = chx_splitmix64(s);
    return (uintptr_t)&key;
}

//------------------------------------------------------------
// This function ignores the seed value, because it uses a separate
// seeding function; the seed argument is the pointer returned by it.
//
// S = sub-block split: each block is processed as S contiguous sub-blocks
// of BLOCK_WORDS/S words (keys k[i*BLOCK_WORDS/S ..)), each giving its own
// (a, b) pair and recurrence step, in order.  In the last block the pairs
// of data (the zero-padded partial pair included) belong to whichever
// sub-block they fall in; sub-blocks beyond the data contribute (0, 0).
// The length goes into the a of the very last pair.  S = 1 is the
// one-pair-per-block function.

template <int BLOCK_WORDS, int K, int S, bool TWIST_IN, bool TWIST_OUT, bool bswap>
static void ChainHashExp( const void * in, const size_t len, const seed_t seed, void * out ) {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
            "BLOCK_WORDS must be a positive multiple of 8*S (4 pairs per inner iteration, per sub-block)");
    static_assert(K == 3 || K == 5 || K == 7, "finalizer degree K must be 3, 5 or 7");

    const chx_key<BLOCK_WORDS, K> * key = (const chx_key<BLOCK_WORDS, K> *)(uintptr_t)seed;
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

    const chx_gf Yhi = chx_gf_hi(key->y);
    const chx_gf U   = chx_gf_from(key->u);
    chx_gf P = chx_gf_from(key->z); // P_0 = z
    for (size_t j = 0; j < n; j++) {
        const size_t off = j * BB;
        const size_t rem = len - off; // bytes of input in this block (0 only if len == 0)
        for (int i = 0; i < S; i++) {
            const size_t soff = (size_t)i * SB;                                          // sub-block start within the block
            const size_t srem = (rem > soff) ? ((rem - soff < SB) ? rem - soff : SB) : 0; // bytes of input in this sub-block
            chx_v128 acc;
            if (srem >= SB) {
                acc = chx_ph_block<SW, bswap>(key->k + i * SW, p + off + soff);      // full sub-block
            } else if (srem > 0) {
                acc = chx_ph_tail<SW, bswap>(key->k + i * SW, p + off + soff, srem); // W' = ceil(srem/16) pairs
            } else {
                acc = chx_v_zero();                                                 // no data: empty PH sum
            }
            if ((j + 1 == n) && (i + 1 == S)) {                                          // length into the last pair's a
                acc = chx_v_xor(acc, chx_v_loadpair<false>((const uint8_t *)&lenpad[0], &zeropad[0]));
            }
            P = chx_recur(P, acc, Yhi, U);                                         // P_m = a_m + (b_m + y)(P_{m-1} + u)
        }
    }

    // Input twist: sigma(P) = P + t_in with INTEGER addition -- a fixed bijection
    // of the finalizer input, so k-wise independence is unchanged.
    const chx_gf v = TWIST_IN ? chx_gf_addint(P, key->tin) : P;
    uint64_t h = chx_gf_to(chx_finalize<K>::apply(key->c, v));
    // Output twist: integer addition of t_out (also a bijection).
    if (TWIST_OUT) { h += key->tout; }
    PUT_U64<bswap>(h, (uint8_t *)out, 0);
}

//------------------------------------------------------------
#if defined(CHX_IMPL_PORTABLE)
  #define CHX_IMPL_FLAGS   \
        FLAG_IMPL_MULTIPLY_64_64 | \
        FLAG_IMPL_LICENSE_BSD    | \
        FLAG_IMPL_VERY_SLOW
#else
  #define CHX_IMPL_FLAGS   \
        FLAG_IMPL_MULTIPLY_64_64 | \
        FLAG_IMPL_LICENSE_BSD
#endif

REGISTER_FAMILY(chainhash_exp,
   $.src_status = HashFamilyInfo::SRC_ACTIVE
 );

#define CHX_REGISTER(NAME, DESC, K, TIN, TOUT, VLE, VBE)                              \
REGISTER_HASH(NAME,                                                                    \
   $.desc       = DESC,                                                                \
   $.impl       = CHX_IMPL_STR,                                                        \
   $.hash_flags =                                                                      \
         FLAG_HASH_CLMUL_BASED,                                                        \
   $.impl_flags =                                                                      \
         CHX_IMPL_FLAGS,                                                               \
   $.bits = 64,                                                                        \
   $.verification_LE = VLE,                                                            \
   $.verification_BE = VBE,                                                            \
   $.seedfn          = chx_seed_init<32, K>,                                           \
   $.hashfn_native   = ChainHashExp<32, K, 1, TIN, TOUT, false>,                       \
   $.hashfn_bswap    = ChainHashExp<32, K, 1, TIN, TOUT, true>                         \
 )

// Control: identical to chainhash-256 (K = 7, no twists).
CHX_REGISTER(chainhash_exp_k7,
   "ChainHash EXPERIMENT control: degree-7 finalizer (4 mults), no twist; == chainhash-256",
   7, false, false, 0xCB0491AF, 0xE527D6A9);

CHX_REGISTER(chainhash_exp_k5,
   "ChainHash EXPERIMENT: degree-5 finalizer (3 mults), no twist",
   5, false, false, 0xA6F72889, 0x62BB874A);

CHX_REGISTER(chainhash_exp_k5_tin,
   "ChainHash EXPERIMENT: degree-5 finalizer (3 mults), integer-add input twist",
   5, true, false, 0xDE1AB9F9, 0xCA97ABE0);

CHX_REGISTER(chainhash_exp_k5_tin_tout,
   "ChainHash EXPERIMENT: degree-5 finalizer (3 mults), integer-add input + output twists",
   5, true, true, 0xB48D2403, 0x3C4F4FDB);

CHX_REGISTER(chainhash_exp_k3_tin,
   "ChainHash EXPERIMENT: degree-3 finalizer (2 mults), integer-add input twist",
   3, true, false, 0x996A2EAD, 0x8265E6CC);

CHX_REGISTER(chainhash_exp_k3_tin_tout,
   "ChainHash EXPERIMENT: degree-3 finalizer (2 mults), integer-add input + output twists",
   3, true, true, 0x0A7FFA9A, 0xC8BDE72C);
