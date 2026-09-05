/* ***********************************************
 * Hash functions:
 * This file define several hash functions as
 * classes.
 *
 * If DEBUG is defined it asserts that initialization
 * is done properly.
 * ***********************************************/

#ifndef _FAST_HASHING_H_
#define _FAST_HASHING_H_

#include <cstdint>
#include <type_traits>
#include <vector>

#ifdef DEBUG
#include <cassert>
#endif

#include "multiplication.h"
#include "randomgen.h"

#define upper(m) (_mm_srli_si128(m, 8))


using namespace std;

// Note: Knuth–Eve polynomial evaluation:
// Q(x) = Q1(x^2) + Q2(x^2)x
// Aka: Parity split. Similar to Estrin's scheme.
// Or maybe it's a bit more complicated, see
// "Data parallel evaluation of univariate polynomials
// by the Knuth-Eve algorithm"


/* ***************************************************
 * Normal polyhash, using horner.
 * Uses the smart, fast division method from the paper.
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
 * Mersenne polyhash, using horner
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

// Uses smart division for the last iteration
template <const int L>
class poly_64_2 {
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
    for (int i = 1; i < L-1; i++) {
      h = fast_large_mult_mod(h, m[i], x);
    }
    h = fast_large_mult_mod_exact(h, m[L-1], x);
    return h;
  }
};

// Let's see if clang can make as good code as me
template <std::size_t N>
class estrin_mers_gen {
  __uint128_t ms[N];

 public:
  void init() {
    for (int i = 0; i < N; i++)
      ms[i] = getRandomUInt128() >> 39;
  }
  uint64_t operator()(uint64_t x) {
    assert(N >= 2);
    if (N == 2)
       // FIXME: Needs to check for res >= P
       return extra_large_mult_add_mod(ms[0], x, ms[1]);

    __uint128_t ds[(N + 1) / 2];
#pragma unroll
    for (int i = 0; i < N / 2; i++) {
      ds[i] = fast_large_mult_mod(ms[2*i], x, ms[2*i+1]);
    }
    if ((N & 1) == 1) ds[N / 2] = ms[N - 1];
    int n = (N + 1) / 2;

#pragma unroll
    while (n > 2) {
      // This is the main issue with the "general" version.
      // We are introducing a particular order on the xs.
      x = extra_large_mult_add_mod(x, x, 0);
#pragma unroll
      for (int i = 0; i < n / 2; i++) {
        ds[i] = extra_large_mult_add_mod(ds[2*i], x, ds[2*i+1]);
      }
      if ((n & 1) == 1) ds[n / 2] = ds[n - 1];
      n = (n + 1) / 2;
    }

    assert(n == 2);
    // FIXME: Needs to check for res >= P
    return extra_large_mult_add_mod(ds[0], x, ds[1]);
  }
};

/* ***************************************************
 * N-wise independent hashing using mersenne and smart polynomials.
 * ***************************************************/

template <std::size_t N>
class smartpoly_64 {
  __uint128_t ms[N];
  constexpr static __uint128_t M89 = ((__uint128_t)1 << 89) - 1;

 public:
  void init() {
    for (int i = 0; i < N; i++) {
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
  }

 private:
  uint64_t mult2(uint64_t input) {
    assert(N == 2);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0); // y = (x + 0) * (x + a0);
    __uint128_t P = y + ms[1];                               // P = y + a1;
    // FIXME: This might even be wrong, since after adding ms[1], we could be larger than 2P...
    // Even if only by a little bit...
    // Maybe we have to change the extra_large_mult_mod to allow an added term that can be
    // incooperated in the mod. It's just annoying, since that's not how the current
    // polynomium generator works.
    // Also, we want to use the "exact" mod the last time - the one using "smart division".
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult3(uint64_t input) {
    assert(N == 3);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);     // y = (x + 0) * (x + a0);
    __uint128_t z = fast_large_mult_mod_2(x + y + ms[1], x + 0); // z = (x + y + a1) * (x + 0);
    __uint128_t P = z + ms[2];                                   // P = z + a2;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult4(uint64_t input) {
    assert(N == 4);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);        // y = (x + a0) * (x + 0);
    __uint128_t z = extra_large_mult_mod(y + ms[1], x + y + ms[2]); // z = (y + a1) * (x + y + a2);
    __uint128_t P = z + ms[3];                                      // P = z + a3;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult5(uint64_t input) {
    assert(N == 5);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);        // y = (x + 0) * (x + a0);
    __uint128_t z = extra_large_mult_mod(y + ms[1], x + y + ms[2]); // z = (y + a1) * (x + y + a2);
    __uint128_t t = fast_large_mult_mod_2(y + z + ms[3], x + 0);    // t = (y + z + a3) * (x + 0);
    __uint128_t P = t + ms[4];                                      // P = t + a4;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult6(uint64_t input) {
    assert(N == 6);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = fast_large_mult_mod_2(x + y + ms[1], x + 0);        // z = (x + 0) * (x + y + a1);
    __uint128_t t = extra_large_mult_mod(y + z + ms[2], x + z + ms[3]); // t = (y + z + a2) * (x + z + a3);
    __uint128_t u = fast_large_mult_mod_2(z + ms[4], x + 0);            // u = (x + 0) * (z + a4);
    __uint128_t P = t + u + ms[5];                                      // P = t + u + a5;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult7(uint64_t input) {
    assert(N == 7);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = extra_large_mult_mod(y + ms[1], x + ms[2]);         // z = (y + a1) * (x + a2);
    __uint128_t t = fast_large_mult_mod_2(z + ms[3], x + 0);            // t = (z + a3) * (x + 0);
    __uint128_t u = extra_large_mult_mod(z + ms[4], y + z + t + ms[5]); // u = (z + a4) * (y + z + t + a5);
    __uint128_t P = u + y + ms[6];                                      // P = u + y + a6;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult8(uint64_t input) {
    assert(N == 8);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = extra_large_mult_mod(y + ms[1], x + y + ms[2]);     // z = (y + a1) * (x + y + a2);
    __uint128_t t = fast_large_mult_mod_2(x + ms[3], x + 0);            // t = (x + 0) * (x + a3);
    __uint128_t u = extra_large_mult_mod(z + ms[4], y + z + t + ms[5]); // u = (z + a4) * (y + z + t + a5);
    __uint128_t v = fast_large_mult_mod_2(z + t + ms[6], x + 0);        // v = (z + t + a6) * (x + 0);
    __uint128_t P = u + v + z + ms[7];                                  // P = u + v + z + a7;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult9(uint64_t input) {
    assert(N == 9);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = fast_large_mult_mod_2(y + ms[1], x + 0);            // z = (x + 0) * (y + a1);
    __uint128_t t = extra_large_mult_mod(y + z + ms[2], x + z + ms[3]); // t = (y + z + a2) * (x + z + a3);
    __uint128_t u = extra_large_mult_mod(x + y + z + ms[4], x + ms[5]); // u = (x + y + z + a4) * (x + a5);
    __uint128_t v = extra_large_mult_mod(x + y + t + ms[6], z + ms[7]); // v = (x + y + t + a6) * (z + a7);
    __uint128_t P = u + v + ms[8];                                      // P = u + v + a8;
    if (P >= M89) P -= M89;
    return P;
  }
};

/* ***************************************************
 * Motzkin's quartic over the Mersenne prime p = 2^61 - 1
 * (4-wise independent, two multiplications)
 *
 *   y = x (x + b0) + b1,      P = y (y + x + b2) + b3
 *
 * Expanded:  P = x^4 + (2 b0 + 1) x^3 + (b0^2 + b0 + 2 b1 + b2) x^2
 *               + (b1 (2 b0 + 1) + b0 b2) x + (b1^2 + b1 b2 + b3).
 * In odd characteristic the key map (b0,b1,b2,b3) -> (a3,a2,a1,a0) is a
 * bijection onto the monic quartics, with explicit decoder
 *   b0 = (a3 - 1)/2,  c = a2 - b0^2 - b0,  b1 = a1 - b0 c,
 *   b2 = c - 2 b1,    b3 = a0 - b1^2 - b1 b2,
 * so uniform keys give a uniformly random monic quartic and the hash is
 * exactly 4-wise independent on the universe [p].  (Over GF(2^64) the same
 * circuit has a3 = 2 b0 + 1 = 1 and is only 3-wise: see smartcl_64<4>.)
 * 64-bit inputs are folded modulo p (x and x + p collide); the output is
 * fully reduced into [0, p).
 *
 * The arithmetic is lazy: values stay below 2^64 and are only folded with
 * 2^61 = 1 (mod p).  The bound at each step is noted inline; all of them
 * are exercised by `bench_tabrows selftest` (extreme keys and inputs,
 * compared against Horner evaluation of the expanded quartic).
 * ***************************************************/

class motzkin_61 {
  uint64_t b[4];
  constexpr static uint64_t P61 = ((uint64_t)1 << 61) - 1;

  // v mod p (lazily): (v mod 2^61) + (v >> 61) < 2^61 + 8 for any 64-bit v.
  static inline uint64_t fold(uint64_t v) { return (v & P61) + (v >> 61); }
  // a * b mod p (lazily): one 64x64->128 product and one fold.  Requires
  // a * b < 7 * 2^122 so that the fold cannot overflow; the result is
  // < 2^61 + (a * b >> 61).
  static inline uint64_t mul(uint64_t a, uint64_t b) {
    __uint128_t z = (__uint128_t)a * b;
    return ((uint64_t)z & P61) + (uint64_t)(z >> 61);
  }

 public:
  void init() {
    for (int i = 0; i < 4; i++) {
      do { b[i] = getRandomUInt64() >> 3; } while (b[i] >= P61);  // uniform in [0, p)
    }
  }
  void set_keys(uint64_t b0, uint64_t b1, uint64_t b2, uint64_t b3) {
    b[0] = b0; b[1] = b1; b[2] = b2; b[3] = b3;
  }
  const uint64_t* keys() const { return b; }
  uint64_t operator()(uint64_t x) {
    x = fold(x);                                 // x < 2^61 + 8,  x + b0 < 2^62 + 8
    uint64_t y = fold(mul(x, x + b[0]) + b[1]);  // product < 2^123 + 2^66,  y < 2^61 + 4
    uint64_t t = y + x + b[2];                   // t < 3 * 2^61 + 12
    uint64_t P = mul(y, t) + b[3];               // product < 3 * 2^122 + 2^66,  P < 5 * 2^61 + 32
    P = fold(P);                                 // P < 2^61 + 5
    return P - (P61 & (0 - (uint64_t)(P >= P61)));  // canonical [0, p), branch-free
  }
};

template <std::size_t N>
class smartpoly_64_kar {
  __uint128_t ms[N];
  constexpr static __uint128_t M89 = ((__uint128_t)1 << 89) - 1;

 public:
  void init() {
    for (int i = 0; i < N; i++) {
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
  }

 private:
  uint64_t mult2(uint64_t input) {
    assert(N == 2);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0); // y = (x + 0) * (x + a0);
    __uint128_t P = y + ms[1];                               // P = y + a1;
    // FIXME: This might even be wrong, since after adding ms[1], we could be larger than 2P...
    // Also, the following code is significantly faster than mine :(
    //__uint128_t P = fast_large_mult_mod(x + ms[0], ms[1], x);
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult3(uint64_t input) {
    assert(N == 3);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);     // y = (x + 0) * (x + a0);
    __uint128_t z = fast_large_mult_mod_2(x + y + ms[1], x + 0); // z = (x + y + a1) * (x + 0);
    __uint128_t P = z + ms[2];                                   // P = z + a2;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult4(uint64_t input) {
    assert(N == 4);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);        // y = (x + a0) * (x + 0);
    __uint128_t z = karatsuba_3vec_mult_mod(y + ms[1], x + y + ms[2]); // z = (y + a1) * (x + y + a2);
    __uint128_t P = z + ms[3];                                      // P = z + a3;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult5(uint64_t input) {
    assert(N == 5);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);        // y = (x + 0) * (x + a0);
    __uint128_t z = karatsuba_3vec_mult_mod(y + ms[1], x + y + ms[2]); // z = (y + a1) * (x + y + a2);
    __uint128_t t = fast_large_mult_mod_2(y + z + ms[3], x + 0);    // t = (y + z + a3) * (x + 0);
    __uint128_t P = t + ms[4];                                      // P = t + a4;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult6(uint64_t input) {
    assert(N == 6);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = fast_large_mult_mod_2(x + y + ms[1], x + 0);        // z = (x + 0) * (x + y + a1);
    __uint128_t t = karatsuba_3vec_mult_mod(y + z + ms[2], x + z + ms[3]); // t = (y + z + a2) * (x + z + a3);
    __uint128_t u = fast_large_mult_mod_2(z + ms[4], x + 0);            // u = (x + 0) * (z + a4);
    __uint128_t P = t + u + ms[5];                                      // P = t + u + a5;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult7(uint64_t input) {
    assert(N == 7);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = karatsuba_3vec_mult_mod(x + ms[1], x + y + ms[2]);     // z = (x + a1) * (x + y + a2);
    __uint128_t t = fast_large_mult_mod_2(z + ms[3], x + 0);            // t = (x + 0) * (z + a3);
    __uint128_t u = karatsuba_3vec_mult_mod(z + ms[4], y + z + t + ms[5]); // u = (z + a4) * (y + z + t + a5);
    __uint128_t P = u + y + ms[6];                                      // P = u + y + a6;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult8(uint64_t input) {
    assert(N == 8);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = karatsuba_3vec_mult_mod(y + ms[1], x + y + ms[2]);     // z = (y + a1) * (x + y + a2);
    __uint128_t t = fast_large_mult_mod_2(x + ms[3], x + 0);            // t = (x + 0) * (x + a3);
    __uint128_t u = karatsuba_3vec_mult_mod(z + ms[4], y + z + t + ms[5]); // u = (z + a4) * (y + z + t + a5);
    __uint128_t v = fast_large_mult_mod_2(z + t + ms[6], x + 0);        // v = (z + t + a6) * (x + 0);
    __uint128_t P = u + v + z + ms[7];                                  // P = u + v + z + a7;
    if (P >= M89) P -= M89;
    return P;
  }
  uint64_t mult9(uint64_t input) {
    assert(N == 9);
    __uint128_t x = input;
    __uint128_t y = fast_large_mult_mod_2(x + ms[0], x + 0);            // y = (x + 0) * (x + a0);
    __uint128_t z = karatsuba_3vec_mult_mod(x + y + ms[1], y + ms[2]);     // z = (x + y + a1) * (y + a2);
    __uint128_t t = karatsuba_3vec_mult_mod(z + ms[3], x + y + z + ms[4]); // t = (z + a3) * (x + y + z + a4);
    __uint128_t u = fast_large_mult_mod_2(y + z + t + ms[5], x + 0);    // u = (x + 0) * (y + z + t + a5);
    __uint128_t v = karatsuba_3vec_mult_mod(y + ms[6], z + ms[7]);         // v = (y + a6) * (z + a7);
    __uint128_t P = u + v + y + ms[8];                                  // P = u + v + y + a8;
    if (P >= M89) P -= M89;
    return P;
  }
};

/* ***************************************************
 * N-wise independent hashing using carryless multiplication.
 * Normal orners rule.
 * ***************************************************/

template <std::size_t N>
class carryless_64 {
  __m128i ms[(N + 1) / 2];

 public:
  void init() {
    for (std::size_t i = 0; i < (N + 1) / 2; ++i) {
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
    }
  }
  uint64_t operator()(uint64_t input) {
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i h = ms[0];
    if ((N & 1) == 0) {
      h = gf64_mult(h, x) ^ upper(ms[0]);
    }
    for (int i = 1; i < (N + 1) / 2; i++) {
      h = gf64_mult(h, x) ^ ms[i];
      h = gf64_mult(h, x) ^ upper(ms[i]);
    }
    return _mm_cvtsi128_si64(h);
  }
};

/* ***************************************************
 * Lemire N-wise independent hashing using carryless multiplication.
 * ***************************************************/

static __m128i lemul(__m128i a, __m128i b) {
  // Multiplies low parts of a and b
  return lemire_modulo(_mm_clmulepi64_si128(a, b, 0));
}
static __m128i lemul1(__m128i a) {
  // Multiplies high and low halfs of a
  return lemire_modulo(_mm_clmulepi64_si128(a, a, 0x01));
}

/**
 * Returns h*x + m[i] mod P64.
 * if i == 0 we use the lower bits of m, otherwise the higher bits.
 **/
static __m128i horner(__m128i h, __m128i x, __m128i m, int i) {
  h = lemul(h, x);
  return h ^ (i == 0 ? m : upper(m));
}

template <std::size_t N>
class lemire_64 {
  __m128i ms[(N + 1) / 2];

 public:
  void init() {
    for (std::size_t i = 0; i < (N + 1) / 2; ++i) {
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
    }
  }
  uint64_t operator()(uint64_t input) {
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i h = ms[0];
    if ((N & 1) == 0) {
      h = horner(h, x, ms[0], 1);
    }
    for (std::size_t i = 1; i < (N + 1) / 2; ++i) {
      h = horner(h, x, ms[i], 0);
      h = horner(h, x, ms[i], 1);
    }
    return _mm_cvtsi128_si64(h);
  }
};


template <std::size_t N>
class weird_horner_64 {
  __m128i ms[(N + 1) / 2];

 public:
  void init() {
    for (std::size_t i = 0; i < (N + 1) / 2; ++i) {
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
    }
  }
  uint64_t operator()(uint64_t input) {
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i xi = x;
    __m128i h = ms[0];
    if ((N & 1) == 0) {
      h = h ^ lemul(x, upper(ms[0]));
    }
    for (std::size_t i = 1; i < (N + 1) / 2; ++i) {
      xi = lemul(xi, x);
      h = h ^ lemul(xi, ms[i]);
      xi = lemul(xi, x);
      h = h ^ lemul(xi, upper(ms[i]));
    }
    return _mm_cvtsi128_si64(h);
  }
};

/* ***************************************************
 * Estrin N-wise independent hashing using fast (Lemire) carryless
 * multiplication.
 * ***************************************************/

template <std::size_t N>
class estrin_64 {
  __m128i ms[(N + 1) / 2];

 public:
  void init() {
    for (int i = 0; i < (N + 1) / 2; i++)
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
  }
  uint64_t operator()(uint64_t x) {
    if (N == 9) return mult9(x);
    if (N == 8) return mult8(x);
    if (N == 7) return mult7(x);
    if (N == 6) return mult6(x);
    if (N == 5) return mult5(x);
    if (N == 4) return mult4(x);
    if (N == 3) return mult3(x);
    if (N == 2) return mult2(x);
    assert(false);
  }

 private:
  uint64_t mult2(uint64_t input) {
    assert(N == 2);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i h = horner(x, ms[0], ms[0], 1);  // H = M0 + M1 x
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult3(uint64_t input) {
    assert(N == 3);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i c1 = horner(x, ms[0], ms[0], 1);  // C1 = M0 + M1 x
    __m128i c2 = ms[1];                       // C2 = M2
    __m128i h = horner(x2, c2, c1, 0);        // H = C1 + C2 x^2
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult4(uint64_t input) {
    assert(N == 4);
    // P3(x) = (C0 + C1x) + (C2 + C3x) x2
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    // Then we basically do bottom-up horner
    __m128i c1 = horner(x, ms[0], ms[0], 1);  // C1 = M0 + M1 x
    __m128i c2 = horner(x, ms[1], ms[1], 1);  // C2 = M2 + M3 x
    __m128i h = horner(x2, c2, c1, 0);        //  H = C1 + C2 x^2
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult5(uint64_t input) {
    assert(N == 5);
    // P4(x) = (C0 + C1x) + (C2 + C3x) x2 + C4x4
    __m128i x = _mm_cvtsi64_si128(input);
    // First we precompute the powers of x
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    // Then we basically do bottom-up horner
    __m128i c1 = horner(x, ms[0], ms[0], 1);  // C1 = M0 + M1 x
    __m128i c2 = horner(x, ms[1], ms[1], 1);  // C2 = M2 + M3 x
    __m128i c3 = ms[2];                       // C3 = M4
    // Combine first two terms using horner with x^2
    __m128i d1 = horner(x2, c2, c1, 0);       // D1 = C0 + C1 x^2
    __m128i d2 = c3;                          // D2 = C3
    // Combine last term using horner with x^4
    __m128i h = horner(x4, d2, d1, 0);        // H = D1 + D2 x^4
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult6(uint64_t input) {
    assert(N == 6);
    __m128i x = _mm_cvtsi64_si128(input);
    // First we precompute the powers of x
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    // Then we basically do bottom-up horner
    __m128i c0 = horner(x, ms[0], ms[0], 1);  // C0 = M0 + M1 x
    __m128i c1 = horner(x, ms[1], ms[1], 1);  // C1 = M2 + M3 x
    __m128i c2 = horner(x, ms[2], ms[2], 1);  // C2 = M5 + M5 x
    __m128i d0 = horner(x2, c1, c0, 0);       // D0 = C0 + C1 x^2
    __m128i d1 = c2;                          // D1 = C2
    __m128i h = horner(x4, d1, d0, 0);        // H = D0 + D1 x^4
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult7(uint64_t input) {
    assert(N == 7);
    // P6(x) = (C0 + C1x) + (C2 + C3x) x2 + ((C4 + C5x) + C6x2)x4
    __m128i x = _mm_cvtsi64_si128(input);
    // First we precompute the powers of x
    // It's actually a lot slower if we compute them as we go...
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    // Then we basically do bottom-up horner
    __m128i c0 = horner(x, ms[0], ms[0], 1);  // C0 = M0 + M1 x
    __m128i c1 = horner(x, ms[1], ms[1], 1);  // C1 = M2 + M3 x
    __m128i c2 = horner(x, ms[2], ms[2], 1);  // C2 = M5 + M5 x
    __m128i c3 = ms[3];                       // C3 = M6
    __m128i d0 = horner(x2, c1, c0, 0);       // D0 = C0 + C1 x^2
    __m128i d1 = horner(x2, c3, c2, 0);       // D1 = C2 + C3 x^2
    __m128i h = horner(x4, d1, d0, 0);        // H = D0 + D1 x^4
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult8(uint64_t input) {
    assert(N == 8);
    // P7(x) = (C0 + C1x) + (C2 + C3x) x2 + ((C4 + C5x) + (C6 + C7x) x2)x4
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    // Then we basically do bottom-up horner
    __m128i c0 = horner(x, ms[0], ms[0], 1);  // C0 = M0 + M1 x
    __m128i c1 = horner(x, ms[1], ms[1], 1);  // C1 = M2 + M3 x
    __m128i c2 = horner(x, ms[2], ms[2], 1);  // C2 = M5 + M5 x
    __m128i c3 = horner(x, ms[3], ms[3], 1);  // C3 = M6 + M7 x
    __m128i d0 = horner(x2, c1, c0, 0);       // D0 = C0 + C1 x^2
    __m128i d1 = horner(x2, c3, c2, 0);       // D1 = C2 + C3 x^2
    __m128i h = horner(x4, d1, d0, 0);        // H = D0 + D1 x^4
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult9(uint64_t input) {
    assert(N == 9);
    // P8(x) = (C0 + C1x) + (C2 + C3x) x2 + ((C4 + C5x) + (C6 + C7x) x2)x4 + C8x8
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    __m128i x8 = lemul(x4, x4);
    // Then we basically do bottom-up horner
    __m128i c0 = horner(x, ms[0], ms[0], 1);  // C0 = M0 + M1 x
    __m128i c1 = horner(x, ms[1], ms[1], 1);  // C1 = M2 + M3 x
    __m128i c2 = horner(x, ms[2], ms[2], 1);  // C2 = M5 + M5 x
    __m128i c3 = horner(x, ms[3], ms[3], 1);  // C3 = M6 + M7 x
    __m128i c4 = ms[4];                       // C4 = M8
    __m128i d0 = horner(x2, c1, c0, 0);       // D0 = C0 + C1 x^2
    __m128i d1 = horner(x2, c3, c2, 0);       // D1 = C2 + C3 x^2
    __m128i e0 = horner(x4, d1, d0, 0);       // E0 = D0 + D1 x^4
    __m128i e1 = c4;                          // E1 = C4
    __m128i h = horner(x8, e1, e0, 0);        // H = E0 + E1 x8
    return _mm_cvtsi128_si64(h);
  }
};

// Let's see if clang can make as good code as me
template <std::size_t N>
class estrin_64_gen {
  __m128i ms[(N + 1) / 2];

 public:
  void init() {
    for (int i = 0; i < (N + 1) / 2; i++)
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
  }
  uint64_t operator()(uint64_t input) {
    assert(N >= 2);
    __m128i x = _mm_cvtsi64_si128(input);

    __m128i ds[(N + 1) / 2];
    for (int i = 0; i < N / 2; i++) {
      // We only store things in the lower bits of ds.
      // But the ms have data in both lower and higher bits.
      ds[i] = horner(x, ms[i], ms[i], 1);  // C0 x + C1
    }
    if ((N & 1) == 1) ds[N / 2] = ms[N / 2];
    int n = (N + 1) / 2;

    // int k = 1;
    // int l = n;
    // while (n != 1) {
    //    k++;
    //    l = (l + 1) / 2;
    // }
    // __m128i xs[l];
    // xs
    // for (int i = 0; i < l; l++)
    //    xs[i]

    while (n != 1) {
      // This is the main issue with the "general" version.
      // We are introducing a particular order on the xs.
      x = lemul(x, x);
      for (int i = 0; i < n / 2; i++) {
        ds[i] = horner(x, ds[2 * i + 1], ds[2 * i], 0);
      }
      if ((n & 1) == 1) ds[n / 2] = ds[n - 1];
      n = (n + 1) / 2;
    }

    return _mm_cvtsi128_si64(ds[0]);
  }
};


/* ***************************************************
 * R&W multiplication.
 * Note this differs from Berstein's version, since he
 * only wanted injectivity, and not surjectivity.
 * See http://cr.yp.to/antiforgery/pema-20071022.pdf
 * and "Evaluating Bernstein–Rabin–Winograd polynomials"
 * for details.
 * ***************************************************/


template <std::size_t N>
class rw_64 {
  __m128i ms[(N + 1) / 2];

 public:
  void init() {
    for (int i = 0; i < (N + 1) / 2; i++)
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
  }
  uint64_t operator()(uint64_t x) {
    if (N == 9) return mult9(x);
    if (N == 8) return mult8(x);
    if (N == 7) return mult7(x);
    if (N == 6) return mult6(x);
    if (N == 5) return mult5(x);
    if (N == 4) return mult4(x);
    if (N == 3) return mult3(x);
    if (N == 2) return mult2(x);
    assert(false);
  }

 private:
  uint64_t mult2(uint64_t input) {
    assert(N == 2);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i h1 = x ^ ms[0];                   // H1 = x + M0
    __m128i h2 = lemul(h1, x) ^ upper(ms[0]); // H2 = H1 x + M1
    return _mm_cvtsi128_si64(h2);
  }
  uint64_t mult3(uint64_t input) {
    assert(N == 3);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i h1 = x ^ ms[0];                  // H1 = x + M0
    __m128i g1 = x ^ upper(ms[0]);           // G1 = x + M1
    __m128i h3 = lemul(h1, x2 ^ ms[1]) ^ g1; // H3 = H1 (x^2 + M2) + G1
    return _mm_cvtsi128_si64(h3);
  }
  uint64_t mult4(uint64_t input) {
    assert(N == 4);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i h1 = x ^ ms[0];                   // H1 = x + M0
    __m128i g1 = x ^ upper(ms[0]);            // G1 = x + M1
    __m128i h3 = lemul(h1, x2 ^ ms[1]) ^ g1;  // H3 = H1 (x^2 + M2) + G1
    __m128i h4 = lemul(h3, x) ^ upper(ms[1]); // H4 = H3 x + M3
    return _mm_cvtsi128_si64(h4);
  }
  uint64_t mult5(uint64_t input) {
    assert(N == 5);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    __m128i h1 = x ^ ms[0];                   // H1 = x + M0
    __m128i g1 = x ^ upper(ms[0]);            // G1 = x + M1
    __m128i i1 = x ^ ms[2];                   // I1 = x + M4
    __m128i h3 = lemul(h1, x2 ^ ms[1]) ^ g1;  // H3 = H1 (x^2 + M2) + G1
    __m128i h4 = lemul(h3, x) ^ upper(ms[1]); // H4 = H3 x + M3
    __m128i h5 = h4 ^ lemul(x4, i1);          // H5 = I1 x^4 + H4
    return _mm_cvtsi128_si64(h5);
  }
  uint64_t mult6(uint64_t input) {
    assert(N == 6);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    __m128i h1 = x ^ ms[0];                         // H1 = x + M0
    __m128i g1 = x ^ upper(ms[0]);                  // G1 = x + M1
    __m128i i1 = x ^ upper(ms[1]);                  // I1 = x + M3
    __m128i h3 = lemul(h1, x2 ^ ms[1]) ^ g1;        // H3 = H1 (x^2 + M2) + G1
    __m128i h4 = lemul(h3, x) ^ upper(ms[2]);       // H4 = H3 x + M3
    __m128i g2 = lemul(i1, x) ^ ms[2];              // G2 = M4 + x I1
    __m128i h6 = lemul(g2, x4) ^ h4;                // H6 = G2 x^4 + H4
    return _mm_cvtsi128_si64(h6);
  }
  uint64_t mult7(uint64_t input) {
    assert(N == 7);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    __m128i h1 = x ^ ms[0];                         // H1 = x + M0
    __m128i g1 = x ^ upper(ms[0]);                  // G1 = x + M1
    __m128i i1 = x ^ upper(ms[1]);                  // I1 = x + M3
    __m128i j1 = x ^ ms[1];                         // J1 = x + M4
    __m128i h3 = lemul(h1, x2 ^ ms[2]) ^ g1;        // H3 = H1 (x^2 + M2) + G1
    __m128i g3 = lemul(i1, x2 ^ upper(ms[2])) ^ j1; // G3 = I1 (x^2 + M5) + J1
    __m128i h7 = lemul(g3, x4 ^ ms[3]) ^ h3;        // H7 = G3 (x^4 + M6) + H3
    return _mm_cvtsi128_si64(h7);
  }
  uint64_t mult8(uint64_t input) {
    assert(N == 8);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    __m128i h1 = x ^ ms[0];                         // H1 = x + M0
    __m128i g1 = x ^ upper(ms[0]);                  // G1 = x + M1
    __m128i i1 = x ^ upper(ms[1]);                  // I1 = x + M3
    __m128i j1 = x ^ ms[1];                         // J1 = x + M4
    __m128i h3 = lemul(h1, x2 ^ ms[2]) ^ g1;        // H3 = H1 (x^2 + M2) + G1
    __m128i g3 = lemul(i1, x2 ^ upper(ms[2])) ^ j1; // G3 = I1 (x^2 + M5) + J1
    __m128i h7 = lemul(g3, x4 ^ ms[3]) ^ h3;        // H7 = G3 (x^4 + M6) + H3
    __m128i h8 = lemul(h7, x) ^ upper(ms[3]);       // H8 = M7 + x H7
    return _mm_cvtsi128_si64(h8);
  }
  uint64_t mult9(uint64_t input) {
    assert(N == 9);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i x2 = lemul(x, x);
    __m128i x4 = lemul(x2, x2);
    __m128i x8 = lemul(x4, x4);
    __m128i h1 = x ^ ms[0];                         // H1 = x + M0
    __m128i g1 = x ^ upper(ms[0]);                  // G1 = x + M1
    __m128i i1 = x ^ upper(ms[1]);                  // I1 = x + M2
    __m128i j1 = x ^ ms[1];                         // J1 = x + M3
    __m128i k1 = x ^ upper(ms[2]);                  // K1 = x + M4
    __m128i h3 = lemul(h1, x2 ^ ms[2]) ^ g1;        // H3 = H1 (x^2 + M5) + G1
    __m128i g3 = lemul(i1, x2 ^ upper(ms[3])) ^ j1; // G3 = I1 (x^2 + M6) + J1
    __m128i h7 = lemul(g3, x4 ^ ms[3]) ^ h3;        // H7 = G3 (x^4 + M7) + H3
    __m128i h8 = lemul(h7, x) ^ ms[4];              // H8 = M8 + x H7
    __m128i h9 = lemul(k1, x8) ^ h8;                // H9 = H8 + x^8 K1
    return _mm_cvtsi128_si64(h9);
  }
};

// Recursive version. This is a lot slower than the hand-rolled one above.
// Maybe there's a way to make it as fast?
template <std::size_t N>
class rw_64_rec {
  __m128i ms[N];
  __m128i xs[N-1]; // Just some upper bound to log2(N)

public:
  void init() {
    // We only need to store this in the low bits, but I don't remember
    // which are the high and low...
    for (int i = 0; i < N; i++) {
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
    }
  }
  uint64_t operator()(uint64_t input) {
    __m128i x = _mm_cvtsi64_si128(input);
    xs[0] = x;
    for (int i = 1; (1 << i) <= N; i++)
       xs[i] = xs[i-1] * xs[i-1];
    return _mm_cvtsi128_si64(rec(0, N));
  }
private:
  __m128i rec(int a, int b) {
     int n = b - a;
     if (n == 1) {
        return xs[0] ^ ms[a];
     }
     // assert(n >= 1);
     int k = 0, tk = 1;
     while (2 * tk <= n) {
        k++;
        tk *= 2;
     }
     // assert((1 << k) == tk);
     // assert(tk <= n);
     // assert(n < 2*tk);
     if (n == 2*tk - 1) {
        __m128i hi = rec(a, a + tk - 1);
        __m128i lo = rec(a + tk, b); // b - (a + tk) == n - tk = tk - 1
        return lemul(hi, xs[k] ^ ms[a + tk - 1]) ^ lo;
     } else {
        __m128i hi = rec(a, b - tk + 1);
        __m128i lo = rec(b - tk + 1, b);
        return lemul(hi, xs[k]) ^ lo;
     }
  }
};

/* ***************************************************
 * Smart N indep, carryless
 * ***************************************************/

template <std::size_t N>
class smartcl_64 {
  __m128i ms[(N + 1) / 2];

 public:
  void init() {
    for (int i = 0; i < (N + 1) / 2; i++)
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
  }
  __uint128_t operator()(uint64_t x) {
    if (N == 2) return small(x);
    if (N == 3) return mult3(x);
    if (N == 4) return mult4(x);
    if (N == 5) return mult5(x);
    if (N == 6) return mult6(x);
    //if (N == 7) return mult7_alt(x);
    //if (N == 7) return mult7(x);
    if (N == 7) return mult7_alt2(x);
    if (N == 8) return mult8(x);
    if (N == 9) return mult9_alt(x);
    assert(false);
  }

 private:
  uint64_t small(uint64_t input) {
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i h = ms[0];
    if ((N & 1) == 0) {
      h = horner(h, x, ms[0], 1);
    }
    for (std::size_t i = 1; i < (N + 1) / 2; ++i) {
      h = horner(h, x, ms[i], 0);
      h = horner(h, x, ms[i], 1);
    }
    return _mm_cvtsi128_si64(h);
  }
  uint64_t mult3(uint64_t input) {
    assert(N >= 3);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x);                        // y = (x + 0) * (x + 0);
    __m128i z = lemul(x ^ ms[0], y ^ upper(ms[0])); // z = (x + a0) * (y + a1);
    return _mm_cvtsi128_si64(z ^ ms[1]);            // P = z + a2;
  }
  uint64_t mult3_alt(uint64_t input) {
    assert(N >= 3);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x);                        // y = (x + 0) * (x + 0);
    // Let's try to to do the whole xor in one go,
    // by packing x and y into a single 128 vector.
    // Conclusion: Doesn't help.
    __m128i combined = _mm_unpacklo_epi64(x, y);
    __m128i z = lemul1(combined ^ ms[0]);           // z = (y + a0) * (x + a1);
    return _mm_cvtsi128_si64(z ^ ms[1]);            // P = z + a2;
  }
  uint64_t mult4(uint64_t input) {
     // Not faster than just using Lemire/Horner
    assert(N == 4);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x);                        // y = (x + 0) * (x + 0);
    __m128i z = lemul(x ^ ms[0], y ^ upper(ms[0])); // z = (x + a0) * (y + a1);
    __m128i t = lemul(z ^ ms[1], x);                // Just horner on 3
    return _mm_cvtsi128_si64(t ^ upper(ms[1]));
  }
  uint64_t mult5(uint64_t input) {
    assert(N >= 5);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x);                            // y = x * x
    __m128i z = lemul(y ^ ms[0], x ^ y ^ upper(ms[0])); // z = (y + a4) * (x + y + a3)
    __m128i w = lemul(x ^ ms[1], z ^ upper(ms[1]));     // w = (x + a2) * (z + a1)
    __m128i P = w ^ ms[2];                              // P = w + a0
    return _mm_cvtsi128_si64(P);
  }
  uint64_t mult6(uint64_t input) {
    assert(N == 6);
    // Basically make a H3, then
    // P = H3 y^2 + x (a4 + x)
    // That is, we shift up by 2, so we can work independently on the lower part.
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x ^ 0, x ^ ms[0]);                // y = (x + 0) * (x + a0);
    __m128i z = lemul(y ^ upper(ms[0]), x ^ y ^ ms[1]); // z = (y + a1) * (x + y + a2);
    __m128i t = lemul(z ^ upper(ms[1]), y ^ 0);         // t = (z + a3) * (y + 0);
    __m128i u = lemul(x ^ ms[2], x ^ 0);                // u = (x + a4) * (x + 0);
    __m128i P = t ^ u ^ upper(ms[2]);                   // P = t + u + a5;
    return _mm_cvtsi128_si64(P);
  }
  // Somehow this is even slower than Rabin Winograd.
  // Meanwhile the N = 5 case above is actually faster.
  // Maybe this is because computing x^2 first is actually
  // quite fast in practice? Maybe try a polynomial here
  // that does that too, even if it costs an extra add?
  uint64_t mult7(uint64_t input) {
    assert(N >= 7);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x ^ ms[0]);                    // y = x (x + a6)
    __m128i z = lemul(x ^ ms[1], y ^ upper(ms[1]));     // z = (x + a5) (y + a4)
    __m128i w = lemul(z, z ^ upper(ms[0]));             // w = z (z + a3)
    __m128i v = lemul(x ^ ms[2], w ^ y ^ upper(ms[2])); // v = (x + a1) (w + y + a2)
    __m128i P = v ^ ms[3];                              // P = v + a0
    return _mm_cvtsi128_si64(P);
  }
  uint64_t mult7_alt2(uint64_t input) {
    assert(N == 7);
    __m128i x = _mm_cvtsi64_si128(input);

    //__m128i y = lemul(x ^ 0, x ^ ms[0]);                // y = (x + 0) * (x + a0);
    //__m128i z = lemul(x ^ y ^ upper(ms[0]), x ^ ms[1]); // z = (x + y + a1) * (x + a2);
    //__m128i t = lemul(y ^ z ^ 0, y ^ z ^ upper(ms[1])); // t = (y + z + 0) * (y + z + a3);
    //__m128i u = lemul(x ^ ms[2], y ^ t ^ upper(ms[2])); // u = (x + a4) * (y + t + a5);
    //__m128i P = u ^ ms[3];

    __m128i y = lemul(x ^ 0, x ^ ms[0]);                    // y = (x + 0) * (x + a0);
    __m128i z = lemul(x ^ upper(ms[0]), y ^ ms[1]);         // z = (x + a1) * (y + a2);
    __m128i t = lemul(z ^ upper(ms[1]), z ^ 0);             // t = (z + a3) * (z + 0);
    __m128i u = lemul(x ^ y ^ t ^ ms[2], x ^ upper(ms[2])); // u = (x + y + t + a4) * (x + a5);
    __m128i P = u ^ ms[3];                                  // P = u + a6;
    
    // __m128i y = lemul(x ^ 0, x ^ ms[0]);
    // __m128i z = lemul(x ^ upper(ms[0]), x ^ y ^ ms[1]);
    // __m128i t = lemul(x ^ y ^ z ^ 0, x ^ y ^ z ^ upper(ms[1]));
    // __m128i u = lemul(x ^ y ^ t ^ ms[2], x ^ upper(ms[2]));
    // __m128i P = u ^ ms[3];
    
    // __m128i y = lemul(x ^ 0, x ^ ms[0]);                // y = (x + 0) * (x + a0);
    // __m128i z = lemul(x ^ upper(ms[0]), y ^ ms[1]);     // z = (x + a1) * (y + a2);
    // __m128i t = lemul(z ^ upper(ms[1]), z ^ 0);         // t = (z + a3) * (z + 0);
    // __m128i u = lemul(y ^ t ^ ms[2], x ^ upper(ms[2])); // u = (y + t + a4) * (x + a5);
    // __m128i P = u ^ ms[3];                              // P = u + a6;

    return _mm_cvtsi128_si64(P);
  }
  uint64_t mult8(uint64_t input) {
    assert(N == 8);
    __m128i x = _mm_cvtsi64_si128(input);
    //__m128i y = lemul(x ^ 0, x ^ ms[0]);                    // y = (x + 0) * (x + a0);
    //__m128i z = lemul(x ^ 0, y ^ 0);                        // z = (x + 0) * (y + 0);
    //__m128i t = lemul(y ^ upper(ms[0]), y ^ z ^ ms[1]);     // t = (y + a1) * (y + z + a2);
    //__m128i u = lemul(x ^ y ^ t ^ upper(ms[1]), z ^ ms[2]); // u = (x + y + t + a3) * (z + a4);
    //__m128i v = lemul(x ^ upper(ms[2]), y ^ ms[3]);         // v = (x + a5) * (y + a6);
    //__m128i P = u ^ v ^ upper(ms[3]);                       // P = u + v + a7;
    __m128i y = lemul(x ^ 0, x ^ ms[0]);                    // y = (x + 0) * (x + a0);
    __m128i z = lemul(x ^ 0, y ^ 0);                        // z = (x + 0) * (y + 0);
    __m128i t = lemul(y ^ upper(ms[0]), y ^ z ^ ms[1]);     // t = (y + a1) * (y + z + a2);
    __m128i u = lemul(x ^ y ^ t ^ upper(ms[1]), z ^ ms[2]); // u = (x + y + t + a3) * (z + a4);
    __m128i v = lemul(x ^ upper(ms[2]), y ^ ms[3]);         // v = (x + a5) * (y + a6);
    __m128i P = u ^ v ^ upper(ms[3]);                       // P = u + v + a7;
    return _mm_cvtsi128_si64(P);
  }
  uint64_t mult9(uint64_t input) {
    assert(N == 9);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x ^ ms[0]);                    // y = (x + 0) * (x + a0)
    __m128i z = lemul(x ^ upper(ms[0]), y ^ ms[1]);     // z = (x + a1) * (y + a2)
    __m128i t = lemul(z ^ upper(ms[1]), x ^ ms[2]);     // t = (z + a3) * (x + a4)
    __m128i u = lemul(x ^ upper(ms[2]), y ^ t ^ ms[3]); // u = (x + a5) * (y + t + a6)
    __m128i v = lemul(t ^ upper(ms[3]), u);             // v = (t + a7) * (u + 0)
    __m128i P = v ^ z ^ ms[4];                          // P = v + z + a8
    return _mm_cvtsi128_si64(P);
  }
  // This version uses 1 more addition (12 in total), but it starts by computing x^2,
  // which seems to often be faster in practice. Another reason could be that this
  // keeps the memory access pattern for the ms more aligned.
  uint64_t mult9_alt(uint64_t input) {
    assert(N == 9);
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x);                            // y = (x + 0) * (x + 0)
    __m128i z = lemul(ms[0] ^ x, upper(ms[0]) ^ y);     // z = (x + a0) * (y + a1)
    __m128i u = lemul(ms[1] ^ x, upper(ms[1]) ^ y);     // u = (x + a4) * (y + a5)
    __m128i t = lemul(ms[2] ^ z, upper(ms[2]) ^ y ^ z); // t = (z + a2) * (y + z + a3)
    __m128i v = lemul(ms[3] ^ t, upper(ms[3]) ^ x ^ z); // v = (t + a6) * (x + z + a7)
    __m128i P = ms[4] ^ u ^ v;                          // P = u + v + a8
    return _mm_cvtsi128_si64(P);
  }
};

/* ***************************************************
 * The two quartic circuits over GF(2^64) as separately named classes, so
 * that both exist on both platforms with the same names.  (Here
 * smartcl_64<4>::mult4 is the three-multiplication circuit; in
 * fast_hashing_arm.h smartcl_64<4>::mult4 is Motzkin's two-multiplication
 * circuit.  Both existing classes are left untouched.)
 *
 * quartic2_64 -- Motzkin's quartic, two multiplications:
 *   y = x (x + a0) + a1,   P = y (y + x + a2) + a3
 *     = x^4 + (2 a0 + 1) x^3 + (a0^2 + a0 + a2) x^2 + (a0 a2 + a1) x
 *       + (a1^2 + a1 a2 + a3).
 *   In characteristic 2 the x^3 coefficient is 2 a0 + 1 = 1 for every key,
 *   so the family is exactly 3-wise independent (the other three
 *   coefficients are uniform).  Same circuit as motzkin_61 over 2^61 - 1,
 *   where it is 4-wise.
 *
 * quartic3_64 -- x Q3(x) + a3 with Q3 the two-multiplication cubic, three
 * multiplications:
 *   y = x^2,  z = (x + a0)(y + a1),  t = (z + a2) x,  P = t + a3
 *     = x^4 + a0 x^3 + a1 x^2 + (a0 a1 + a2) x + a3.
 *   The key map is a bijection onto the monic quartics, with decoder
 *   a0 = c3, a1 = c2, a2 = c1 + c3 c2, a3 = c0, so the hash is 4-wise.
 *
 * Both are checked against Horner on the expanded polynomial (and the
 * quartic3_64 decoder round-trip) by `bench_tabrows selftest`.
 * ***************************************************/

class quartic2_64 {
  __m128i ms[2];  // ms[0] = (a1 : a0), ms[1] = (a3 : a2)  (high : low)

 public:
  void init() {
    for (int i = 0; i < 2; i++)
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
  }
  void set_keys(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3) {
    ms[0] = _mm_set_epi64x(a1, a0);
    ms[1] = _mm_set_epi64x(a3, a2);
  }
  uint64_t operator()(uint64_t input) {
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x ^ ms[0]) ^ upper(ms[0]);      // y = x (x + a0) + a1
    __m128i P = lemul(y, y ^ x ^ ms[1]) ^ upper(ms[1]);  // P = y (y + x + a2) + a3
    return _mm_cvtsi128_si64(P);
  }
};

class quartic3_64 {
  __m128i ms[2];  // ms[0] = (a1 : a0), ms[1] = (a3 : a2)  (high : low)

 public:
  void init() {
    for (int i = 0; i < 2; i++)
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
  }
  void set_keys(uint64_t a0, uint64_t a1, uint64_t a2, uint64_t a3) {
    ms[0] = _mm_set_epi64x(a1, a0);
    ms[1] = _mm_set_epi64x(a3, a2);
  }
  uint64_t operator()(uint64_t input) {
    // Identical to smartcl_64<4>::mult4 in this file.
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x);                         // y = x^2
    __m128i z = lemul(x ^ ms[0], y ^ upper(ms[0]));  // z = (x + a0) (y + a1)
    __m128i t = lemul(z ^ ms[1], x);                 // t = (z + a2) x
    return _mm_cvtsi128_si64(t ^ upper(ms[1]));      // P = t + a3
  }
};


/* ***************************************************
 * septic7_64 -- the certified degree-7 circuit over GF(2^64), four
 * multiplications (the characteristic-2 circuit with the unit-pivot decoder
 * of the paper's appendix; ChainHash's former finalizer, website CIRCUITS[7]):
 *   y = x (x + c0),  z = (x + c1)(y + c2),  t = z (z + c3),
 *   u = (x + c4)(y + t + c5),  P = u + c6.
 * Expanded over GF(2)[c][x] (tools/bench/chainhash/verify7.py; re-checked
 * numerically by `bench_tabrows selftest`), with b = c0 + c1,
 * e = c2 + c0 c1, d = c1 c2:
 *   P = x^7 + c4 x^6 + b^2 x^5 + (c3 + c4 b^2) x^4
 *       + (e^2 + c3 b + 1 + c3 c4) x^3
 *       + (c3 e + c0 + c4 (e^2 + c3 b + 1)) x^2
 *       + (d^2 + c3 d + c5 + c4 (c3 e + c0)) x
 *       + (c6 + c4 (d^2 + c3 d + c5)).
 * The key map (c0..c6) -> (a6..a0) is a bijection of GF(2^64)^7 onto the
 * monic septics, with the explicit decoder (sqrt is the Frobenius inverse,
 * sqrt(a) = a^(2^63), a bijection of GF(2^64)):
 *   q0 = a6,  q1 = sqrt(a5),  q2 = a4 + q0 q1^2,
 *   q3 = sqrt(a3 + q2 q1 + q2 q0 + 1),
 *   q4 = a2 + q2 q3 + q1 + q0 (q3^2 + q2 q1 + 1),
 *   delta = q4 (q3 + q1 q4 + q4^2),
 *   q5 = a1 + delta^2 + q2 delta + q0 (q2 q3 + q1 + q4),
 *   q6 = a0 + q0 (delta^2 + q2 delta + q5),
 *   (c0, .., c6) = (q1 + q4, q4, q3 + q1 q4 + q4^2, q2, q0, q5, q6).
 * Uniform keys therefore give a uniformly random monic septic, so the hash
 * is exactly 7-wise independent.  (smartcl_64<7>::mult7_alt2 above is the
 * search circuit, u = (x + y + t + a4)(x + a5), for which no inverse is
 * displayed.)
 * ***************************************************/

class septic7_64 {
  __m128i ms[4];  // ms[0] = (c1 : c0), ms[1] = (c3 : c2), ms[2] = (c5 : c4), ms[3] = (0 : c6)  (high : low)

 public:
  void init() {
    for (int i = 0; i < 3; i++)
      ms[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
    ms[3] = _mm_cvtsi64_si128(getRandomUInt64());
  }
  void set_keys(const uint64_t c[7]) {
    ms[0] = _mm_set_epi64x(c[1], c[0]);
    ms[1] = _mm_set_epi64x(c[3], c[2]);
    ms[2] = _mm_set_epi64x(c[5], c[4]);
    ms[3] = _mm_cvtsi64_si128(c[6]);
  }
  uint64_t operator()(uint64_t input) {
    __m128i x = _mm_cvtsi64_si128(input);
    __m128i y = lemul(x, x ^ ms[0]);                      // y = x (x + c0)
    __m128i z = lemul(x ^ upper(ms[0]), y ^ ms[1]);       // z = (x + c1) (y + c2)
    __m128i t = lemul(z, z ^ upper(ms[1]));               // t = z (z + c3)
    __m128i u = lemul(x ^ ms[2], y ^ t ^ upper(ms[2]));   // u = (x + c4) (y + t + c5)
    return _mm_cvtsi128_si64(u ^ ms[3]);                  // P = u + c6
  }
};

/* ***************************************************
 * Tabulation
 * ***************************************************/

class tabulation_64 {
  uint64_t table[8][256];

 public:
  void init() {
    for (int i = 0; i < 8; i++)
      for (int j = 0; j < 256; j++) table[i][j] = getRandomUInt64();
  }
  uint64_t operator()(uint64_t x) {
    uint64_t res = 0;
    for (int i = 0; i < 8; i++) {
      res ^= table[i][(char)x];
      x >>= 8;
    }
    return res;
  }
};

class tabulation_64_tree {
  uint64_t table[8][256];

 public:
  void init() {
    for (int i = 0; i < 8; i++)
      for (int j = 0; j < 256; j++) table[i][j] = getRandomUInt64();
  }
  uint64_t operator()(uint64_t x) {
    uint64_t r0 = table[0][(char)x] ^ table[1][(char)(x >> 8)];
    uint64_t r1 = table[2][(char)(x >> 8*2)] ^ table[3][(char)(x >> 8*3)];
    uint64_t r2 = table[4][(char)(x >> 8*4)] ^ table[5][(char)(x >> 8*5)];
    uint64_t r3 = table[6][(char)(x >> 8*6)] ^ table[7][(char)(x >> 8*7)];
    uint64_t s0 = r0 ^ r1;
    uint64_t s1 = r2 ^ r3;
    return s0 ^ s1;
  }
};

class tabulation_16x4 {
  uint64_t table[16][16];

 public:
  void init() {
    for (int i = 0; i < 16; i++)
      for (int j = 0; j < 16; j++) table[i][j] = getRandomUInt64();
  }
  uint64_t operator()(uint64_t x) {
    uint64_t res = 0;
    for (int i = 0; i < 16; i++) {
      res ^= table[i][x & 0xf];
      x >>= 4;
    }
    return res;
  }
};

class tabulation_4x16 {
  uint64_t table[4][1 << 16];

 public:
  void init() {
    for (int i = 0; i < 4; i++)
      //for (int j = 0; j < (1<<16); j++) table[i][j] = getRandomUInt64();
      for (int j = 0; j < (1<<8); j++) table[i][j] = getRandomUInt64();
  }
  uint64_t operator()(uint64_t x) {
    uint64_t res = 0;
    for (int i = 0; i < 4; i++) {
      assert((x & 0xffff) >= 0);
      assert((x & 0xffff) < (1 << 16));
      res ^= table[i][x & 0xffff];
      x >>= 16;
    }
    return res;
  }
};

template <const int D>
class mixed_64 {
  __uint128_t table1[8][256];
  uint64_t table2[D][256];

 public:
  void init() {
    for (int j = 0; j < 256; j++) {
      for (int i = 0; i < 8; i++) table1[i][j] = getRandomUInt128();
      for (int i = 0; i < D; i++) table2[i][j] = getRandomUInt64();
    }
  }
  uint64_t operator()(uint64_t x) {
    __uint128_t v1v2 = 0;
    for (int i = 0; i < 8; i++) {
      v1v2 ^= table1[i][(char)x];
      x >>= 8;
    }
    uint64_t v1 = v1v2 >> 64; // High bits (used for extra chars)
    uint64_t h = v1v2;        // Low bits (the main tabulation hash)
    for (int i = 0; i < D; i++) {
      h ^= table2[i][(char)v1];
      v1 >>= 8;
    }
    return h;
  }
};



/* ***************************************************
 * Shuf.
 * Thomas trying to make a faster tabulation-hash
 * using the shuffle_epi8 instruction.
 * ***************************************************/

template <const int L>
class shuf_64 {
  __m128i table[L];
  __m128i rot =
      _mm_setr_epi8(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0);

 public:
  void init() {
    for (int i = 0; i < L; i++)
      table[i] = _mm_set_epi64x(getRandomUInt64(), getRandomUInt64());
  }

  uint64_t operator()(uint64_t input) {
    __m128i x = _mm_set_epi64x(input >> 4, input);  // Split in odd and evens
    __m128i h = _mm_cvtsi64_si128(0);
    for (int i = 0; i < L; i++) {
      h ^= _mm_shuffle_epi8(table[i], x);
      x = _mm_shuffle_epi8(x, rot);  // Wait, is it actually as fast?
                                     // x = _mm_srli_si128(x, 1);
      // x = _mm_srli_si128(x, 1) | _mm_srli_si128(x, 15);
    }
    return _mm_cvtsi128_si64(h);
  }
};

/* ***************************************************
 * Murmur
 * ***************************************************/

template <const int L>
class murmur_64 {
  uint64_t table[L];

 public:
  void init() {
    for (int i = 0; i < L; i++) table[i] = getRandomUInt64();
  }
  uint64_t operator()(uint64_t k) {
    k ^= k >> 33;
    for (int i = 0; i < L; i++) {
      k *= table[i];
      k ^= k >> 33;
    }
    return k;
  }
};

#endif  // _FAST_HASHING_H_
