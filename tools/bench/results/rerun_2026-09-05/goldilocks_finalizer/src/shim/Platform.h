/* Minimal stand-in for SMHasher3's Platform.h so that hashes/chainhash_goldi_exp.cpp
 * compiles standalone (microbenchmark and cross-checks).  x86-64: PCLMUL backend;
 * AArch64: PMULL backend.  Not used inside SMHasher3. */
#pragma once
#include <stdint.h>
#include <stddef.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#define FORCE_INLINE inline __attribute__((always_inline))
#define NEVER_INLINE __attribute__((noinline))
#define likely(x)   __builtin_expect(!!(x), 1)
#define unlikely(x) __builtin_expect(!!(x), 0)
typedef uint64_t seed_t;
#if defined(__x86_64__)
  #define HAVE_X86_64_CLMUL 1
#elif defined(__aarch64__)
  #define HAVE_ARM_NEON 1
  #define HAVE_ARM_AES 1
#endif
template <bool bswap> static FORCE_INLINE uint64_t GET_U64(const uint8_t* p, size_t off) { uint64_t v; memcpy(&v, p + off, 8); return bswap ? __builtin_bswap64(v) : v; }
template <bool bswap> static FORCE_INLINE void PUT_U64(uint64_t v, uint8_t* p, size_t off) { if (bswap) v = __builtin_bswap64(v); memcpy(p + off, &v, 8); }
