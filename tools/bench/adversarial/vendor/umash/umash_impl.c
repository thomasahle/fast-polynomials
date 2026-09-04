/*
 * Thin wrapper translation unit for the vendored, VERBATIM upstream
 * umash.c (backtrace-labs/umash).  Its only purpose is to let umash.c
 * build under the benchmark harness's plain `-march=native` flags,
 * exactly the way tools/bench/adversarial/hashes.h already enables the ARM
 * PMULL path for its own GF(2^64) code with a per-function
 * `__attribute__((target("aes")))`.
 *
 * Upstream umash.c requires the CLMUL carry-less multiply:
 *   - x86-64: the __PCLMUL__ macro (from -mpclmul / -march=native with
 *     a CLMUL-capable CPU).  Nothing to do here; native already has it.
 *   - aarch64: the __ARM_FEATURE_CRYPTO macro AND codegen for the
 *     PMULL (vmull_p64) intrinsic.  Apple clang's `-march=native`
 *     does NOT define __ARM_FEATURE_CRYPTO, so we (a) define it so the
 *     upstream #error and platform selection pick the ARM path, and
 *     (b) push target("aes") over every function in umash.c so the
 *     PMULL intrinsic is emitted.  "aes" is the minimal feature that
 *     provides vmull_p64 and is what hashes.h already uses.
 *
 * The upstream sources (umash.c / umash.h / umash_long.inc) are left
 * byte-for-byte unmodified; all platform adaptation lives here.
 *
 * Compile as C:
 *   clang -O3 -std=c11 -march=native -c umash_impl.c -o umash_impl.o
 */
#if defined(__aarch64__) && !defined(__ARM_FEATURE_CRYPTO)
#define __ARM_FEATURE_CRYPTO 1
#pragma clang attribute push(__attribute__((target("aes"))), apply_to = function)
#define UMASH_IMPL_POPPED_ATTR 1
#endif

#include "umash.c"

#ifdef UMASH_IMPL_POPPED_ATTR
#pragma clang attribute pop
#undef UMASH_IMPL_POPPED_ATTR
#endif
