/* ***********************************************
 * Port-equivalence test for injective_hashing.h (x86, PCLMULQDQ)
 * versus injective_hashing_arm.h (ARM NEON).
 *
 * Builds the platform's header, seeds every class exactly the way the
 * benchmarks do (init() draws from bytes1.bin via randomgen.h, in the
 * same order on both platforms), hashes 200 deterministic messages
 * (splitmix64 from a fixed seed) per (class, N), and prints one 64-bit
 * checksum per (class, N).  Run from tools/bench/ (bytes1.bin is opened by
 * relative path); diff the native and x86 outputs.
 *
 * Build (native ARM):
 *   clang++ -O3 -std=c++17 -march=armv8-a+crypto test_port_equiv.cpp
 * Build (x86 cross, run under Rosetta with `arch -x86_64`):
 *   clang++ -O3 -std=c++17 -target x86_64-apple-macos12 -mpclmul -msse4.1 test_port_equiv.cpp
 * ***********************************************/

#include <cstdint>
#include <cstdio>
#include <iostream>

#if defined(__aarch64__)
#include "injective_hashing_arm.h"
#define PORT_PLATFORM "arm64"
#else
#include "injective_hashing.h"
#define PORT_PLATFORM "x86_64"
#endif

static const int NUM_MSGS = 200;
static const uint64_t SEED = 0x9E3779B97F4A7C15ULL;

static uint64_t splitmix64(uint64_t& state) {
    uint64_t z = (state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

// Order-sensitive fold of a 64-bit value into the running checksum.
static inline void fold(uint64_t& acc, uint64_t v) {
    acc = (acc ^ v) * 0x100000001B3ULL;  // FNV-style multiply
    acc ^= acc >> 29;
}

static void report(const char* cls, size_t n, const char* variant, uint64_t acc) {
    // Print in a fixed, locale-independent format.
    printf("%-28s N=%-4zu %-6s %016llx\n", cls, n, variant,
           (unsigned long long)acc);
}

// 64-bit output, single-key operator()(x)
template <typename H>
static void run1(const char* cls, size_t n) {
    H h;
    h.init();
    uint64_t st = SEED, acc = 0;
    for (int i = 0; i < NUM_MSGS; i++) {
        fold(acc, h(splitmix64(st)));
    }
    report(cls, n, "1key", acc);
}

// 64-bit output, two-key operator()(x, y)
template <typename H>
static void run2(const char* cls, size_t n) {
    H h;
    h.init();
    uint64_t st = SEED, acc = 0;
    for (int i = 0; i < NUM_MSGS; i++) {
        uint64_t x = splitmix64(st);
        uint64_t y = splitmix64(st);
        fold(acc, h(x, y));
    }
    report(cls, n, "2key", acc);
}

// 128-bit output, single-key operator()(x)
template <typename H>
static void run1_128(const char* cls, size_t n) {
    H h;
    h.init();
    uint64_t st = SEED, acc = 0;
    for (int i = 0; i < NUM_MSGS; i++) {
        hash128_t r = h(splitmix64(st));
        fold(acc, r.lo);
        fold(acc, r.hi);
    }
    report(cls, n, "1key", acc);
}

// 128-bit output, two-key operator()(x_lo, x_hi)
template <typename H>
static void run2_128(const char* cls, size_t n) {
    H h;
    h.init();
    uint64_t st = SEED, acc = 0;
    for (int i = 0; i < NUM_MSGS; i++) {
        uint64_t x = splitmix64(st);
        uint64_t y = splitmix64(st);
        hash128_t r = h(x, y);
        fold(acc, r.lo);
        fold(acc, r.hi);
    }
    report(cls, n, "2key", acc);
}

// Mirrors the instantiations in carryless_arm.cpp:
//   test_universal_hash<n> and test_128bit_hash<n>.
template <size_t n>
static void run_all() {
    run1<univ_horner_64<n>>("univ_horner_64", n);
    run1<horner_unrolled_64<2*n>>("horner_unrolled_64", 2*n);
    run1<horner_parallel_64<2*n>>("horner_parallel_64", 2*n);
    run1<univ_injective_64<n>>("univ_injective_64", n);
    run2<univ_injective_64<n>>("univ_injective_64", n);
    run1<univ_injective_parallel_64<n>>("univ_injective_parallel_64", n);
    run2<univ_injective_parallel_64<n>>("univ_injective_parallel_64", n);
    run1<univ_injective_lanes_64<(int)n, ((int)n < 8 ? (int)n : 8)>>("univ_injective_lanes_64", n);
    run2<univ_injective_lanes_64<(int)n, ((int)n < 8 ? (int)n : 8)>>("univ_injective_lanes_64", n);
    run1<clnh_64<n>>("clnh_64", n);
    run1<univ_brw_64<2*n>>("univ_brw_64", 2*n);
    run1<univ_c2_decbrw_64<2*n>>("univ_c2_decbrw_64", 2*n);
    run1<univ_c4_decbrw_64<2*n>>("univ_c4_decbrw_64", 2*n);
    run1_128<clnh_128<n>>("clnh_128", n);
    run1_128<clnh_2x64<n>>("clnh_2x64", n);
    run1_128<poly_gf128<2*n>>("poly_gf128", 2*n);
    run2_128<poly_gf128<2*n>>("poly_gf128", 2*n);
}

int main() {
    init_randomness();  // reads bytes1.bin from the current directory
    if (randomBytes.empty()) {
        fprintf(stderr, "ERROR: bytes1.bin not found in cwd\n");
        return 1;
    }
    // Platform tag goes to stderr so that stdout is byte-identical across
    // the ARM and x86 builds and can be diffed directly.
    fprintf(stderr, "platform=%s msgs=%d seed=%016llx\n", PORT_PLATFORM,
            NUM_MSGS, (unsigned long long)SEED);

    // Standalone primitive checks (exercise every helper directly).
    {
        uint64_t st = SEED, acc = 0;
        for (int i = 0; i < NUM_MSGS; i++) {
            uint64_t a = splitmix64(st), b = splitmix64(st);
            auto prod = poly_to_u8(clmul_lo_lo(from64(a), from64(b)));
            fold(acc, lower64(prod));
            fold(acc, upper64(prod));
            fold(acc, inj_smul(a, b));
            auto x = xor128(prod, from64(a));
            fold(acc, lower64(x));
            fold(acc, upper64(x));
            hash128_t g = gf128_mul(hash128_t(a, b), hash128_t(b ^ 1, a ^ 2));
            fold(acc, g.lo);
            fold(acc, g.hi);
        }
        report("primitives", 0, "-", acc);
    }

    run_all<4>();
    run_all<8>();
    run_all<16>();
    run_all<32>();
    run_all<64>();
    run_all<128>();

    printf("random bytes consumed: %d\n", usedBytes);
    return 0;
}
