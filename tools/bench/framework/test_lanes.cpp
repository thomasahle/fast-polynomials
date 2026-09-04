/* ***********************************************
 * Correctness test for univ_injective_lanes_64<N, L>
 * (injective_hashing_arm.h on ARM, injective_hashing.h on x86).
 *
 * For every N in {1,2,3,4,5,7,8,9,16,31,32,64,128}, every
 * L in {1,2,3,4,8} with L <= N, and 20 deterministic random keys
 * (plus the edge keys x = 0 and x = 1), the test
 *   - builds the object and reads its message back via a()/b();
 *   - recomputes, here and using only inj_smul, the sequential
 *     recurrence P = x; P = a ^ (b ^ c)(P ^ x^2) of every lane
 *     (lane j owns pairs j, j+L, j+2L, ...), and the specified combine:
 *       single key: H = sum_j P_j x^{jD}, D = 3 ceil(N/L) + 3, with x^D
 *                   obtained by a plain loop of D multiplications;
 *       two keys:   H = sum_j P_j y^j (Horner in y);
 *   - asserts equality with both operator() overloads.
 * For L = 1 it additionally asserts that both overloads equal the
 * univ_injective_64-style sequential evaluation of the whole message.
 *
 * Run from tools/bench/ (init() draws the message from bytes1.bin).
 * Build (native ARM):
 *   clang++ -O3 -std=c++17 -march=armv8-a+crypto framework/test_lanes.cpp
 * Build (x86 cross, run under Rosetta with `arch -x86_64`):
 *   clang++ -O3 -std=c++17 -target x86_64-apple-macos12 -mpclmul -msse4.1 framework/test_lanes.cpp
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

static const int NUM_KEYS = 20;
static const uint64_t SEED = 0x243F6A8885A308D3ULL;

static uint64_t splitmix64(uint64_t& state) {
    uint64_t z = (state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static long g_checks = 0;
static long g_failures = 0;
static long g_pairs = 0;

static void expect_eq(const char* what, int N, int L, int k,
                      uint64_t got, uint64_t want) {
    g_checks++;
    if (got != want) {
        g_failures++;
        printf("FAIL %-28s N=%-3d L=%d key#%-2d got %016llx want %016llx\n",
               what, N, L, k, (unsigned long long)got,
               (unsigned long long)want);
    }
}

/* ---------- independent reference implementation ---------- */

// Sequential recurrence of lane j (pairs j, j+L, j+2L, ... < N),
// multiplier constant c (= x^3 single-key, = y two-key).
static uint64_t ref_lane(const uint64_t* a, const uint64_t* b, int N, int L,
                         int j, uint64_t x, uint64_t x2, uint64_t c) {
    uint64_t P = x;
    for (int i = j; i < N; i += L) {
        P = a[i] ^ inj_smul(b[i] ^ c, P ^ x2);
    }
    return P;
}

// Single key: H = sum_j P_j x^{jD}, D = 3 ceil(N/L) + 3,
// x^D by a plain loop of D multiplications (no square-and-multiply).
static uint64_t ref_single(const uint64_t* a, const uint64_t* b, int N, int L,
                           uint64_t x) {
    uint64_t x2 = inj_smul(x, x);
    uint64_t x3 = inj_smul(x2, x);
    int D = 3 * ((N + L - 1) / L) + 3;
    uint64_t xD = 1;  // multiplicative identity of GF(2^64)
    for (int k = 0; k < D; k++) xD = inj_smul(xD, x);
    uint64_t H = ref_lane(a, b, N, L, L - 1, x, x2, x3);
    for (int j = L - 2; j >= 0; j--) {
        H = inj_smul(H, xD) ^ ref_lane(a, b, N, L, j, x, x2, x3);
    }
    return H;
}

// Two keys: H = sum_j P_j y^j (Horner in y).
static uint64_t ref_two(const uint64_t* a, const uint64_t* b, int N, int L,
                        uint64_t x, uint64_t y) {
    uint64_t x2 = inj_smul(x, x);
    uint64_t H = ref_lane(a, b, N, L, L - 1, x, x2, y);
    for (int j = L - 2; j >= 0; j--) {
        H = inj_smul(H, y) ^ ref_lane(a, b, N, L, j, x, x2, y);
    }
    return H;
}

// univ_injective_64-style sequential evaluation of the whole message.
static uint64_t ref_sequential1(const uint64_t* a, const uint64_t* b, int N,
                                uint64_t x) {
    uint64_t x2 = inj_smul(x, x);
    uint64_t x3 = inj_smul(x2, x);
    uint64_t P = x;
    for (int i = 0; i < N; i++) P = a[i] ^ inj_smul(b[i] ^ x3, P ^ x2);
    return P;
}

static uint64_t ref_sequential2(const uint64_t* a, const uint64_t* b, int N,
                                uint64_t x, uint64_t y) {
    uint64_t x2 = inj_smul(x, x);
    uint64_t P = x;
    for (int i = 0; i < N; i++) P = a[i] ^ inj_smul(b[i] ^ y, P ^ x2);
    return P;
}

// Independent keys: lane j uses x_j (P_0 = x_j, x_j^2, x_j^3); H = XOR_j x_j * P_j.
static uint64_t ref_indep(const uint64_t* a, const uint64_t* b, int N, int L,
                          const uint64_t* xs) {
    uint64_t H = 0;
    for (int j = 0; j < L; j++) {
        uint64_t x2 = inj_smul(xs[j], xs[j]);
        uint64_t x3 = inj_smul(x2, xs[j]);
        H ^= inj_smul(ref_lane(a, b, N, L, j, xs[j], x2, x3), xs[j]);
    }
    return H;
}

/* ---------- driver ---------- */

template <int N, int L>
static void check_one_key(univ_injective_lanes_64<N, L>& h, int k,
                          uint64_t x, uint64_t y) {
    const uint64_t* a = h.a();
    const uint64_t* b = h.b();
    expect_eq("single-key vs reference", N, L, k, h(x), ref_single(a, b, N, L, x));
    expect_eq("two-key vs reference", N, L, k, h(x, y), ref_two(a, b, N, L, x, y));
    {   // independent per-lane keys derived deterministically from (x, y)
        uint64_t st = x ^ (y * 0x9E3779B97F4A7C15ULL) ^ (uint64_t)k;
        uint64_t xs[L];
        for (int j = 0; j < L; j++) xs[j] = splitmix64(st);
        expect_eq("independent-key vs reference", N, L, k, h(xs), ref_indep(a, b, N, L, xs));
        if (L == 1) expect_eq("L=1 independent-key vs x*sequential", N, L, k, h(xs),
                              inj_smul(ref_sequential1(a, b, N, xs[0]), xs[0]));
    }
    if (L == 1) {
        expect_eq("L=1 single-key vs sequential", N, L, k, h(x),
                  ref_sequential1(a, b, N, x));
        expect_eq("L=1 two-key vs sequential", N, L, k, h(x, y),
                  ref_sequential2(a, b, N, x, y));
    }
}

template <int N, int L>
static void check() {
    univ_injective_lanes_64<N, L> h;
    h.init();  // message from bytes1.bin, exactly as the benchmark does
    uint64_t st = SEED ^ ((uint64_t)N * 131 + (uint64_t)L);
    for (int k = 0; k < NUM_KEYS; k++) {
        uint64_t x = splitmix64(st);
        uint64_t y = splitmix64(st);
        check_one_key<N, L>(h, k, x, y);
    }
    // Edge keys: x = 0 (all powers vanish) and x = 1 (all powers are 1).
    check_one_key<N, L>(h, NUM_KEYS, 0, splitmix64(st));
    check_one_key<N, L>(h, NUM_KEYS + 1, 1, splitmix64(st));
    g_pairs++;
}

template <int N>
static void check_all_L() {
    check<N, 1>();
    if constexpr (N >= 2) check<N, 2>();
    if constexpr (N >= 3) check<N, 3>();
    if constexpr (N >= 4) check<N, 4>();
    if constexpr (N >= 8) check<N, 8>();
}

int main() {
    init_randomness();  // reads bytes1.bin from the current directory
    if (randomBytes.empty()) {
        fprintf(stderr, "ERROR: bytes1.bin not found in cwd (run from tools/bench/)\n");
        return 1;
    }
    fprintf(stderr, "platform=%s keys=%d(+2 edge) seed=%016llx\n", PORT_PLATFORM,
            NUM_KEYS, (unsigned long long)SEED);

    check_all_L<1>();
    check_all_L<2>();
    check_all_L<3>();
    check_all_L<4>();
    check_all_L<5>();
    check_all_L<7>();
    check_all_L<8>();
    check_all_L<9>();
    check_all_L<16>();
    check_all_L<31>();
    check_all_L<32>();
    check_all_L<64>();
    check_all_L<128>();

    printf("univ_injective_lanes_64: %ld (N,L) pairs, %ld checks, %ld failures\n",
           g_pairs, g_checks, g_failures);
    printf("random bytes consumed: %d\n", usedBytes);
    return g_failures == 0 ? 0 : 2;
}
