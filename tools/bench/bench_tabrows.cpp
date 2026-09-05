/**
 * All rows of the tabulation-comparison table (Section 5.7 of the paper),
 * timed under one wrapper and one protocol on each platform:
 *   MurmurHash3, xxHash64 (the functions of bench_nonpoly_arm.cpp, copied
 *   verbatim below), Tabulation (tabulation_64, 8 x 2^8, as in
 *   carryless*.cpp), Dietzfelbinger k=3/5/7 (dietz_192<k>, W=192 as stated
 *   in the paper; framework/dietzfelbinger_hash.h), and the polynomial rows
 *   "This Paper" k=3 (smartcl_64<3>), the two quartic circuits over GF(2^64)
 *   (quartic2_64: Motzkin, 2 multiplications, 3-wise; quartic3_64: 3
 *   multiplications, 4-wise), Motzkin's quartic over 2^61-1 (motzkin_61, 2
 *   multiplications, 4-wise), k=5 (smartcl_64<5>) and k=7 (smartcl_64<7>).
 *   The platform's own smartcl_64<4> is timed too as a cross-check (it is
 *   quartic2_64 on ARM and quartic3_64 on x86).
 *
 * Wrapper and protocol are those of carryless.cpp / carryless_arm.cpp:
 * 1e6 inputs from poly_64<2>, 2*nr_times repetitions with a fresh init(),
 * the fastest nr_times kept, mean +/- std in microseconds per 1e6 hashes.
 *
 * Compile (ARM): clang++ -O3 -std=c++17 -march=armv8-a+crypto bench_tabrows.cpp -o bench_tabrows
 * Compile (x86): clang++ -O3 -std=c++17 -march=native bench_tabrows.cpp -o bench_tabrows
 * Run:  ./bench_tabrows [nr_trials] [nr_times]     (defaults 1e6 100, as in the paper)
 *       ./bench_tabrows selftest                    (quartic2_64, quartic3_64, motzkin_61
 *                                                    against Horner + decoders)
 */

#include <cmath>
#include <chrono>
#include <iostream>
#include <vector>
#include <algorithm>
#include <climits>
#include <cstdlib>
#include <cstring>

#if defined(__aarch64__)
#include "framework/fast_hashing_arm.h"
#else
#include <x86intrin.h>
#include "framework/fast_hashing.h"
#endif
#include "framework/dietzfelbinger_hash.h"
#include "framework/randomgen.h"

using namespace std;

/* ------------------------------------------------------------------ */
/* MurmurHash3 / xxHash64: copied verbatim from bench_nonpoly_arm.cpp   */
/* ------------------------------------------------------------------ */

// MurmurHash3 finalizer (64-bit) - the mixing function
// This is the standard MurmurHash3 64-bit finalizer
inline uint64_t murmur3_64(uint64_t k) {
    k ^= k >> 33;
    k *= 0xff51afd7ed558ccdULL;
    k ^= k >> 33;
    k *= 0xc4ceb9fe1a85ec53ULL;
    k ^= k >> 33;
    return k;
}

// xxHash64 - simplified single 64-bit input version
// Based on xxHash by Yann Collet
static const uint64_t PRIME64_1 = 0x9E3779B185EBCA87ULL;
static const uint64_t PRIME64_2 = 0xC2B2AE3D27D4EB4FULL;
static const uint64_t PRIME64_3 = 0x165667B19E3779F9ULL;
static const uint64_t PRIME64_4 = 0x85EBCA77C2B2AE63ULL;
static const uint64_t PRIME64_5 = 0x27D4EB2F165667C5ULL;

inline uint64_t rotl64(uint64_t x, int r) {
    return (x << r) | (x >> (64 - r));
}

inline uint64_t xxhash64(uint64_t input, uint64_t seed = 0) {
    uint64_t h64 = seed + PRIME64_5 + 8;  // 8 bytes of input

    // Process the 8 bytes
    uint64_t k1 = input * PRIME64_2;
    k1 = rotl64(k1, 31);
    k1 *= PRIME64_1;
    h64 ^= k1;
    h64 = rotl64(h64, 27) * PRIME64_1 + PRIME64_4;

    // Final avalanche
    h64 ^= h64 >> 33;
    h64 *= PRIME64_2;
    h64 ^= h64 >> 29;
    h64 *= PRIME64_3;
    h64 ^= h64 >> 32;

    return h64;
}

// Wrapper classes to match the benchmark interface
class MurmurHash3_64 {
public:
    void init() {}
    uint64_t operator()(uint64_t k) {
        return murmur3_64(k);
    }
};

class XXHash64 {
    uint64_t seed;
public:
    void init() {
        seed = 0x1234567890abcdefULL;
    }
    uint64_t operator()(uint64_t k) {
        return xxhash64(k, seed);
    }
};

/* ------------------------------------------------------------------ */
/* Timing wrapper: same as carryless_arm.cpp (ARM) / carryless.cpp (x86) */
/* ------------------------------------------------------------------ */

template <typename T>
uint64_t test_speed_function64(int nr_trials, int nr_times,
                               vector<uint64_t>& numbers) {
#if defined(__aarch64__)
    volatile uint64_t x;
#else
    volatile __uint128_t x;
#endif
    vector<uint64_t> times;

    // First half is warmup
    for (int i = 0; i < 2 * nr_times; ++i) {
        T hash;
        hash.init();

        for (int j = 0; j < nr_trials; ++j) {
            x = hash(numbers[j]);
        }
        auto start = chrono::high_resolution_clock::now();
        for (int j = 0; j < nr_trials; ++j) {
            x = hash(numbers[j]);
        }
        auto end = chrono::high_resolution_clock::now();
        times.push_back(
            chrono::duration_cast<chrono::microseconds>(end - start).count());
    }

    std::sort(times.begin(), times.end());
    times.erase(times.begin() + nr_times, times.end());

    long double mean = 0;
    for (int i = 0; i < nr_times; ++i) {
        mean += times[i];
    }
    mean = mean / nr_times;

    long double MSE = 0;
    for (int i = 0; i < nr_times; ++i) {
        MSE += (times[i] - mean) * (times[i] - mean);
    }
    MSE = MSE / nr_times;

    long double min_time = times[0];

    cout << "Mean: " << mean << " ± " << sqrt(MSE) << " min " << min_time << endl;

    return (uint64_t)mean;
}

/* ------------------------------------------------------------------ */
/* Self-tests                                                          */
/* ------------------------------------------------------------------ */

static uint64_t splitmix64(uint64_t& s) {
    uint64_t z = (s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* --- GF(2^64) = GF(2)[x] / (x^64 + x^4 + x^3 + x + 1), reference arithmetic --- */

// Shift-and-add reference product (independent of the CLMUL/PMULL code paths).
static uint64_t gf_mul_ref(uint64_t a, uint64_t b) {
    uint64_t r = 0;
    for (int i = 0; i < 64; ++i) {
        if ((b >> i) & 1) r ^= a;
        uint64_t hi = a >> 63;
        a <<= 1;
        if (hi) a ^= 27;  // x^64 = x^4 + x^3 + x + 1
    }
    return r;
}

// Horner evaluation of the monic quartic x^4 + c[3] x^3 + c[2] x^2 + c[1] x + c[0] in GF(2^64)
static uint64_t horner_gf64(const uint64_t c[4], uint64_t x) {
    uint64_t h = 1;
    for (int i = 3; i >= 0; --i) h = gf_mul_ref(h, x) ^ c[i];
    return h;
}

// Expanded coefficients of Motzkin's circuit in characteristic 2:
//   y = x (x + a0) + a1,  P = y (y + x + a2) + a3
//   = x^4 + 1 x^3 + (a0^2 + a0 + a2) x^2 + (a0 a2 + a1) x + (a1^2 + a1 a2 + a3)
static void encode_quartic2(const uint64_t a[4], uint64_t c[4]) {
    c[3] = 1;  // 2 a0 + 1 = 1: the x^3 coefficient never depends on the keys
    c[2] = gf_mul_ref(a[0], a[0]) ^ a[0] ^ a[2];
    c[1] = gf_mul_ref(a[0], a[2]) ^ a[1];
    c[0] = gf_mul_ref(a[1], a[1]) ^ gf_mul_ref(a[1], a[2]) ^ a[3];
}

// Expanded coefficients of the three-multiplication circuit:
//   y = x^2, z = (x + a0)(y + a1), t = (z + a2) x, P = t + a3
//   = x^4 + a0 x^3 + a1 x^2 + (a0 a1 + a2) x + a3
static void encode_quartic3(const uint64_t a[4], uint64_t c[4]) {
    c[3] = a[0];
    c[2] = a[1];
    c[1] = gf_mul_ref(a[0], a[1]) ^ a[2];
    c[0] = a[3];
}

// Closed-form decoder for quartic3_64 (bijection onto the monic quartics):
//   a0 = c3, a1 = c2, a2 = c1 + c3 c2, a3 = c0.
static void decode_quartic3(const uint64_t c[4], uint64_t a[4]) {
    a[0] = c[3];
    a[1] = c[2];
    a[2] = c[1] ^ gf_mul_ref(c[3], c[2]);
    a[3] = c[0];
}

template <typename H, void (*ENCODE)(const uint64_t[4], uint64_t[4])>
static bool check_gf64_circuit(const char* name, uint64_t& seed, uint64_t& checked) {
    const uint64_t extremes[] = {0, 1, 2, 3, 27, (1ULL << 63), (1ULL << 63) | 27, ~0ULL, ~0ULL - 1,
                                 0x8000000000000001ULL, 0x5555555555555555ULL, 0xAAAAAAAAAAAAAAAAULL};
    const int n_ext = sizeof(extremes) / sizeof(extremes[0]);
    const uint64_t kext[] = {0, 1, 27, ~0ULL, (1ULL << 63), 0x8000000000000001ULL};
    const int n_kext = sizeof(kext) / sizeof(kext[0]);
    H h;
    auto check_keys = [&](const uint64_t a[4], int n_random) -> bool {
        uint64_t c[4];
        ENCODE(a, c);
        h.set_keys(a[0], a[1], a[2], a[3]);
        for (int i = 0; i < n_ext + n_random; ++i) {
            uint64_t x = i < n_ext ? extremes[i] : splitmix64(seed);
            uint64_t got = (uint64_t)h(x), want = horner_gf64(c, x);
            ++checked;
            if (got != want) {
                cerr << name << " MISMATCH keys=(" << a[0] << "," << a[1] << "," << a[2] << ","
                     << a[3] << ") x=" << x << " got=" << got << " want=" << want << endl;
                return false;
            }
        }
        return true;
    };
    // (1) random keys, extreme + random inputs
    for (int t = 0; t < 64; ++t) {
        uint64_t a[4];
        for (int i = 0; i < 4; ++i) a[i] = splitmix64(seed);
        if (!check_keys(a, 100000)) return false;
    }
    // (2) all 6^4 combinations of extreme keys
    for (int i0 = 0; i0 < n_kext; ++i0)
        for (int i1 = 0; i1 < n_kext; ++i1)
            for (int i2 = 0; i2 < n_kext; ++i2)
                for (int i3 = 0; i3 < n_kext; ++i3) {
                    uint64_t a[4] = {kext[i0], kext[i1], kext[i2], kext[i3]};
                    if (!check_keys(a, 500)) return false;
                }
    return true;
}

static int selftest_gf64() {
    uint64_t seed = 0x600d5eedULL, checked = 0;

    // Reference multiply sanity: x * x^63 = x^64 = 27 (mod P), and it agrees
    // with the platform multiply on random pairs.
    if (gf_mul_ref(2, 1ULL << 63) != 27) { cerr << "gf_mul_ref sanity failed" << endl; return 1; }

    // (A) quartic2_64 against Horner on the expanded polynomial (x^3 coefficient 1).
    if (!check_gf64_circuit<quartic2_64, encode_quartic2>("quartic2_64", seed, checked)) return 1;
    // (B) quartic3_64 against Horner on the expanded polynomial.
    if (!check_gf64_circuit<quartic3_64, encode_quartic3>("quartic3_64", seed, checked)) return 1;
    // (C) quartic3_64 decoder: random monic quartic c -> keys a; encode(a) == c and the
    //     circuit with keys a agrees with Horner on c.  Also records that the x^3
    //     coefficient c3 = a0 takes every value (it is the key itself).
    {
        quartic3_64 h;
        for (int t = 0; t < 64; ++t) {
            uint64_t c[4], a[4], c2[4];
            for (int i = 0; i < 4; ++i) c[i] = splitmix64(seed);
            decode_quartic3(c, a);
            encode_quartic3(a, c2);
            if (memcmp(c, c2, sizeof(c)) != 0 || a[0] != c[3]) {
                cerr << "quartic3_64 DECODER ROUNDTRIP FAILED at trial " << t << endl;
                return 1;
            }
            h.set_keys(a[0], a[1], a[2], a[3]);
            for (int i = 0; i < 20000; ++i) {
                uint64_t x = splitmix64(seed);
                uint64_t got = (uint64_t)h(x), want = horner_gf64(c, x);
                ++checked;
                if (got != want) { cerr << "quartic3_64 DECODER EVAL MISMATCH" << endl; return 1; }
            }
        }
    }
    cout << "quartic2_64 / quartic3_64 selftest: " << checked
         << " evaluations checked against Horner over GF(2^64), 64 random + 1296 extreme key sets each, "
         << "64 quartic3_64 decoder round-trips (a0 = c3, a1 = c2, a2 = c1 + c3 c2, a3 = c0): PASS" << endl;
    return 0;
}

/* --- motzkin_61 against Horner in GF(2^61 - 1) --- */

static const uint64_t P61 = ((uint64_t)1 << 61) - 1;

static uint64_t mulp(uint64_t a, uint64_t b) { return (uint64_t)(((__uint128_t)a * b) % P61); }
static uint64_t addp(uint64_t a, uint64_t b) { uint64_t t = a + b; return t >= P61 ? t - P61 : t; }
static uint64_t subp(uint64_t a, uint64_t b) { return a >= b ? a - b : a + P61 - b; }

// Horner evaluation of the monic quartic x^4 + a[3] x^3 + a[2] x^2 + a[1] x + a[0]
static uint64_t horner_quartic(const uint64_t a[4], uint64_t x) {
    x %= P61;
    uint64_t h = 1;
    for (int i = 3; i >= 0; --i) h = addp(mulp(h, x), a[i]);
    return h;
}

// Coefficients of y (y + x + b2) + b3 with y = x (x + b0) + b1.
static void encode_keys(const uint64_t b[4], uint64_t a[4]) {
    uint64_t b0 = b[0], b1 = b[1], b2 = b[2], b3 = b[3];
    uint64_t two_b0_1 = addp(addp(b0, b0), 1);
    a[3] = two_b0_1;                                                   // 2 b0 + 1
    a[2] = addp(addp(mulp(b0, b0), b0), addp(addp(b1, b1), b2));       // b0^2 + b0 + 2 b1 + b2
    a[1] = addp(mulp(b1, two_b0_1), mulp(b0, b2));                     // b1 (2 b0 + 1) + b0 b2
    a[0] = addp(addp(mulp(b1, b1), mulp(b1, b2)), b3);                 // b1^2 + b1 b2 + b3
}

// Closed-form decoder: b0 = (a3 - 1)/2, c = a2 - b0^2 - b0, b1 = a1 - b0 c,
// b2 = c - 2 b1, b3 = a0 - b1^2 - b1 b2.
static void decode_coeffs(const uint64_t a[4], uint64_t b[4]) {
    const uint64_t inv2 = (P61 + 1) / 2;  // 2^60 = 1/2 mod p
    uint64_t b0 = mulp(subp(a[3], 1), inv2);
    uint64_t c = subp(subp(a[2], mulp(b0, b0)), b0);
    uint64_t b1 = subp(a[1], mulp(b0, c));
    uint64_t b2 = subp(c, addp(b1, b1));
    uint64_t b3 = subp(subp(a[0], mulp(b1, b1)), mulp(b1, b2));
    b[0] = b0; b[1] = b1; b[2] = b2; b[3] = b3;
}

static int selftest_motzkin61() {
    uint64_t seed = 0x5eed5eed5eedULL;
    const uint64_t extremes[] = {0, 1, 2, P61 - 2, P61 - 1, P61, P61 + 1, P61 + 2,
                                 (1ULL << 61), (1ULL << 62), (1ULL << 63), (1ULL << 62) + (1ULL << 61),
                                 ~0ULL, ~0ULL - 1, ~0ULL - P61, ~0ULL - P61 + 1, ~0ULL - P61 - 1,
                                 7 * P61, 7 * P61 + 6, 0x8000000000000001ULL};
    const int n_ext = sizeof(extremes) / sizeof(extremes[0]);
    uint64_t checked = 0;
    motzkin_61 h;

    auto check_keys = [&](const uint64_t b[4], int n_random) -> bool {
        uint64_t a[4];
        encode_keys(b, a);
        h.set_keys(b[0], b[1], b[2], b[3]);
        for (int i = 0; i < n_ext + n_random; ++i) {
            uint64_t x = i < n_ext ? extremes[i] : splitmix64(seed);
            uint64_t got = h(x), want = horner_quartic(a, x);
            ++checked;
            if (got != want || got >= P61) {
                cerr << "MISMATCH keys=(" << b[0] << "," << b[1] << "," << b[2] << "," << b[3]
                     << ") x=" << x << " got=" << got << " want=" << want << endl;
                return false;
            }
        }
        return true;
    };

    // (1) Random keys, random and extreme inputs.
    for (int t = 0; t < 64; ++t) {
        uint64_t b[4];
        for (int i = 0; i < 4; ++i) b[i] = splitmix64(seed) % P61;
        if (!check_keys(b, 200000)) return 1;
    }
    // (2) Extreme keys (all-zero, all-max, mixed) with extreme and random inputs.
    const uint64_t kext[] = {0, 1, P61 - 1, P61 - 2, (1ULL << 60), (1ULL << 60) - 1};
    const int n_kext = sizeof(kext) / sizeof(kext[0]);
    for (int i0 = 0; i0 < n_kext; ++i0)
        for (int i1 = 0; i1 < n_kext; ++i1)
            for (int i2 = 0; i2 < n_kext; ++i2)
                for (int i3 = 0; i3 < n_kext; ++i3) {
                    uint64_t b[4] = {kext[i0], kext[i1], kext[i2], kext[i3]};
                    if (!check_keys(b, 500)) return 1;
                }
    // (3) Decoder: random monic quartics a -> keys b; encode(b) == a and the
    //     circuit with keys b agrees with Horner on a at random points.
    for (int t = 0; t < 64; ++t) {
        uint64_t a[4], b[4], a2[4];
        for (int i = 0; i < 4; ++i) a[i] = splitmix64(seed) % P61;
        decode_coeffs(a, b);
        encode_keys(b, a2);
        if (memcmp(a, a2, sizeof(a)) != 0) {
            cerr << "DECODER ROUNDTRIP FAILED at trial " << t << endl;
            return 1;
        }
        h.set_keys(b[0], b[1], b[2], b[3]);
        for (int i = 0; i < 20000; ++i) {
            uint64_t x = splitmix64(seed);
            uint64_t got = h(x), want = horner_quartic(a, x);
            ++checked;
            if (got != want) {
                cerr << "DECODER EVAL MISMATCH trial " << t << " x=" << x << endl;
                return 1;
            }
        }
    }
    // (4) Keys drawn by init() are in [0, p).
    for (int t = 0; t < 1000; ++t) {
        h.init();
        for (int i = 0; i < 4; ++i)
            if (h.keys()[i] >= P61) { cerr << "init() key out of range" << endl; return 1; }
    }
    cout << "motzkin_61 selftest: " << checked << " evaluations checked against Horner, "
         << "64 random + " << (n_kext * n_kext * n_kext * n_kext) << " extreme key sets, "
         << "64 decoder round-trips (b0 = (a3-1)/2, ...): PASS" << endl;
    return 0;
}

static int selftest() {
    if (selftest_gf64() != 0) return 1;
    if (selftest_motzkin61() != 0) return 1;
    return 0;
}

int main(int argc, char* argv[]) {
    if (argc >= 2 && strcmp(argv[1], "selftest") == 0) return selftest();

    double nr_trials = 1e6;
    double nr_times = 1e2;
    if (argc >= 3) {
        nr_trials = stod(argv[1]);
        nr_times = stod(argv[2]);
    }

    init_randomness();

#if defined(__aarch64__)
    cout << "Tabulation-table rows (ARM)" << endl;
#else
    cout << "Tabulation-table rows (x86)" << endl;
#endif
    cout << "Trials per test: " << (int)nr_trials << endl;
    cout << "Repetitions: " << (int)nr_times << endl << endl;

    poly_64<2> rng;
    rng.init();
    vector<uint64_t> numbers;
    for (int i = 0; i < nr_trials; ++i) numbers.push_back(rng(i));

    cout << "MurmurHash3 [murmur3_64 finalizer]: ";
    test_speed_function64<MurmurHash3_64>(nr_trials, nr_times, numbers);
    cout << "xxHash64 [xxhash64, 8-byte input]: ";
    test_speed_function64<XXHash64>(nr_trials, nr_times, numbers);
    cout << "Tabulation 8x2^8 [tabulation_64]: ";
    test_speed_function64<tabulation_64>(nr_trials, nr_times, numbers);
    cout << "Dietzfelbinger k=3 [dietz_192<3>]: ";
    test_speed_function64<dietz_192<3>>(nr_trials, nr_times, numbers);
    cout << "Dietzfelbinger k=5 [dietz_192<5>]: ";
    test_speed_function64<dietz_192<5>>(nr_trials, nr_times, numbers);
    cout << "Dietzfelbinger k=7 [dietz_192<7>]: ";
    test_speed_function64<dietz_192<7>>(nr_trials, nr_times, numbers);
    cout << "This Paper (k=3) [smartcl_64<3>]: ";
    test_speed_function64<smartcl_64<3>>(nr_trials, nr_times, numbers);
    cout << "Quartic GF(2^64), 2 mults, 3-wise [quartic2_64]: ";
    test_speed_function64<quartic2_64>(nr_trials, nr_times, numbers);
    cout << "Quartic GF(2^64), 3 mults, 4-wise [quartic3_64]: ";
    test_speed_function64<quartic3_64>(nr_trials, nr_times, numbers);
    cout << "Motzkin quartic 2^61-1, 2 mults, 4-wise [motzkin_61]: ";
    test_speed_function64<motzkin_61>(nr_trials, nr_times, numbers);
    cout << "This Paper (k=5) [smartcl_64<5>]: ";
    test_speed_function64<smartcl_64<5>>(nr_trials, nr_times, numbers);
    cout << "This Paper (k=7) [smartcl_64<7>]: ";
    test_speed_function64<smartcl_64<7>>(nr_trials, nr_times, numbers);
#if defined(__aarch64__)
    cout << "Cross-check: this platform's smartcl_64<4> (= quartic2_64 circuit): ";
#else
    cout << "Cross-check: this platform's smartcl_64<4> (= quartic3_64 circuit): ";
#endif
    test_speed_function64<smartcl_64<4>>(nr_trials, nr_times, numbers);

    return 0;
}
