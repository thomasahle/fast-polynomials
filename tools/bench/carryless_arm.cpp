/**
 * ARM NEON benchmark for k-wise hash functions
 * Equivalent to carryless.cpp but for Apple Silicon / ARM64
 *
 * Compile: clang++ -O3 -std=c++17 -march=armv8-a+crypto carryless_arm.cpp -o bench_arm
 * Run:     ./bench_arm [nr_trials] [nr_times]
 */

#include <cmath>
#include <chrono>
#include <iostream>
#include <vector>
#include <algorithm>
#include <climits>

#include "framework/fast_hashing_arm.h"
#include "framework/injective_hashing_arm.h"
#include "framework/dietzfelbinger_hash.h"
#include "framework/randomgen.h"

using namespace std;

#ifndef FROM
#define FROM 2
#endif

#ifndef TO
#define TO 10
#endif

template <typename T>
uint64_t test_speed_function64(int nr_trials, int nr_times,
                               vector<uint64_t>& numbers) {
    volatile uint64_t x;
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

// Recursive template loop for testing all degrees
template<int n>
void test_speed_function64_loop(int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    cout << "Degree " << n << endl;

    cout << "Mersenne (traditional): ";
    test_speed_function64<poly_64_normal<n>>(nr_trials, nr_times, numbers);

    cout << "Mersenne (Mikkel): ";
    test_speed_function64<poly_64<n>>(nr_trials, nr_times, numbers);

    cout << "Mersenne, smart: ";
    test_speed_function64<smartpoly_64<n>>(nr_trials, nr_times, numbers);

    cout << "Carryless: ";
    test_speed_function64<carryless_64<n>>(nr_trials, nr_times, numbers);

    cout << "Lemire: ";
    test_speed_function64<lemire_64<n>>(nr_trials, nr_times, numbers);

    cout << "Estrin: ";
    test_speed_function64<estrin_64<n>>(nr_trials, nr_times, numbers);

    cout << "Rabin Winograd: ";
    test_speed_function64<rw_64<n>>(nr_trials, nr_times, numbers);

    cout << "Smart CL: ";
    test_speed_function64<smartcl_64<n>>(nr_trials, nr_times, numbers);

    // Dietzfelbinger bound: W >= 127 + ceil(log2(k*(k-1)/2))
    // W=128 only valid for k=2, W=192 needed for k>=3
    if constexpr (n == 2) {
        cout << "Dietz-128 (W=128, valid): ";
        test_speed_function64<dietz_128_opt<n>>(nr_trials, nr_times, numbers);
    } else {
        cout << "Dietz-128 (W=128, INVALID for k>=3): ";
        test_speed_function64<dietz_128_opt<n>>(nr_trials, nr_times, numbers);
    }

    cout << "Dietz-192 (W=192, valid for k<=~2^33): ";
    test_speed_function64<dietz_192<n>>(nr_trials, nr_times, numbers);

    // Continue recursion
    test_speed_function64_loop<n + 1>(nr_trials, nr_times, numbers);
}

// Recursion terminator
template<>
void test_speed_function64_loop<TO>(int, int, vector<uint64_t>&) {
    // End of recursion
}

void test_speed64(int nr_trials, int nr_times) {
    poly_64<2> rng;
    rng.init();

    vector<uint64_t> numbers;
    for (int i = 0; i < nr_trials; ++i) {
        numbers.push_back(rng(i));
    }

    cout << "Tabulation 8x2^8: ";
    test_speed_function64<tabulation_64>(nr_trials, nr_times, numbers);

    cout << "Dietz 2-wise (specialized): ";
    test_speed_function64<dietz_2wise>(nr_trials, nr_times, numbers);

    cout << "Thorup pair-multiply: ";
    test_speed_function64<thorup_pair_64>(nr_trials, nr_times, numbers);
    cout << endl;

    // Test degrees FROM to TO-1
    test_speed_function64_loop<FROM>(nr_trials, nr_times, numbers);
}

// Universal hash benchmark - compares methods for hashing 2N values
template<int n>
void test_universal_hash(int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    cout << "N=" << n << " (2N=" << 2*n << " blocks)" << endl;

    cout << "  Horner (2N-1 mults):      ";
    test_speed_function64<univ_horner_64<n>>(nr_trials, nr_times, numbers);

    cout << "  Horner-Unrolled:          ";
    test_speed_function64<horner_unrolled_64<2*n>>(nr_trials, nr_times, numbers);

    cout << "  Horner-Parallel:          ";
    test_speed_function64<horner_parallel_64<2*n>>(nr_trials, nr_times, numbers);

    cout << "  Injective (N mults):      ";
    test_speed_function64<univ_injective_64<n>>(nr_trials, nr_times, numbers);

    cout << "  Injective-Parallel (3N):  ";
    test_speed_function64<univ_injective_parallel_64<n>>(nr_trials, nr_times, numbers);

    cout << "  Injective-Lanes (N+L):    ";
    test_speed_function64<univ_injective_lanes_64<n, (n < 8 ? n : 8)>>(nr_trials, nr_times, numbers);

    cout << "  CLNH (multilinear):       ";
    test_speed_function64<clnh_64<n>>(nr_trials, nr_times, numbers);

    cout << "  BRW (recursive):          ";
    test_speed_function64<univ_brw_64<2*n>>(nr_trials, nr_times, numbers);

    cout << "  c-decBRW (c=2):           ";
    test_speed_function64<univ_c2_decbrw_64<2*n>>(nr_trials, nr_times, numbers);

    cout << "  c-decBRW (c=4):           ";
    test_speed_function64<univ_c4_decbrw_64<2*n>>(nr_trials, nr_times, numbers);

    cout << endl;
}

void test_injective(int nr_trials, int nr_times) {
    poly_64<2> rng;
    rng.init();

    vector<uint64_t> numbers;
    for (int i = 0; i < nr_trials; ++i) {
        numbers.push_back(rng(i));
    }

    cout << endl;
    cout << "Universal Hash Comparison" << endl;
    cout << "=========================" << endl;
    cout << "(Compares methods for hashing 2N values)" << endl;
    cout << endl;

    // Small sizes
    test_universal_hash<4>(nr_trials, nr_times, numbers);
    test_universal_hash<8>(nr_trials, nr_times, numbers);
    test_universal_hash<16>(nr_trials, nr_times, numbers);
    test_universal_hash<32>(nr_trials, nr_times, numbers);
    test_universal_hash<64>(nr_trials, nr_times, numbers);
    test_universal_hash<128>(nr_trials, nr_times, numbers);
}

// 128-bit hash benchmark
template <typename HashFunc>
void test_speed_function128(int nr_trials, int nr_times, const vector<uint64_t>& numbers) {
    HashFunc hash;
    hash.init();

    vector<double> times;
    for (int t = 0; t < nr_times; ++t) {
        auto start = chrono::high_resolution_clock::now();
        hash128_t h(0, 0);
        for (int j = 0; j < nr_trials; ++j) {
            h = h ^ hash(numbers[j]);
        }
        auto end = chrono::high_resolution_clock::now();
        volatile uint64_t sink = h.lo ^ h.hi;
        (void)sink;
        times.push_back(chrono::duration_cast<chrono::microseconds>(end - start).count());
    }

    double mean = 0, var = 0;
    for (double t : times) mean += t;
    mean /= times.size();
    for (double t : times) var += (t - mean) * (t - mean);
    var = sqrt(var / times.size());
    double minv = *min_element(times.begin(), times.end());

    cout << "Mean: " << mean << " ± " << var << " min " << minv << endl;
}

template <int n>
void test_128bit_hash(int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    cout << "N=" << n << " (2N=" << 2*n << " keys)" << endl;

    cout << "  CLNH-128 (full product):  ";
    test_speed_function128<clnh_128<n>>(nr_trials, nr_times, numbers);

    cout << "  CLNH 2×64 (two hashes):   ";
    test_speed_function128<clnh_2x64<n>>(nr_trials, nr_times, numbers);

    cout << "  Poly GF(2^128) Horner:    ";
    test_speed_function128<poly_gf128<2*n>>(nr_trials, nr_times, numbers);

    cout << endl;
}

void test_128bit(int nr_trials, int nr_times) {
    poly_64<2> rng;
    rng.init();

    vector<uint64_t> numbers;
    for (int i = 0; i < nr_trials; ++i) {
        numbers.push_back(rng(i));
    }

    cout << endl;
    cout << "128-bit Hash Comparison" << endl;
    cout << "=======================" << endl;
    cout << endl;

    test_128bit_hash<4>(nr_trials, nr_times, numbers);
    test_128bit_hash<8>(nr_trials, nr_times, numbers);
    test_128bit_hash<16>(nr_trials, nr_times, numbers);
    test_128bit_hash<32>(nr_trials, nr_times, numbers);
    test_128bit_hash<64>(nr_trials, nr_times, numbers);
}

int main(int argc, char* argv[]) {
    double nr_trials = 1e6;
    double nr_times = 1e2;

    if (argc >= 3) {
        nr_trials = stod(argv[1]);
        nr_times = stod(argv[2]);
    }

    init_randomness();

    cout << "ARM NEON Benchmark" << endl;
    cout << "==================" << endl;
    cout << "Trials per test: " << (int)nr_trials << endl;
    cout << "Repetitions: " << (int)nr_times << endl;
    cout << endl;

    test_speed64(nr_trials, nr_times);
    test_injective(nr_trials, nr_times);
    test_128bit(nr_trials, nr_times);

#ifdef DEBUG
    cout << "Random bytes used: " << usedBytes << endl;
#endif

    return 0;
}
