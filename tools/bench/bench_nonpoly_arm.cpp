/**
 * Benchmark for non-polynomial hash functions (MurmurHash3, xxHash64)
 * For comparison with k-wise independent hashing
 *
 * Compile: clang++ -O3 -std=c++17 -march=armv8-a+crypto bench_nonpoly_arm.cpp -o bench_nonpoly
 * Run:     ./bench_nonpoly
 */

#include <cmath>
#include <chrono>
#include <iostream>
#include <vector>
#include <algorithm>
#include <cstdint>
#include <cstring>

using namespace std;

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

// Simple tabulation for comparison
class Tabulation_64 {
    uint64_t table[8][256];
public:
    void init() {
        for (int i = 0; i < 8; i++) {
            for (int j = 0; j < 256; j++) {
                table[i][j] = ((uint64_t)rand() << 32) | rand();
            }
        }
    }
    uint64_t operator()(uint64_t k) {
        uint64_t h = 0;
        for (int i = 0; i < 8; i++) {
            h ^= table[i][(k >> (i * 8)) & 0xFF];
        }
        return h;
    }
};

template <typename T>
void benchmark(const char* name, int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    volatile uint64_t x;
    vector<uint64_t> times;

    // Warmup + measurement
    for (int i = 0; i < 2 * nr_times; ++i) {
        T hash;
        hash.init();

        // Warmup run
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

    // Keep only the best half (discard warmup)
    sort(times.begin(), times.end());
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

    cout << name << ": Mean: " << mean << " +/- " << sqrt(MSE) << " min " << min_time << endl;
}

int main(int argc, char* argv[]) {
    int nr_trials = 1000000;
    int nr_times = 100;

    if (argc >= 3) {
        nr_trials = atoi(argv[1]);
        nr_times = atoi(argv[2]);
    }

    srand(12345);

    vector<uint64_t> numbers;
    for (int i = 0; i < nr_trials; ++i) {
        numbers.push_back(((uint64_t)rand() << 32) | rand());
    }

    cout << "Non-polynomial Hash Benchmark (ARM)" << endl;
    cout << "====================================" << endl;
    cout << "Trials per test: " << nr_trials << endl;
    cout << "Repetitions: " << nr_times << endl;
    cout << endl;

    benchmark<MurmurHash3_64>("MurmurHash3-64", nr_trials, nr_times, numbers);
    benchmark<XXHash64>("xxHash64", nr_trials, nr_times, numbers);
    benchmark<Tabulation_64>("Tabulation 8x256", nr_trials, nr_times, numbers);

    return 0;
}
