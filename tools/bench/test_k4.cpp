// Quick test for k=4 timing - matching original benchmark methodology
#include <chrono>
#include <iostream>
#include <vector>
#include <cmath>
#include <algorithm>
#include "framework/fast_hashing_arm.h"
#include "framework/randomgen.h"

using namespace std;

template <typename T>
void benchmark(const char* name, int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    volatile uint64_t x;
    vector<uint64_t> times;

    // Run 2x measurements, first half is warmup
    for (int i = 0; i < 2 * nr_times; ++i) {
        T hash;
        hash.init();

        // Per-iteration warmup
        for (int j = 0; j < nr_trials; ++j) x = hash(numbers[j]);

        auto start = chrono::high_resolution_clock::now();
        for (int j = 0; j < nr_trials; ++j) x = hash(numbers[j]);
        auto end = chrono::high_resolution_clock::now();
        times.push_back(chrono::duration_cast<chrono::microseconds>(end - start).count());
    }

    // Sort and keep only best half
    sort(times.begin(), times.end());
    times.erase(times.begin() + nr_times, times.end());

    long double mean = 0;
    for (auto t : times) mean += t;
    mean /= nr_times;

    long double var = 0;
    for (auto t : times) var += (t - mean) * (t - mean);
    var = sqrt(var / nr_times);

    cout << name << ": " << mean << " +/- " << var << endl;
}

int main() {
    init_randomness();
    int nr_trials = 1000000;
    int nr_times = 100;

    vector<uint64_t> numbers;
    for (int i = 0; i < nr_trials; ++i) numbers.push_back(getRandomUInt64());

    benchmark<smartcl_64<3>>("k=3", nr_trials, nr_times, numbers);
    benchmark<smartcl_64<4>>("k=4", nr_trials, nr_times, numbers);
    benchmark<smartcl_64<5>>("k=5", nr_trials, nr_times, numbers);
    return 0;
}
