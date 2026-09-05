/**
 * Focused test for Horner-Parallel anomaly investigation
 */

#include <cmath>
#include <chrono>
#include <iostream>
#include <vector>
#include <algorithm>

#include "framework/injective_hashing_arm.h"
#include "framework/randomgen.h"

using namespace std;

template <typename T>
void run_test(const char* name, int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    volatile uint64_t x;
    vector<uint64_t> times;

    for (int i = 0; i < nr_times; ++i) {
        T hash;
        hash.init();

        // Warmup
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

    sort(times.begin(), times.end());

    double mean = 0;
    for (auto t : times) mean += t;
    mean /= times.size();

    double var = 0;
    for (auto t : times) var += (t - mean) * (t - mean);
    var = sqrt(var / times.size());

    double median = times[times.size()/2];

    cout << name << ": mean=" << mean << " ±" << var
         << " median=" << median
         << " min=" << times[0]
         << " max=" << times.back() << endl;
}

int main() {
    init_randomness();

    int nr_trials = 100000;
    int nr_times = 100;

    vector<uint64_t> numbers;
    for (int i = 0; i < nr_trials; ++i) {
        numbers.push_back(getRandomUInt64());
    }

    cout << "Horner-Parallel Investigation" << endl;
    cout << "=============================" << endl;
    cout << "Trials: " << nr_trials << ", Runs: " << nr_times << endl;
    cout << endl;

    cout << "Testing different sizes:" << endl;
    run_test<horner_parallel_64<8>>("N=8  ", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<16>>("N=16 ", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<32>>("N=32 ", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<64>>("N=64 ", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<96>>("N=96 ", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<112>>("N=112", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<128>>("N=128", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<144>>("N=144", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<160>>("N=160", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<192>>("N=192", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<256>>("N=256", nr_trials, nr_times, numbers);
    run_test<horner_parallel_64<512>>("N=512", nr_trials, nr_times, numbers);

    cout << endl;
    cout << "For comparison - sequential Horner:" << endl;
    run_test<horner_unrolled_64<128>>("Horner-Unroll N=128", nr_trials, nr_times, numbers);
    run_test<horner_unrolled_64<256>>("Horner-Unroll N=256", nr_trials, nr_times, numbers);

    return 0;
}
