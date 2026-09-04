#include <algorithm>
#include <math.h> /* sqrt */
#include <x86intrin.h>

#include <chrono>
#include <iostream>
#include <vector>
#include <climits>

#include "framework/fast_hashing.h"
#include "framework/injective_hashing.h"
#include "framework/dietzfelbinger_hash.h"
#include "framework/randomgen.h"

using namespace std;

#ifndef FROM
#define FROM 2
#endif

// TO should be one more than the maximum
#ifndef TO
#define TO 10
#endif

template <typename T>
uint64_t test_speed_function64(int nr_trials, int nr_times,
                               vector<uint64_t>& numbers) {
  volatile __uint128_t x;

  vector<uint64_t> times;

  // First half is warmup
  for (int i = 0; i < 2*nr_times; ++i) {
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
  // times.erase(times.begin(), times.begin() + nr_times);
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

  long double min = mean;
  for (int i = 0; i < nr_times; ++i) {
     if (times[i] < min)
        min = times[i];
  }

  cout << "Mean: " << mean << " ± " << sqrt(MSE) << " min " << min << endl;

  return (uint64_t)
      mean;  // chrono::duration_cast<chrono::nanoseconds>(end - start).count();
}

// Have to use recursion instead of a for-loop because of templates.
template<int n>
void test_speed_function64_loop(int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    cout << "Degree " << n << endl;
    cout << "Mersenne (traditional): ";
    test_speed_function64<poly_64_normal<n>>(nr_trials, nr_times, numbers);
    cout << "Mersenne (Mikkel): ";
    test_speed_function64<poly_64<n>>(nr_trials, nr_times, numbers);
    cout << "Mersenne (AKT): ";
    test_speed_function64<poly_64_2<n>>(nr_trials, nr_times, numbers);
    cout << "Mersenne, Estrin: ";
    test_speed_function64<estrin_mers_gen<n>>(nr_trials, nr_times, numbers);
    cout << "Mersenne, smart: ";
    test_speed_function64<smartpoly_64<n>>(nr_trials, nr_times, numbers);
    //cout << "Mersenne, karat: ";
    //test_speed_function64<smartpoly_64_kar<n>>(nr_trials, nr_times, numbers);

    cout << "Carryless: ";
    test_speed_function64<carryless_64<n>>(nr_trials, nr_times, numbers);
    cout << "Lemire: ";
    test_speed_function64<lemire_64<n>>(nr_trials, nr_times, numbers);
    // cout << "Weird Horner: ";
    // test_speed_function64<weird_horner_64<n>>(nr_trials, nr_times, numbers);
    cout << "Estrin: ";
    test_speed_function64<estrin_64<n>>(nr_trials, nr_times, numbers);
    //cout << "Estrin General: ";
    //test_speed_function64<estrin_64_gen<n>>(nr_trials, nr_times, numbers);
    cout << "Rabin Winograd: ";
    test_speed_function64<rw_64<n>>(nr_trials, nr_times, numbers);
    // cout << "Rabin Winograd, Rec: ";
    // test_speed_function64<rw_64_rec<n>>(nr_trials, nr_times, numbers);
    cout << "Smart CL: ";
    test_speed_function64<smartcl_64<n>>(nr_trials, nr_times, numbers);

    cout << "Dietz-128: ";
    test_speed_function64<dietz_128_opt<n>>(nr_trials, nr_times, numbers);
    cout << "Dietz-256: ";
    test_speed_function64<dietz_256<n>>(nr_trials, nr_times, numbers);

    // cout << "Murmur: ";
    // test_speed_function64<murmur_64<n>>(nr_trials, nr_times, numbers);
    // cout << endl;

   // Next step of the for loop
   test_speed_function64_loop<n+1>(nr_trials, nr_times, numbers);
}
template<>
void test_speed_function64_loop<TO>(int nr_trials, int nr_times, vector<uint64_t>& numbers) {
   // End of recursion.
}

void test_speed64(int nr_trials, int nr_times) {
  poly_64<2> rng;
  rng.init();

  vector<uint64_t> numbers;
  for (int i = 0; i < nr_trials; ++i) {
    numbers.push_back(rng(i));
  }

  cout << "Tabulation 16x2^4: ";
  test_speed_function64<tabulation_16x4>(nr_trials, nr_times, numbers);
  cout << "Tabulation 8x2^8: ";
  test_speed_function64<tabulation_64>(nr_trials, nr_times, numbers);
  cout << "Tabulation 8x2^8 tree: ";
  test_speed_function64<tabulation_64_tree>(nr_trials, nr_times, numbers);
  cout << "Tabulation 4x2^16: ";
  test_speed_function64<tabulation_4x16>(nr_trials, nr_times, numbers);

  // cout << "Shuf_1: ";
  // test_speed_function64<shuf_64<1>>(nr_trials, nr_times, numbers);
  // cout << "Shuf_2: ";
  // test_speed_function64<shuf_64<2>>(nr_trials, nr_times, numbers);
  // cout << "Shuf_4: ";
  // test_speed_function64<shuf_64<4>>(nr_trials, nr_times, numbers);
  // cout << "Shuf_8: ";
  // test_speed_function64<shuf_64<8>>(nr_trials, nr_times, numbers);
  // cout << "Shuf_16: ";
  // test_speed_function64<shuf_64<16>>(nr_trials, nr_times, numbers);
  cout << "Mixed(8x2^8, 1): ";
  test_speed_function64<mixed_64<1>>(nr_trials, nr_times, numbers);
  // cout << "Mixed(2): ";
  // test_speed_function64<mixed_64<2>>(nr_trials, nr_times, numbers);
  // cout << "Mixed(4): ";
  // test_speed_function64<mixed_64<4>>(nr_trials, nr_times, numbers);
  // cout << "Mixed(8): ";
  // test_speed_function64<mixed_64<8>>(nr_trials, nr_times, numbers);

  cout << "Dietz 2-wise (specialized): ";
  test_speed_function64<dietz_2wise>(nr_trials, nr_times, numbers);
  cout << "Thorup pair-multiply: ";
  test_speed_function64<thorup_pair_64>(nr_trials, nr_times, numbers);
  cout << endl;

  // cout << "Estrin: ";
  // test_speed_function64<estrin_64<5>>(nr_trials, nr_times, numbers);
  // cout << "Estrin General: ";
  // test_speed_function64<estrin_64_gen<5>>(nr_trials, nr_times, numbers);

  // cout << "Estrin: ";
  // test_speed_function64<estrin_64<7>>(nr_trials, nr_times, numbers);
  // cout << "Estrin General: ";
  // test_speed_function64<estrin_64_gen<7>>(nr_trials, nr_times, numbers);

  // Loop 2 to 7
  test_speed_function64_loop<FROM>(nr_trials, nr_times, numbers);

  // cout << "Estrin General: ";
  // test_speed_function64<estrin_64_gen<7>>(nr_trials, nr_times, numbers);
  // cout << "Rabin Winograd: ";
  // test_speed_function64<rw_64<7>>(nr_trials, nr_times, numbers);
  // cout << "Smart CL: ";
  // test_speed_function64<smartcl_64<7>>(nr_trials, nr_times, numbers);
}

// Injective polynomial hashing benchmark
template<int N>
void test_injective_size(int nr_trials, int nr_times, vector<uint64_t>& numbers) {
    cout << "N=" << N << " (2N=" << 2*N << " blocks)" << endl;
    cout << "  Horner (2N-1 mults): ";
    test_speed_function64<univ_horner_64<N>>(nr_trials, nr_times, numbers);
    cout << "  Injective (N mults): ";
    test_speed_function64<univ_injective_64<N>>(nr_trials, nr_times, numbers);
    cout << endl;
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

    cout << endl << "Injective Polynomial Hashing" << endl;
    cout << "============================" << endl;
    test_injective_size<4>(nr_trials, nr_times, numbers);
    test_injective_size<8>(nr_trials, nr_times, numbers);
    test_injective_size<16>(nr_trials, nr_times, numbers);
    test_injective_size<32>(nr_trials, nr_times, numbers);

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

int main(int argc, char* argv[]) {
  double nr_trials = 1e6;
  double nr_times = 1e2;
  if (argc >= 3) {
      nr_trials = stod(argv[1]);
      nr_times = stod(argv[2]);
  }

  init_randomness();

  test_speed64(nr_trials, nr_times);
  test_injective(nr_trials, nr_times);

#ifdef DEBUG
  cout << "Random bytes used: " << usedBytes << endl;
#endif

  return 0;
}
