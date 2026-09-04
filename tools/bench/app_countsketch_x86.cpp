/**
 * Application-level benchmark: CountSketch update loop.
 *
 * This measures the end-to-end cost of hashing + indexing + updating a counter array,
 * rather than just raw hash throughput.
 *
 * Compile (Apple Silicon):
 *   clang++ -O3 -std=c++17 -march=armv8-a+crypto app_countsketch_arm.cpp -o countsketch_arm
 *
 * Run:
 *   ./countsketch_arm [n_updates] [repetitions] [table_lg]
 */

#include <algorithm>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

#include "framework/fast_hashing.h"
#include "framework/randomgen.h"

using Clock = std::chrono::high_resolution_clock;

template <typename Hash>
static double bench_updates(const std::vector<uint64_t>& keys, int reps, std::size_t table_lg) {
  const std::size_t m = std::size_t{1} << table_lg;
  std::vector<int32_t> table(m, 0);

  Hash hash;
  hash.init();

  volatile uint64_t sink = 0;
  std::vector<uint64_t> times_us;
  times_us.reserve(2 * reps);

  // Warm-up + timed runs
  for (int r = 0; r < 2 * reps; r++) {
    std::fill(table.begin(), table.end(), 0);

    // Warm-up a little each run to stabilize.
    for (std::size_t i = 0; i < std::min<std::size_t>(keys.size(), 1 << 12); i++) {
      const uint64_t h = hash(keys[i]);
      const std::size_t idx = (std::size_t)h & (m - 1);
      const int32_t s = (int32_t)((h >> 63) ? 1 : -1);
      table[idx] += s;
      sink ^= (uint64_t)table[idx];
    }

    auto start = Clock::now();
    for (uint64_t k : keys) {
      const uint64_t h = hash(k);
      const std::size_t idx = (std::size_t)h & (m - 1);
      const int32_t s = (int32_t)((h >> 63) ? 1 : -1);
      table[idx] += s;
      sink ^= (uint64_t)table[idx];
    }
    auto end = Clock::now();
    times_us.push_back(
        (uint64_t)std::chrono::duration_cast<std::chrono::microseconds>(end - start).count());
  }

  std::sort(times_us.begin(), times_us.end());
  times_us.erase(times_us.begin() + reps, times_us.end());

  long double mean = 0;
  for (int i = 0; i < reps; i++) mean += times_us[i];
  mean /= reps;

  long double mse = 0;
  for (int i = 0; i < reps; i++) mse += (times_us[i] - mean) * (times_us[i] - mean);
  mse /= reps;

  // Prevent sink from being optimized away.
  if (sink == 0x12345678ULL) std::cout << "sink\n";

  const double ns_per_update = (double)(mean * 1000.0) / (double)keys.size();
  const double std_us = std::sqrt((double)mse);
  std::cout << "  mean " << (double)mean << "us ± " << std_us << "us"
            << "  (" << ns_per_update << " ns/update)\n";
  return ns_per_update;
}

int main(int argc, char** argv) {
  std::size_t n_updates = 1 << 20;
  int reps = 50;
  std::size_t table_lg = 16;
  if (argc >= 2) n_updates = (std::size_t)std::stoull(argv[1]);
  if (argc >= 3) reps = std::stoi(argv[2]);
  if (argc >= 4) table_lg = (std::size_t)std::stoull(argv[3]);

  init_randomness();

  poly_64<2> rng;
  rng.init();
  std::vector<uint64_t> keys;
  keys.reserve(n_updates);
  for (std::size_t i = 0; i < n_updates; i++) keys.push_back((uint64_t)rng((uint64_t)i));

  std::cout << "CountSketch update benchmark (x86, GF(2^64))\n";
  std::cout << "  updates=" << n_updates << " reps=" << reps << " table=2^" << table_lg << "\n";
  std::cout << "  (hash output used for bucket+sign)\n\n";

  std::cout << "Degree 9\n";
  std::cout << "Carryless (Horner):\n";
  const double t_horner = bench_updates<carryless_64<9>>(keys, reps, table_lg);

  std::cout << "Rabin--Winograd:\n";
  const double t_rw = bench_updates<rw_64<9>>(keys, reps, table_lg);

  std::cout << "Smart CL (this paper):\n";
  const double t_ours = bench_updates<smartcl_64<9>>(keys, reps, table_lg);

  std::cout << "\nSpeedups vs Horner (ns/update):\n";
  std::cout << "  RW:   " << (t_horner / t_rw) << "x\n";
  std::cout << "  Ours: " << (t_horner / t_ours) << "x\n";
  return 0;
}

