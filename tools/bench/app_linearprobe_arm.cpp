/**
 * Application-level benchmark: linear probing hash table.
 *
 * Measures end-to-end cost of hashing + probing memory, for both build (inserts)
 * and query (lookups), comparing Horner vs Rabin--Winograd vs this paper.
 *
 * Compile (Apple Silicon):
 *   clang++ -O3 -std=c++17 -march=armv8-a+crypto app_linearprobe_arm.cpp -o linearprobe_arm
 *
 * Run:
 *   ./linearprobe_arm [table_lg] [load_pct] [reps]
 */

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "framework/fast_hashing_arm.h"
#include "framework/randomgen.h"

using Clock = std::chrono::high_resolution_clock;

static inline uint64_t splitmix64(uint64_t x) {
  x += 0x9e3779b97f4a7c15ULL;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}

struct BenchResult {
  double ns_per_insert = 0;
  double ns_per_lookup = 0;
  double probes_per_lookup = 0;
};

template <typename Hash>
static BenchResult bench_linearprobe(std::size_t table_lg, int load_pct, int reps) {
  const std::size_t cap = std::size_t{1} << table_lg;
  const std::size_t mask = cap - 1;
  const std::size_t n_keys = (cap * (std::size_t)load_pct) / 100;
  const std::size_t n_queries = 2 * n_keys;

  std::vector<uint64_t> keys;
  keys.reserve(n_keys);
  for (std::size_t i = 0; i < n_keys; i++) {
    // Ensure nonzero sentinel.
    keys.push_back(splitmix64(i + 1) | 1ULL);
  }

  std::vector<uint64_t> queries;
  queries.reserve(n_queries);
  for (std::size_t i = 0; i < n_queries / 2; i++) queries.push_back(keys[i]);
  for (std::size_t i = 0; i < n_queries / 2; i++) {
    // Probabilistically misses.
    queries.push_back(splitmix64(0xdeadbeefULL + i) | 1ULL);
  }

  Hash hash;
  hash.init();

  std::vector<uint64_t> table(cap, 0);

  auto insert_one = [&](uint64_t key) {
    const uint64_t h = hash(key);
    std::size_t idx = (std::size_t)h & mask;
    while (true) {
      const uint64_t cur = table[idx];
      if (cur == 0 || cur == key) {
        table[idx] = key;
        return;
      }
      idx = (idx + 1) & mask;
    }
  };

  auto lookup_one = [&](uint64_t key) -> bool {
    const uint64_t h = hash(key);
    std::size_t idx = (std::size_t)h & mask;
    while (true) {
      const uint64_t cur = table[idx];
      if (cur == 0) return false;
      if (cur == key) return true;
      idx = (idx + 1) & mask;
    }
  };

  // Build once (timed), after a warmup build.
  for (std::size_t i = 0; i < std::min<std::size_t>(keys.size(), 1 << 12); i++) insert_one(keys[i]);
  std::fill(table.begin(), table.end(), 0);

  auto start = Clock::now();
  for (uint64_t k : keys) insert_one(k);
  auto end = Clock::now();
  const uint64_t build_ns =
      (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();

  // Lookup benchmark (repeated).
  volatile uint64_t sink = 0;
  uint64_t total_probes = 0;

  // Warmup.
  for (std::size_t i = 0; i < std::min<std::size_t>(queries.size(), 1 << 12); i++) sink ^= lookup_one(queries[i]);

  start = Clock::now();
  for (int r = 0; r < reps; r++) {
    for (uint64_t q : queries) {
      // Inline probe count by repeating the loop.
      const uint64_t h = hash(q);
      std::size_t idx = (std::size_t)h & mask;
      uint64_t probes = 0;
      while (true) {
        probes++;
        const uint64_t cur = table[idx];
        if (cur == 0) break;
        if (cur == q) break;
        idx = (idx + 1) & mask;
      }
      total_probes += probes;
      sink ^= (uint64_t)table[idx];
    }
  }
  end = Clock::now();
  const uint64_t lookup_ns =
      (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();

  if (sink == 0x12345678ULL) std::cout << "sink\n";

  BenchResult out;
  out.ns_per_insert = (double)build_ns / (double)n_keys;
  out.ns_per_lookup = (double)lookup_ns / (double)(reps * n_queries);
  out.probes_per_lookup = (double)total_probes / (double)(reps * n_queries);
  return out;
}

static void print_result(const std::string& label, const BenchResult& r) {
  std::cout << label << "\n";
  std::cout << "  build:  " << r.ns_per_insert << " ns/insert\n";
  std::cout << "  lookup: " << r.ns_per_lookup << " ns/query"
            << " (avg probes " << r.probes_per_lookup << ")\n";
}

int main(int argc, char** argv) {
  std::size_t table_lg = 20;
  int load_pct = 70;
  int reps = 5;
  if (argc >= 2) table_lg = (std::size_t)std::stoull(argv[1]);
  if (argc >= 3) load_pct = std::stoi(argv[2]);
  if (argc >= 4) reps = std::stoi(argv[3]);

  init_randomness();

  std::cout << "Linear probing benchmark (ARM NEON, GF(2^64))\n";
  std::cout << "  table=2^" << table_lg << " load=" << load_pct << "% reps=" << reps << "\n\n";

  std::cout << "Degree 9\n";

  const auto horner = bench_linearprobe<carryless_64<9>>(table_lg, load_pct, reps);
  const auto rw = bench_linearprobe<rw_64<9>>(table_lg, load_pct, reps);
  const auto ours = bench_linearprobe<smartcl_64<9>>(table_lg, load_pct, reps);

  print_result("Carryless (Horner)", horner);
  print_result("Rabin--Winograd", rw);
  print_result("Smart CL (this paper)", ours);

  std::cout << "\nSpeedups vs Horner\n";
  std::cout << "  build:  RW " << (horner.ns_per_insert / rw.ns_per_insert) << "x"
            << "  Ours " << (horner.ns_per_insert / ours.ns_per_insert) << "x\n";
  std::cout << "  lookup: RW " << (horner.ns_per_lookup / rw.ns_per_lookup) << "x"
            << "  Ours " << (horner.ns_per_lookup / ours.ns_per_lookup) << "x\n";

  return 0;
}

