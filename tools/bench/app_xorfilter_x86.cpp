/**
 * Application-level benchmark: XOR-filter-style membership structure.
 *
 * We implement a simplified 3-hash XOR filter (peeling construction) with an 8-bit
 * fingerprint array. This is an "approximate membership" data structure similar in
 * spirit to Bloom/cuckoo filters, with very fast queries: three table reads + XORs.
 *
 * The goal here is to measure build and query throughput when hashing cost matters.
 *
 * Compile (Apple Silicon):
 *   clang++ -O3 -std=c++17 -march=armv8-a+crypto app_xorfilter_arm.cpp -o xorfilter_arm
 *
 * Run:
 *   ./xorfilter_arm [table_lg] [load_pct] [reps]
 */

#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <string>
#include <vector>

#include "framework/fast_hashing.h"
#include "framework/randomgen.h"

using Clock = std::chrono::high_resolution_clock;

static inline uint64_t splitmix64(uint64_t x) {
  x += 0x9e3779b97f4a7c15ULL;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return x ^ (x >> 31);
}

static inline uint64_t rotl64(uint64_t x, int r) { return (x << r) | (x >> (64 - r)); }

struct XorFilter {
  std::vector<uint8_t> table;
  uint64_t seed = 0;
  std::size_t mask = 0;
};

struct BenchResult {
  double ns_per_key_build = 0;
  double ns_per_query = 0;
  double false_positive_rate = 0;
  int attempts = 0;
};

template <typename Hash>
static inline void positions_and_fp(Hash& hash,
                                    uint64_t key,
                                    uint64_t seed,
                                    std::size_t mask,
                                    std::size_t pos[3],
                                    uint8_t& fp) {
  const uint64_t h = hash(key ^ seed);
  pos[0] = (std::size_t)(h)&mask;
  pos[1] = (std::size_t)(rotl64(h, 21)) & mask;
  pos[2] = (std::size_t)(rotl64(h, 42)) & mask;
  const uint64_t f = h ^ (h >> 32) ^ (h >> 48);
  fp = (uint8_t)f;
  if (fp == 0) fp = 1;
}

template <typename Hash>
static bool build_xorfilter(Hash& hash, const std::vector<uint64_t>& keys, std::size_t table_lg,
                            uint64_t seed, XorFilter& out) {
  const std::size_t m = std::size_t{1} << table_lg;
  const std::size_t mask = m - 1;

  std::vector<uint32_t> cnt(m, 0);
  std::vector<uint64_t> key_xor(m, 0);
  std::vector<uint8_t> fp_xor(m, 0);

  std::size_t pos[3];
  uint8_t fp = 0;
  for (uint64_t k : keys) {
    positions_and_fp(hash, k, seed, mask, pos, fp);
    for (int j = 0; j < 3; j++) {
      cnt[pos[j]]++;
      key_xor[pos[j]] ^= k;
      fp_xor[pos[j]] ^= fp;
    }
  }

  std::vector<uint32_t> q;
  q.reserve(m);
  for (uint32_t i = 0; i < m; i++) {
    if (cnt[i] == 1) q.push_back(i);
  }

  struct Node {
    uint32_t idx;
    uint64_t key;
    uint8_t fp;
  };
  std::vector<Node> stack;
  stack.reserve(keys.size());

  while (!q.empty()) {
    const uint32_t i = q.back();
    q.pop_back();
    if (cnt[i] != 1) continue;

    const uint64_t key = key_xor[i];
    const uint8_t f = fp_xor[i];
    stack.push_back(Node{i, key, f});

    positions_and_fp(hash, key, seed, mask, pos, fp);
    for (int j = 0; j < 3; j++) {
      const uint32_t p = (uint32_t)pos[j];
      if (p == i) continue;
      cnt[p]--;
      key_xor[p] ^= key;
      fp_xor[p] ^= f;
      if (cnt[p] == 1) q.push_back(p);
    }

    cnt[i] = 0;
  }

  if (stack.size() != keys.size()) return false;

  out.table.assign(m, 0);
  out.seed = seed;
  out.mask = mask;

  // Assign in reverse peel order.
  for (std::size_t t = stack.size(); t-- > 0;) {
    const auto n = stack[t];
    positions_and_fp(hash, n.key, seed, mask, pos, fp);
    uint8_t x = out.table[pos[0]] ^ out.table[pos[1]] ^ out.table[pos[2]];
    out.table[n.idx] = n.fp ^ x;
    if (out.table[n.idx] == 0) out.table[n.idx] = 1;
  }
  return true;
}

template <typename Hash>
static inline bool query_xorfilter(Hash& hash, const XorFilter& f, uint64_t key) {
  std::size_t pos[3];
  uint8_t fp;
  positions_and_fp(hash, key, f.seed, f.mask, pos, fp);
  const uint8_t got = f.table[pos[0]] ^ f.table[pos[1]] ^ f.table[pos[2]];
  return got == fp;
}

template <typename Hash>
static BenchResult bench_xorfilter(std::size_t table_lg, int load_pct, int reps) {
  const std::size_t m = std::size_t{1} << table_lg;
  const std::size_t n_keys = (m * (std::size_t)load_pct) / 100;
  const std::size_t n_queries = 2 * n_keys;

  std::vector<uint64_t> keys;
  keys.reserve(n_keys);
  for (std::size_t i = 0; i < n_keys; i++) keys.push_back(splitmix64(i + 1) | 1ULL);

  std::vector<uint64_t> queries;
  queries.reserve(n_queries);
  for (std::size_t i = 0; i < n_queries / 2; i++) queries.push_back(keys[i]);
  for (std::size_t i = 0; i < n_queries / 2; i++) queries.push_back(splitmix64(0x12345678ULL + i) | 1ULL);

  Hash hash;
  hash.init();

  // Build (with retries if the peel fails).
  XorFilter filter;
  uint64_t seed = getRandomUInt64();
  int attempts = 0;
  auto start = Clock::now();
  while (true) {
    attempts++;
    if (build_xorfilter(hash, keys, table_lg, seed, filter)) break;
    seed = splitmix64(seed);
    if (attempts > 50) {
      std::cerr << "Too many build attempts; try lowering load.\n";
      std::exit(2);
    }
  }
  auto end = Clock::now();
  const uint64_t build_ns =
      (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();

  // Query benchmark.
  volatile uint64_t sink = 0;
  uint64_t fp = 0;

  // Warmup
  for (std::size_t i = 0; i < std::min<std::size_t>(queries.size(), 1 << 12); i++) {
    sink ^= query_xorfilter(hash, filter, queries[i]);
  }

  start = Clock::now();
  for (int r = 0; r < reps; r++) {
    for (uint64_t q : queries) sink ^= query_xorfilter(hash, filter, q);
  }
  end = Clock::now();
  const uint64_t query_ns =
      (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count();

  // False positive rate estimate on the "miss" half.
  for (std::size_t i = n_queries / 2; i < n_queries; i++) fp += query_xorfilter(hash, filter, queries[i]);

  if (sink == 0x12345678ULL) std::cout << "sink\n";

  BenchResult out;
  out.ns_per_key_build = (double)build_ns / (double)n_keys;
  out.ns_per_query = (double)query_ns / (double)(reps * n_queries);
  out.false_positive_rate = (double)fp / (double)(n_queries / 2);
  out.attempts = attempts;
  return out;
}

static void print_result(const std::string& label, const BenchResult& r) {
  std::cout << label << "\n";
  std::cout << "  build:  " << r.ns_per_key_build << " ns/key"
            << " (attempts " << r.attempts << ")\n";
  std::cout << "  query:  " << r.ns_per_query << " ns/query\n";
  std::cout << "  FP rate (est.): " << r.false_positive_rate << "\n";
}

int main(int argc, char** argv) {
  std::size_t table_lg = 20;
  int load_pct = 75;
  int reps = 5;
  if (argc >= 2) table_lg = (std::size_t)std::stoull(argv[1]);
  if (argc >= 3) load_pct = std::stoi(argv[2]);
  if (argc >= 4) reps = std::stoi(argv[3]);

  init_randomness();

  std::cout << "XOR-filter-style benchmark (x86, GF(2^64))\n";
  std::cout << "  table=2^" << table_lg << " load=" << load_pct << "% reps=" << reps << "\n\n";

  std::cout << "Degree 9\n";
  const auto horner = bench_xorfilter<carryless_64<9>>(table_lg, load_pct, reps);
  const auto rw = bench_xorfilter<rw_64<9>>(table_lg, load_pct, reps);
  const auto ours = bench_xorfilter<smartcl_64<9>>(table_lg, load_pct, reps);

  print_result("Carryless (Horner)", horner);
  print_result("Rabin--Winograd", rw);
  print_result("Smart CL (this paper)", ours);

  std::cout << "\nSpeedups vs Horner\n";
  std::cout << "  build: RW " << (horner.ns_per_key_build / rw.ns_per_key_build) << "x"
            << "  Ours " << (horner.ns_per_key_build / ours.ns_per_key_build) << "x\n";
  std::cout << "  query: RW " << (horner.ns_per_query / rw.ns_per_query) << "x"
            << "  Ours " << (horner.ns_per_query / ours.ns_per_query) << "x\n";
  return 0;
}

