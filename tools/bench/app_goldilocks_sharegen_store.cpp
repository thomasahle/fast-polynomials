#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

#include "framework/x2s_goldilocks_chains.h"

using Clock = std::chrono::high_resolution_clock;

static inline uint64_t nanos_since(const Clock::time_point& start) {
  return (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start).count();
}

template <size_t DEG>
static inline uint64_t horner_eval(const std::array<uint64_t, DEG + 1>& coeffs, uint64_t x) {
  x = goldilocks_reduce_u64(x);
  uint64_t acc = coeffs[DEG];
  for (size_t i = DEG; i-- > 0;) {
    acc = goldilocks_add(goldilocks_mul(acc, x), coeffs[i]);
  }
  return acc;
}

template <typename Chain>
static void bench_chain_store(const std::string& label, size_t n_points, size_t iters) {
  Chain chain;
  chain.init();

  constexpr size_t DEG = Chain::DEGREE;
  const auto coeffs = chain.coeffs();

  std::vector<uint64_t> xs;
  xs.reserve(n_points);
  for (size_t i = 0; i < n_points; i++) xs.push_back((uint64_t)(i + 1));

  std::vector<uint64_t> out_horner(n_points);
  std::vector<uint64_t> out_chain(n_points);

  // Correctness check (single pass).
  for (size_t i = 0; i < std::min<size_t>(n_points, 64); i++) {
    const uint64_t x = xs[i];
    const uint64_t a = chain.eval(x);
    const uint64_t b = horner_eval<DEG>(coeffs, x);
    if (a != b) {
      std::cerr << "Mismatch at degree " << DEG << " x=" << x << "\n";
      std::exit(1);
    }
  }

  auto t0 = Clock::now();
  for (size_t it = 0; it < iters; it++) {
    for (size_t i = 0; i < n_points; i++) out_horner[i] = horner_eval<DEG>(coeffs, xs[i]);
  }
  const uint64_t horner_ns = nanos_since(t0);

  t0 = Clock::now();
  for (size_t it = 0; it < iters; it++) {
    for (size_t i = 0; i < n_points; i++) out_chain[i] = chain.eval(xs[i]);
  }
  const uint64_t chain_ns = nanos_since(t0);

  // Ensure results are used (and also provide a sanity equality check).
  volatile uint64_t sink = 0;
  for (size_t i = 0; i < n_points; i++) sink ^= (out_horner[i] ^ out_chain[i]);

  const double per_eval_horner = (double)horner_ns / (double)(iters * n_points);
  const double per_eval_chain = (double)chain_ns / (double)(iters * n_points);

  std::cout << label << " (degree " << DEG << ", store-to-memory)\n";
  std::cout << "  Horner: " << per_eval_horner << " ns/share\n";
  std::cout << "  Chain : " << per_eval_chain << " ns/share\n";
  std::cout << "  Speedup: " << (per_eval_horner / per_eval_chain) << "x\n";

  if (sink == 0x12345678ULL) std::cout << "sink\n";
}

int main(int argc, char** argv) {
  size_t n_points = 1 << 16;
  size_t iters = 1 << 8;
  if (argc >= 2) n_points = (size_t)std::stoull(argv[1]);
  if (argc >= 3) iters = (size_t)std::stoull(argv[2]);

  init_randomness();

  std::cout << "Goldilocks(p=2^64-2^32+1) share-generation (store) benchmark\n";
  std::cout << "  points=" << n_points << " iters=" << iters << "\n\n";

  bench_chain_store<X2S_Goldilocks_13>("x2s/sharegen", n_points, iters);
  bench_chain_store<X2S_Goldilocks_15>("x2s/sharegen", n_points, iters);
  bench_chain_store<X2S_Goldilocks_17>("x2s/sharegen", n_points, iters);
  bench_chain_store<X2S_Goldilocks_19>("x2s/sharegen", n_points, iters);
  bench_chain_store<X2S_Goldilocks_21>("x2s/sharegen", n_points, iters);

  return 0;
}

