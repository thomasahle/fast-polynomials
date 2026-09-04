#include <algorithm>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <string>
#include <vector>

#include "framework/x2s_mersenne_chains.h"

using Clock = std::chrono::high_resolution_clock;

static inline uint64_t nanos_since(const Clock::time_point& start) {
  return (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(Clock::now() - start).count();
}

template <size_t DEG>
static inline __uint128_t horner_eval(const std::array<__uint128_t, DEG + 1>& coeffs, uint64_t x) {
  __uint128_t acc = coeffs[DEG];
  for (size_t i = DEG; i-- > 0;) {
    acc = fast_large_mult_mod(acc, coeffs[i], x);
  }
  return mersenne_reduce(acc);
}

template <size_t DEG>
static inline __uint128_t horner_eval_full(const std::array<__uint128_t, DEG + 1>& coeffs, __uint128_t x) {
  x = mersenne_reduce(x);
  __uint128_t acc = coeffs[DEG];
  for (size_t i = DEG; i-- > 0;) {
    acc = mersenne_add(mersenne_mul(acc, x), coeffs[i]);
  }
  return mersenne_reduce(acc);
}

template <typename Chain>
static void bench_chain_u64(const std::string& label, const std::vector<uint64_t>& xs, size_t iters) {
  Chain chain;
  chain.init();

  constexpr size_t DEG = Chain::DEGREE;
  const auto coeffs = chain.coeffs();

  // Quick correctness sanity check.
  for (size_t i = 0; i < std::min<size_t>(xs.size(), 16); i++) {
    const auto x = xs[i];
    const auto a = mersenne_reduce(chain.eval(x));
    const auto b = mersenne_reduce(horner_eval<DEG>(coeffs, x));
    if (a != b) {
      std::cerr << "Mismatch(u64) at degree " << DEG << " x=" << x << "\n";
      std::exit(1);
    }
  }

  volatile __uint128_t sink = 0;

  // Horner baseline.
  auto t0 = Clock::now();
  for (size_t it = 0; it < iters; it++) {
    for (uint64_t x : xs) sink ^= horner_eval<DEG>(coeffs, x);
  }
  const uint64_t horner_ns = nanos_since(t0);

  // Fast chain.
  t0 = Clock::now();
  for (size_t it = 0; it < iters; it++) {
    for (uint64_t x : xs) sink ^= chain.eval(x);
  }
  const uint64_t chain_ns = nanos_since(t0);

  const double per_eval_horner = (double)horner_ns / (double)(iters * xs.size());
  const double per_eval_chain = (double)chain_ns / (double)(iters * xs.size());

  std::cout << label << " (degree " << DEG << ")\n";
  std::cout << "  Horner: " << per_eval_horner << " ns/eval\n";
  std::cout << "  Chain : " << per_eval_chain << " ns/eval\n";
  std::cout << "  Speedup: " << (per_eval_horner / per_eval_chain) << "x\n";

  // Ensure sink is used.
  if ((uint64_t)sink == 0x12345678ULL) std::cout << "sink\n";
}

template <typename Chain>
static void bench_chain_full(const std::string& label,
                             const std::vector<__uint128_t>& xs,
                             size_t iters) {
  Chain chain;
  chain.init();

  constexpr size_t DEG = Chain::DEGREE;
  const auto coeffs = chain.coeffs();

  for (size_t i = 0; i < std::min<size_t>(xs.size(), 16); i++) {
    const auto x = xs[i];
    const auto a = mersenne_reduce(chain.eval_full(x));
    const auto b = mersenne_reduce(horner_eval_full<DEG>(coeffs, x));
    if (a != b) {
      std::cerr << "Mismatch(full) at degree " << DEG << "\n";
      std::exit(1);
    }
  }

  volatile __uint128_t sink = 0;

  auto t0 = Clock::now();
  for (size_t it = 0; it < iters; it++) {
    for (__uint128_t x : xs) sink ^= horner_eval_full<DEG>(coeffs, x);
  }
  const uint64_t horner_ns = nanos_since(t0);

  t0 = Clock::now();
  for (size_t it = 0; it < iters; it++) {
    for (__uint128_t x : xs) sink ^= chain.eval_full(x);
  }
  const uint64_t chain_ns = nanos_since(t0);

  const double per_eval_horner = (double)horner_ns / (double)(iters * xs.size());
  const double per_eval_chain = (double)chain_ns / (double)(iters * xs.size());

  std::cout << label << " (degree " << DEG << ", full-field x)\n";
  std::cout << "  Horner: " << per_eval_horner << " ns/eval\n";
  std::cout << "  Chain : " << per_eval_chain << " ns/eval\n";
  std::cout << "  Speedup: " << (per_eval_horner / per_eval_chain) << "x\n";

  if ((uint64_t)sink == 0x12345678ULL) std::cout << "sink\n";
}

int main(int argc, char** argv) {
  size_t n_points = 1 << 12;
  size_t iters = 1 << 10;
  if (argc >= 2) n_points = (size_t)std::stoull(argv[1]);
  if (argc >= 3) iters = (size_t)std::stoull(argv[2]);

  init_randomness();

  std::vector<uint64_t> xs;
  xs.reserve(n_points);
  for (size_t i = 0; i < n_points; i++) xs.push_back((uint64_t)(i + 1));

  std::vector<__uint128_t> xs_seq_full;
  xs_seq_full.reserve(n_points);
  for (size_t i = 0; i < n_points; i++) xs_seq_full.push_back((__uint128_t)(i + 1));

  std::vector<__uint128_t> xs_full;
  xs_full.reserve(n_points);
  for (size_t i = 0; i < n_points; i++) xs_full.push_back(getRandomUInt128() >> 39);

  std::cout << "Mersenne(2^89-1) Shamir-style share generation benchmark\n";
  std::cout << "  points=" << n_points << " iters=" << iters << "\n\n";

  bench_chain_u64<X2S_Mersenne_13>("x2s/u64-x", xs, iters);
  bench_chain_u64<X2S_Mersenne_15>("x2s/u64-x", xs, iters);
  bench_chain_u64<X2S_Mersenne_17>("x2s/u64-x", xs, iters);
  bench_chain_u64<X2S_Mersenne_19>("x2s/u64-x", xs, iters);
  bench_chain_u64<X2S_Mersenne_21>("x2s/u64-x", xs, iters);
  std::cout << "\n";
  bench_chain_full<X2S_Mersenne_13>("x2s/sharegen-seq", xs_seq_full, iters);
  bench_chain_full<X2S_Mersenne_15>("x2s/sharegen-seq", xs_seq_full, iters);
  bench_chain_full<X2S_Mersenne_17>("x2s/sharegen-seq", xs_seq_full, iters);
  bench_chain_full<X2S_Mersenne_19>("x2s/sharegen-seq", xs_seq_full, iters);
  bench_chain_full<X2S_Mersenne_21>("x2s/sharegen-seq", xs_seq_full, iters);
  std::cout << "\n";
  bench_chain_full<X2S_Mersenne_13>("x2s/prf-rand", xs_full, iters);
  bench_chain_full<X2S_Mersenne_15>("x2s/prf-rand", xs_full, iters);
  bench_chain_full<X2S_Mersenne_17>("x2s/prf-rand", xs_full, iters);
  bench_chain_full<X2S_Mersenne_19>("x2s/prf-rand", xs_full, iters);
  bench_chain_full<X2S_Mersenne_21>("x2s/prf-rand", xs_full, iters);

  return 0;
}
