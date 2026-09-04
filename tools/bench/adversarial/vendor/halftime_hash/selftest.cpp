// selftest.cpp -- standalone faithfulness check for the vendored HalftimeHash.
//
// Validation is against the repo's OWN published test vectors, generated.txt.
// That file is produced upstream by check-consistency.cpp, which seeds its
// entropy with a DEFAULT-constructed std::mt19937_64 (the C++-standard fixed
// seed 5489, identical on every conforming library) and prints, for output
// widths 2..5 and every input length 0..kCodeCoverageByteLength-1, the words of
//     halftime_hash::advanced::V4<out_width>(entropy, "XXX...", length, out).
// We reproduce that here and compare byte-for-byte. V4 == "Style512" and its
// value is ISA-independent, so a match validates the vendored algorithm exactly.
//
// Build (AArch64 or x86):
//   clang++ -O3 -std=c++17 -march=native selftest.cpp -o selftest && ./selftest
//
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <fstream>
#include <random>
#include <string>
#include <vector>

#include "hh_bench.h"   // arm_neon_fix.h + verbatim halftime-hash.hpp

using std::uint64_t;

template <int out_width>
static bool CheckWidth(const uint64_t* entropy, std::ifstream& in, size_t& line) {
  std::vector<char> input(halftime_hash::kCodeCoverageByteLength, 'X');
  uint64_t output[out_width];
  for (size_t i = 0; i < halftime_hash::kCodeCoverageByteLength; ++i) {
    halftime_hash::advanced::V4<out_width>(entropy, input.data(), i, output);
    for (int j = 0; j < out_width; ++j) {
      uint64_t expect;
      if (!(in >> std::hex >> expect)) {
        std::fprintf(stderr, "generated.txt ended early (width %d, line %zu)\n",
                     out_width, line);
        return false;
      }
      if (expect != output[j]) {
        std::fprintf(stderr,
                     "MISMATCH width=%d len=%zu col=%d: got %016llx expect %016llx\n",
                     out_width, i, j, (unsigned long long)output[j],
                     (unsigned long long)expect);
        return false;
      }
    }
    ++line;
  }
  return true;
}

int main(int argc, char** argv) {
  const char* path = (argc > 1) ? argv[1] : "generated.txt";
  std::ifstream in(path);
  if (!in) { std::fprintf(stderr, "cannot open %s\n", path); return 2; }

  // Exactly the upstream entropy: default-seeded mt19937_64.
  std::array<uint64_t, halftime_hash::advanced::MaxEntropyBytesNeeded()> entropy;
  std::generate(entropy.begin(), entropy.end(), std::mt19937_64());

  size_t line = 1;
  bool ok = true;
  ok &= CheckWidth<2>(entropy.data(), in, line);
  ok &= CheckWidth<3>(entropy.data(), in, line);
  ok &= CheckWidth<4>(entropy.data(), in, line);
  ok &= CheckWidth<5>(entropy.data(), in, line);
  std::printf("official-vectors (generated.txt, widths 2-5): %s\n",
              ok ? "MATCH" : "FAIL");
  if (!ok) return 1;

  // Smoke-test the exact public entry the benchmark harness will call, over a
  // spread of lengths, to confirm it runs and is deterministic. (No published
  // single-word vectors exist for Style512; correctness of its V4<2> core is
  // already proven by the match above.)
  std::array<uint64_t, halftime_hash::kEntropyBytesNeeded / sizeof(uint64_t)> ent2;
  std::generate(ent2.begin(), ent2.end(), std::mt19937_64(12345));
  std::vector<char> buf(200000, 0);
  for (size_t i = 0; i < buf.size(); ++i) buf[i] = (char)(i * 131 + 7);
  uint64_t acc = 0;
  for (size_t len : {(size_t)0, (size_t)1, (size_t)16, (size_t)17, (size_t)64,
                     (size_t)255, (size_t)1024, (size_t)4096, (size_t)65536,
                     (size_t)200000}) {
    uint64_t h = halftime_hash::HalftimeHashStyle512(ent2.data(), buf.data(), len);
    uint64_t h2 = halftime_hash::HalftimeHashStyle512(ent2.data(), buf.data(), len);
    if (h != h2) { std::printf("Style512 nondeterministic at len=%zu\n", len); return 1; }
    acc ^= h;
    std::printf("Style512(len=%6zu) = %016llx\n", len, (unsigned long long)h);
  }
  std::printf("Style512 smoke: OK (xor=%016llx)\n", (unsigned long long)acc);
  return 0;
}
