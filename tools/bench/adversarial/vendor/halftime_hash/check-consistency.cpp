#include <array>
#include <cstddef>  // for std::size_t
#include <iostream>
#include <random>
#include <string>
#include <vector>

#include "halftime-hash.hpp"

using namespace std;

template <int out_length>
void Generate(const uint64_t entropy[halftime_hash::advanced::MaxEntropyBytesNeeded()]) {
  vector<char> input(halftime_hash::kCodeCoverageByteLength, 'X');
  uint64_t output[out_length];
  for (size_t i = 0; i < halftime_hash::kCodeCoverageByteLength; ++i) {
    halftime_hash::advanced::V4<out_length>(entropy, input.data(), i, output);
    for (int j = 0; j < out_length; ++j) {
      cout << hex << output[j] << ' ';
    }
    cout << endl;
  }
}

template <int out_length>
bool Check(const uint64_t entropy[halftime_hash::advanced::MaxEntropyBytesNeeded()]) {
  vector<char> input(halftime_hash::kCodeCoverageByteLength, 'X');
  uint64_t output[out_length];
  for (size_t i = 0; i < halftime_hash::kCodeCoverageByteLength; ++i) {
    halftime_hash::advanced::V4<out_length>(entropy, input.data(), i, output);
    for (int j = 0; j < out_length; ++j) {
      uint64_t check;
      cin >> hex >> check;
      if (check != output[j]) return false;
    }
  }
  return true;
}


void GenerateAll(const uint64_t entropy[halftime_hash::advanced::MaxEntropyBytesNeeded()]) {
  Generate<2>(entropy);
  Generate<3>(entropy);
  Generate<4>(entropy);
  Generate<5>(entropy);
}



int main(int argc, char ** argv) {
  if (argc < 2) return 1;
  array<uint64_t, halftime_hash::advanced::MaxEntropyBytesNeeded()> entropy;
  generate(entropy.begin(), entropy.end(), mt19937_64());
  if (string("generate") == argv[1]) {
    GenerateAll(entropy.data());
  } else if (string("check") == argv[1]) {
    cout << "2 " << (Check<2>(entropy.data()) ? "OK" : "NOT OK") << endl;
    cout << "3 " << (Check<3>(entropy.data()) ? "OK" : "NOT OK") << endl;
    cout << "4 " << (Check<4>(entropy.data()) ? "OK" : "NOT OK") << endl;
    cout << "5 " << (Check<5>(entropy.data()) ? "OK" : "NOT OK") << endl;
  } else {
    return 1;
  }
  return 0;
}
