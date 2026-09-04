/* ***********************************************
 * Random number generation with file form Random.org
 * ***********************************************/

#ifndef _RANDOMGEN_H_
#define _RANDOMGEN_H_

#include <cassert>
#include <fstream>
#include <string>
#include <vector>

#ifdef DEBUG
#include <iostream>
#endif

using namespace std;

bool randomHasInit = false;
vector<char> randomBytes;
int usedBytes = 0;
char boolByte;
int usedBoolByte = 8;

// Initialize the random generator
void init_randomness() {
  cout << "Reading random bytes from seed" << endl;
  for (uint32_t i = 1; i <= 100; ++i) {
    ifstream input("bytes1.bin", ios::binary | ios::in);
    randomBytes.insert(randomBytes.end(), (istreambuf_iterator<char>(input)),
                       (istreambuf_iterator<char>()));
    input.close();
  }
#ifdef DEBUG
  cout << "Available number of random bytes: " << randomBytes.size() << endl;
#endif
  randomHasInit = true;
  usedBytes = 0;
  usedBoolByte = 8;
}

// Returns a random byte from the seed
// Calls init_randomness if it hasn't already been called.
char getRandomByte() {
  if (!randomHasInit) init_randomness();
  ++usedBytes;
#ifdef DEBUG
  assert(!randomBytes.empty());
#endif
  char c = randomBytes.back();
  randomBytes.pop_back();
  return c;
}

// Returns a random bool
// We use just one bit per bool by popping a byte and using its bits one at a
// time.
bool getRandomBool() {
  if (!randomHasInit) init_randomness();
#ifdef DEBUG
  assert(usedBoolByte <= 8);
#endif
  if (usedBoolByte == 8) {
    usedBoolByte = 0;
    boolByte = getRandomByte();
  }
  ++usedBoolByte;
  bool ret = boolByte & 1;
  boolByte >>= 1;
  return ret;
}

// Returns a random 32-bit unsigned integer
uint32_t getRandomUInt32() {
  uint32_t a(0);
  for (uint32_t i = 0; i < 4; ++i) {
    int32_t t(getRandomByte());
    if (t < 0) t += (1 << 8);
    a = (a << 8) + t;
  }
  return a;
}

// Returns a random 64-bit unsigned integer
uint64_t getRandomUInt64() {
  uint64_t a(0);
  for (uint64_t i = 0; i < 8; ++i) {
    int64_t t(getRandomByte());
    if (t < 0) t += (1 << 8);
    a = (a << 8) + t;
  }
  return a;
}

// Returns a random 128-bit unsigned integer
__uint128_t getRandomUInt128() {
  __uint128_t a(0);
  for (uint64_t i = 0; i < 16; ++i) {
    __uint128_t t(getRandomByte());
    if (t < 0) t += (1 << 8);
    a = (a << 8) + t;
  }
  return a;
}

#endif  // _RANDOMGEN_H_
