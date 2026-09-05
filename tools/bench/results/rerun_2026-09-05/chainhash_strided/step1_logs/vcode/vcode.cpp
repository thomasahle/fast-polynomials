// Recompute SMHasher3's LE verification code from the bench headers (chainhash.h fast, chainhash_ref.h reference):
// keys {}, {0}, {0,1}, ... up to 255 bytes, seed 256 - i; then the 2048-byte concatenation with seed 0; first 4 bytes LE.
#include <cstdio>
#include <cstdint>
#include <cstring>
#include "chainhash.h"
#include "chainhash_ref.h"
template <int BW, int S> static void run(const char* name) {
    uint8_t key[256], hashes_f[2048], hashes_r[2048];
    memset(key, 0, 256);
    for (int i = 0; i < 256; i++) {
        auto fk = chainhash::Key<BW, 5, S>::from_seed((uint64_t)(256 - i));
        auto rk = chainhash_ref::Key<BW, 5, S>::from_seed((uint64_t)(256 - i));
        uint64_t hf = chainhash::hash(fk, key, (size_t)i), hr = chainhash_ref::hash(rk, key, (size_t)i);
        for (int j = 0; j < 8; j++) { hashes_f[8 * i + j] = (uint8_t)(hf >> (8 * j)); hashes_r[8 * i + j] = (uint8_t)(hr >> (8 * j)); }
        key[i] = (uint8_t)i;
    }
    auto fk0 = chainhash::Key<BW, 5, S>::from_seed(0);
    auto rk0 = chainhash_ref::Key<BW, 5, S>::from_seed(0);
    uint64_t tf = chainhash::hash(fk0, hashes_f, 2048), tr = chainhash_ref::hash(rk0, hashes_r, 2048);
    printf("%s: fast LE vcode 0x%08X, reference LE vcode 0x%08X\n", name, (uint32_t)tf, (uint32_t)tr);
}
int main() { run<32, 1>("chainhash-256"); run<128, 2>("chainhash-1k"); return 0; }
