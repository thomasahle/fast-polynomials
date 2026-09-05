// Validation driver for chainhash_goldi.h.
//  (1) FIN_CHAR2 of the experimental header == the shipped chainhash.h (HEAD), 2000 messages, both configs;
//  (2) prints the hashes of the same 2000 (seed, message) pairs for goldi_ref.py (G4/G5 and CHAR2);
//  (3) SMHasher3 verification codes (LE) of every registration, computed the way lib/Hashinfo.cpp does.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include "chainhash_shipped.h"
#include "chainhash_goldi.h"
using namespace chainhash_goldi;

struct SMs { uint64_t s; explicit SMs(uint64_t st) : s(st) {} uint64_t next() { return splitmix64(s); } };

template <class H> static uint32_t vcode() {
    std::vector<uint8_t> key(256), hashes(256 * 8);
    for (int i = 0; i < 256; i++) {
        H h((uint64_t)(256 - i));
        uint64_t v = h(key.data(), (size_t)i);
        memcpy(&hashes[8 * i], &v, 8);
        key[i] = (uint8_t)i;
    }
    H h0((uint64_t)0);
    uint64_t total = h0(hashes.data(), hashes.size());
    return (uint32_t)total;   // first four bytes, little-endian
}

int main() {
    int bad = 0;
    std::vector<uint8_t> buf;
    for (int i = 0; i < 2000; i++) {
        SMs sm(0xABCDEFULL + (uint64_t)i);
        size_t len = (size_t)(sm.next() % 2101);
        buf.assign((len + 7) / 8 * 8 + 16, 0);
        for (size_t w = 0; w < (len + 7) / 8; w++) { uint64_t x = sm.next(); memcpy(&buf[8 * w], &x, 8); }
        uint64_t seed = sm.next();
        // (1) shipped vs experimental CHAR2
        chainhash::ChainHash256 s256(seed); chainhash::ChainHash1k s1k(seed);
        ChainHash256 e256(seed); ChainHash1k e1k(seed);
        uint64_t h256 = e256(buf.data(), len), h1k = e1k(buf.data(), len);
        if (h256 != s256(buf.data(), len) || h1k != s1k(buf.data(), len)) { bad++; printf("CHAR2 MISMATCH vs shipped at i=%d len=%zu\n", i, len); }
        // (2) all configurations for the Python reference
        ChainHashG4_256 g4(seed); ChainHashG5_256 g5(seed); ChainHashG5_1k g51k(seed);
        printf("M %d %zu %016llx %016llx %016llx %016llx %016llx\n", i, len, (unsigned long long)h256,
               (unsigned long long)g4(buf.data(), len), (unsigned long long)g5(buf.data(), len),
               (unsigned long long)h1k, (unsigned long long)g51k(buf.data(), len));
    }
    printf("shipped-vs-experimental CHAR2: 2000 messages x 2 configurations, %d mismatches\n", bad);
    printf("VCODE chainhash-256 (shipped header) %08x\n", vcode<chainhash::ChainHash256>());
    printf("VCODE chainhash-1k (shipped header) %08x\n", vcode<chainhash::ChainHash1k>());
    printf("VCODE chainhash-256 (exp CHAR2) %08x\n", vcode<ChainHash256>());
    printf("VCODE chainhash-g4-256 %08x\n", vcode<ChainHashG4_256>());
    printf("VCODE chainhash-g5-256 %08x\n", vcode<ChainHashG5_256>());
    printf("VCODE chainhash-g5-1k %08x\n", vcode<ChainHashG5_1k>());
    printf("key words: g4-256 %zu, g5-256 %zu, g5-1k %zu (shipped 256: %zu, 1k: %zu)\n",
           ChainHashG4_256::key_t::random_key_bytes / 8, ChainHashG5_256::key_t::random_key_bytes / 8,
           ChainHashG5_1k::key_t::random_key_bytes / 8, ChainHash256::key_t::random_key_bytes / 8, ChainHash1k::key_t::random_key_bytes / 8);
    return bad ? 1 : 0;
}
