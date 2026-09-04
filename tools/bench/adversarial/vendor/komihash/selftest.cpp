/*
 * Standalone validation of the vendored komihash reference (komihash.h v5.34).
 *
 * Reproduces the official testvec.c construction (strings + bulk buffer of an
 * incrementing byte sequence) and compares every hash against the published
 * test vectors in the komihash README.md, for the three documented seeds
 * (0, 0x0123456789ABCDEF, 256).
 *
 * Build:  clang++ -O3 -std=c++17 -march=native selftest.cpp -o selftest
 * Run:    ./selftest    (exit code 0 = all vectors match byte-for-byte)
 */
#include <cstdio>
#include <cstring>
#include <cstdint>
#include <string>
#include <vector>

#include "komihash.h"

struct StrVec { const char* s; uint64_t expect; };
struct BulkVec { int len;       uint64_t expect; };

int main() {
    // Official testvec.c string set.
    const char* strs[5] = {
        "This is a 32-byte testing string",
        "The cat is out of the bag",
        "A 16-byte string",
        "The new string",
        "7 chars"
    };
    // Official testvec.c bulk lengths.
    const int bulks[17] = { 3, 6, 8, 12, 20, 31, 32, 40, 47, 48, 56, 64,
                            72, 80, 112, 132, 256 };

    // bulk buffer: incrementing 8-bit values, exactly as testvec.c builds it.
    uint8_t bulkbuf[256];
    for (int i = 0; i < 256; i++) bulkbuf[i] = (uint8_t)i;

    struct SeedBlock {
        uint64_t seed;
        uint64_t strexp[5];   // expected string hashes
        uint64_t bulkexp[17]; // expected bulk hashes
    };

    // Published README.md test vectors (komihash v5.x).
    SeedBlock blocks[3] = {
        { 0x0000000000000000ULL,
          { 0x05ad960802903a9dULL, 0xd15723521d3c37b1ULL, 0x467caa28ea3da7a6ULL,
            0xf18e67bc90c43233ULL, 0x2c514f6e5dcb11cbULL },
          { 0x7a9717e9eea4be8bULL, 0xa56469564c2ea0ffULL, 0x00b4313a24431306ULL,
            0x64c2ad96013f70feULL, 0x7a3888bc95545364ULL, 0xc77e02ed4b201b9aULL,
            0x256d74350303a1baULL, 0x59609c71697bb9dfULL, 0x36eb9e6a4c2c5e4bULL,
            0x8dd56c332850baa6ULL, 0xcbb722192b353999ULL, 0x90b07e2158f88cc0ULL,
            0x24c9621701603741ULL, 0x1d4c1d97ca684334ULL, 0xd1a425d530652287ULL,
            0x72623be342c20ab5ULL, 0x94c3dbdca59ddf57ULL } },
        { 0x0123456789abcdefULL,
          { 0x6ce66a2e8d4979a5ULL, 0x5b1da0b43545d196ULL, 0x26af914213d0c915ULL,
            0x62d9ca1b73250cb5ULL, 0x90ab7c9f831cd940ULL },
          { 0x84ae4eb65b96617eULL, 0xaceebc32a3c0d9e4ULL, 0xdaa1a90ecb95f6f8ULL,
            0xec8eb3ef4af380b4ULL, 0x07045bd31abba34cULL, 0xd5f619fb2e62c4aeULL,
            0x5a336fd2c4c39abeULL, 0x0e870b4623eea8ecULL, 0xe552edd6bf419d1dULL,
            0x37d170ddcb1223e6ULL, 0x1cd89e708e5098b6ULL, 0x765490569ccd77f2ULL,
            0x19e9d77b86d01ee8ULL, 0x25f83ee520c1d241ULL, 0xd6007417091cd4c0ULL,
            0x3e49c2d3727b9cc9ULL, 0xb2b3405ee5d65f4cULL } },
        { 0x0000000000000100ULL,   // 256
          { 0x5f197b30bcec1e45ULL, 0xa761280322bb7698ULL, 0x11c31ccabaa524f1ULL,
            0x3a43b7f58281c229ULL, 0xcff90b0466b7e3a2ULL },
          { 0x8ab53f45cc9315e3ULL, 0xea606e43d1976ccfULL, 0x889b2f2ceecbec73ULL,
            0xacbec1886cd23275ULL, 0x57c3affd1b71fcdbULL, 0x7ef6ba49a3b068c3ULL,
            0x49dbca62ed5a1ddfULL, 0x192848484481e8c0ULL, 0x420b43a5edba1bd7ULL,
            0xd6e8400a9de24ce3ULL, 0xbea291b225ff384dULL, 0x0ec94062b2f06960ULL,
            0xfa613272ecd49985ULL, 0x76f0bb380bc207beULL,
            0 /*112*/, 0 /*132*/, 0 /*256*/ } }
    };
    // The README lists only through bulk(80) for seed 256; mark the rest unknown.
    bool bulk_known_seed256[17] = { true,true,true,true,true,true,true,true,
                                    true,true,true,true,true,true,false,false,false };

    int fail = 0, checked = 0;
    for (int b = 0; b < 3; b++) {
        uint64_t seed = blocks[b].seed;
        for (int i = 0; i < 5; i++) {
            uint64_t got = komihash(strs[i], strlen(strs[i]), seed);
            uint64_t exp = blocks[b].strexp[i];
            bool ok = (got == exp);
            checked++;
            if (!ok) { fail++;
                printf("FAIL seed=0x%016llx \"%s\": got 0x%016llx want 0x%016llx\n",
                       (unsigned long long)seed, strs[i],
                       (unsigned long long)got, (unsigned long long)exp);
            }
        }
        for (int i = 0; i < 17; i++) {
            if (b == 2 && !bulk_known_seed256[i]) continue; // README truncated
            uint64_t got = komihash(bulkbuf, (size_t)bulks[i], seed);
            uint64_t exp = blocks[b].bulkexp[i];
            bool ok = (got == exp);
            checked++;
            if (!ok) { fail++;
                printf("FAIL seed=0x%016llx bulk(%d): got 0x%016llx want 0x%016llx\n",
                       (unsigned long long)seed, bulks[i],
                       (unsigned long long)got, (unsigned long long)exp);
            }
        }
    }

    printf("komihash v5.34 self-test: %d/%d official vectors matched.\n",
           checked - fail, checked);
    if (fail == 0) { printf("ALL PASS\n"); return 0; }
    printf("%d FAILURES\n", fail);
    return 1;
}
