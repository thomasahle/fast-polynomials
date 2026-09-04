/* ============================================================================
 * selftest.cpp -- validation of the vendored faithful aHash 0.8.10 port.
 *
 * (1) GOLD VECTORS: 155 (seed,len) cases whose expected outputs were produced
 *     by BUILDING AND RUNNING THE REAL aHash 0.8.10 crate on this same aarch64
 *     machine (features = ["nightly-arm-aes"], RUSTFLAGS="-C target-cpu=native",
 *     replicating smhasher/ahash-cbindings' `ahash64`). The published crate's
 *     hashing sources were verified byte-identical to the git v0.8.10 tag.
 *     A byte-for-byte match here proves the C++ port reproduces the reference.
 *
 * (2) FIPS-197 sanity: the aesenc primitive is checked against the official
 *     NIST AES-128 known-answer (Appendix B / C.1) so the AES round itself is
 *     independently anchored to a published standard vector.
 *
 * Build: clang++ -O3 -std=c++17 -march=native selftest.cpp -o selftest && ./selftest
 * ==========================================================================*/
#include <cstdio>
#include <vector>
#include "ahash.h"

using namespace ahash_0810;

/* deterministic input generator -- MUST match ahref/src/main.rs gen_input() */
static std::vector<uint8_t> gen_input(size_t len){
    std::vector<uint8_t> v(len);
    for (size_t i = 0; i < len; i++)
        v[i] = (uint8_t)(((uint64_t)i * 179 + 71) & 0xff);
    return v;
}

struct Vec { uint64_t seed; size_t len; uint64_t expect; };
static const Vec VECS[] = {
    {0x0000000000000000ULL, 0, 0x568000a78186bf3bULL},
    {0x0000000000000000ULL, 1, 0xee548214697efcbdULL},
    {0x0000000000000000ULL, 2, 0x56e148419285cf33ULL},
    {0x0000000000000000ULL, 3, 0xa1b2ea5865a72972ULL},
    {0x0000000000000000ULL, 4, 0xa82339e0921e0f52ULL},
    {0x0000000000000000ULL, 5, 0xdad604a938f841c5ULL},
    {0x0000000000000000ULL, 7, 0xcb3907a19c1c1bdbULL},
    {0x0000000000000000ULL, 8, 0x942e52290c2724b6ULL},
    {0x0000000000000000ULL, 9, 0x53dbfb573dbfc29eULL},
    {0x0000000000000000ULL, 15, 0x4c9783ff6b5678e2ULL},
    {0x0000000000000000ULL, 16, 0x48c7ef410d12f32dULL},
    {0x0000000000000000ULL, 17, 0x868683c08abf826fULL},
    {0x0000000000000000ULL, 23, 0x4c5c08b79532c5f4ULL},
    {0x0000000000000000ULL, 31, 0xb0c0b34f2c224d9fULL},
    {0x0000000000000000ULL, 32, 0x7bc6e1aab836d150ULL},
    {0x0000000000000000ULL, 33, 0xd40ed19c9b2b76c1ULL},
    {0x0000000000000000ULL, 40, 0x5046957f537bcd21ULL},
    {0x0000000000000000ULL, 48, 0x60e32da1e85c946bULL},
    {0x0000000000000000ULL, 63, 0x24878c12b4ec61aaULL},
    {0x0000000000000000ULL, 64, 0xa6742eb039ea4e67ULL},
    {0x0000000000000000ULL, 65, 0xd06c8c5d013dbda5ULL},
    {0x0000000000000000ULL, 80, 0x93530eca81564036ULL},
    {0x0000000000000000ULL, 96, 0x8b6b0dfb6ab697d9ULL},
    {0x0000000000000000ULL, 127, 0xb8df82568c990647ULL},
    {0x0000000000000000ULL, 128, 0x7f6b8c7a2040520dULL},
    {0x0000000000000000ULL, 129, 0x5ae515ba51a64432ULL},
    {0x0000000000000000ULL, 200, 0xc1fa96a944d334c6ULL},
    {0x0000000000000000ULL, 256, 0xc7b35eedbab944c3ULL},
    {0x0000000000000000ULL, 257, 0x76d4f14dcb0c3d27ULL},
    {0x0000000000000000ULL, 512, 0xe808c94abae6720fULL},
    {0x0000000000000000ULL, 1000, 0x6fc66f7e693c390aULL},
    {0x0000000000000001ULL, 0, 0x025a47244654984aULL},
    {0x0000000000000001ULL, 1, 0x307e692805b426a8ULL},
    {0x0000000000000001ULL, 2, 0x21373d110edc0e04ULL},
    {0x0000000000000001ULL, 3, 0xf8e923039038b27dULL},
    {0x0000000000000001ULL, 4, 0x14762f9f3e4e83caULL},
    {0x0000000000000001ULL, 5, 0x57995ec0c39abc88ULL},
    {0x0000000000000001ULL, 7, 0x9abd8a15a92167dbULL},
    {0x0000000000000001ULL, 8, 0x7ba1ea5a883bfa77ULL},
    {0x0000000000000001ULL, 9, 0xbb690823c3ab7f62ULL},
    {0x0000000000000001ULL, 15, 0x283653afc84ea87eULL},
    {0x0000000000000001ULL, 16, 0xa1bc35aac9b209f5ULL},
    {0x0000000000000001ULL, 17, 0xe4f5842be45a20cbULL},
    {0x0000000000000001ULL, 23, 0x3a51966a3f170466ULL},
    {0x0000000000000001ULL, 31, 0x143c6ed7bcb75773ULL},
    {0x0000000000000001ULL, 32, 0xe79590aca4c820a5ULL},
    {0x0000000000000001ULL, 33, 0x2c1c3c40a0e9ffd5ULL},
    {0x0000000000000001ULL, 40, 0x513133fa806abe1eULL},
    {0x0000000000000001ULL, 48, 0x0740712af17161dfULL},
    {0x0000000000000001ULL, 63, 0x192c0d25c0535e0eULL},
    {0x0000000000000001ULL, 64, 0xcc31faed23527b1cULL},
    {0x0000000000000001ULL, 65, 0x9688b77546249f65ULL},
    {0x0000000000000001ULL, 80, 0xe5e9bdf0ff9acd57ULL},
    {0x0000000000000001ULL, 96, 0x9d7d44c8ba52b538ULL},
    {0x0000000000000001ULL, 127, 0xc7c2a82b36b579bdULL},
    {0x0000000000000001ULL, 128, 0x924fbe702d54f1b8ULL},
    {0x0000000000000001ULL, 129, 0x5ab58092a4f358beULL},
    {0x0000000000000001ULL, 200, 0x25307789a2ce1be1ULL},
    {0x0000000000000001ULL, 256, 0x389c2016837a931aULL},
    {0x0000000000000001ULL, 257, 0x450ccee71ce722ddULL},
    {0x0000000000000001ULL, 512, 0x77d7758ead5141a2ULL},
    {0x0000000000000001ULL, 1000, 0x7350f461405fd9ffULL},
    {0x0123456789abcdefULL, 0, 0x73807b8b6cdf75f6ULL},
    {0x0123456789abcdefULL, 1, 0x2406c0d52ef1f3c3ULL},
    {0x0123456789abcdefULL, 2, 0xc3093f776535d3e4ULL},
    {0x0123456789abcdefULL, 3, 0xd9bf06c9cb34184bULL},
    {0x0123456789abcdefULL, 4, 0x28c8080b5c5bef35ULL},
    {0x0123456789abcdefULL, 5, 0x4888fbc96970d31fULL},
    {0x0123456789abcdefULL, 7, 0x734d1b7c92a71415ULL},
    {0x0123456789abcdefULL, 8, 0x42596179538bc92fULL},
    {0x0123456789abcdefULL, 9, 0xb45536d2218f2201ULL},
    {0x0123456789abcdefULL, 15, 0x6ff58f64c01ac58fULL},
    {0x0123456789abcdefULL, 16, 0xb3d062879c444ad7ULL},
    {0x0123456789abcdefULL, 17, 0x63dbf205454b6945ULL},
    {0x0123456789abcdefULL, 23, 0x0ef8440da9bce5a0ULL},
    {0x0123456789abcdefULL, 31, 0xd9a2cae537fb2f2cULL},
    {0x0123456789abcdefULL, 32, 0xb0dea8750d000f6fULL},
    {0x0123456789abcdefULL, 33, 0x5087e061b6b3c875ULL},
    {0x0123456789abcdefULL, 40, 0xafe48241c2da4734ULL},
    {0x0123456789abcdefULL, 48, 0x3f02dea488b0c292ULL},
    {0x0123456789abcdefULL, 63, 0x3954b53aed00e526ULL},
    {0x0123456789abcdefULL, 64, 0xb8aee255eafe5271ULL},
    {0x0123456789abcdefULL, 65, 0xeadf100617b4ddfcULL},
    {0x0123456789abcdefULL, 80, 0xf4fedd0fc292a268ULL},
    {0x0123456789abcdefULL, 96, 0xc21d720210939c78ULL},
    {0x0123456789abcdefULL, 127, 0xe2a1bb604aa215c7ULL},
    {0x0123456789abcdefULL, 128, 0x7d523d0a515d3efcULL},
    {0x0123456789abcdefULL, 129, 0x128a76196439cec4ULL},
    {0x0123456789abcdefULL, 200, 0x36cf2a7e7d0ff015ULL},
    {0x0123456789abcdefULL, 256, 0xe99bccc4d6c88089ULL},
    {0x0123456789abcdefULL, 257, 0x03b96245396c123dULL},
    {0x0123456789abcdefULL, 512, 0x65f3cb1ff8605963ULL},
    {0x0123456789abcdefULL, 1000, 0x3dd5b56150275a12ULL},
    {0xffffffffffffffffULL, 0, 0x0eb0e7532109c879ULL},
    {0xffffffffffffffffULL, 1, 0xe2f7eb58bc2652cbULL},
    {0xffffffffffffffffULL, 2, 0x503df9255da29f6fULL},
    {0xffffffffffffffffULL, 3, 0x6d1e6da117fc47d0ULL},
    {0xffffffffffffffffULL, 4, 0x668ffa9f2bacae0bULL},
    {0xffffffffffffffffULL, 5, 0xfcdadfeee593fac2ULL},
    {0xffffffffffffffffULL, 7, 0xf9eade0311350b0dULL},
    {0xffffffffffffffffULL, 8, 0xb7e5778e856e8b37ULL},
    {0xffffffffffffffffULL, 9, 0x73b8bd8b669f585fULL},
    {0xffffffffffffffffULL, 15, 0x1dbaa88a9e022df7ULL},
    {0xffffffffffffffffULL, 16, 0xdffe0eef79410e80ULL},
    {0xffffffffffffffffULL, 17, 0x99973f9d3a830a32ULL},
    {0xffffffffffffffffULL, 23, 0x9fa9bba1810a06ffULL},
    {0xffffffffffffffffULL, 31, 0x0e118e02018de755ULL},
    {0xffffffffffffffffULL, 32, 0xb07e5a3969b76836ULL},
    {0xffffffffffffffffULL, 33, 0x87a5aa3cac5d32bfULL},
    {0xffffffffffffffffULL, 40, 0x139033ae5f01734eULL},
    {0xffffffffffffffffULL, 48, 0x1c4872f1f7060ea3ULL},
    {0xffffffffffffffffULL, 63, 0xfb03c7e3a12a24aeULL},
    {0xffffffffffffffffULL, 64, 0x4b1e127997549e40ULL},
    {0xffffffffffffffffULL, 65, 0xefa65d91c1a9bbfcULL},
    {0xffffffffffffffffULL, 80, 0xf0e352112d4717d2ULL},
    {0xffffffffffffffffULL, 96, 0x4bff792047707879ULL},
    {0xffffffffffffffffULL, 127, 0xe32903b0b24a9ad2ULL},
    {0xffffffffffffffffULL, 128, 0xc09cbbe0f628662eULL},
    {0xffffffffffffffffULL, 129, 0xe54bd0963ae14f02ULL},
    {0xffffffffffffffffULL, 200, 0x7783ed44884b622cULL},
    {0xffffffffffffffffULL, 256, 0x9c5a4734f923ea16ULL},
    {0xffffffffffffffffULL, 257, 0xe78f90d6168a727bULL},
    {0xffffffffffffffffULL, 512, 0x262227b46bc60a5dULL},
    {0xffffffffffffffffULL, 1000, 0x773fb02ac8fd5dfbULL},
    {0x9e3779b97f4a7c15ULL, 0, 0xe7bbf0a61ee384c1ULL},
    {0x9e3779b97f4a7c15ULL, 1, 0x6f22d831df8135f2ULL},
    {0x9e3779b97f4a7c15ULL, 2, 0x5930538712a71737ULL},
    {0x9e3779b97f4a7c15ULL, 3, 0xba66b92701f33b8bULL},
    {0x9e3779b97f4a7c15ULL, 4, 0x01fb21ee9a67dd75ULL},
    {0x9e3779b97f4a7c15ULL, 5, 0x6b544ed2ed36b350ULL},
    {0x9e3779b97f4a7c15ULL, 7, 0x31b9015d37dfd12cULL},
    {0x9e3779b97f4a7c15ULL, 8, 0x47f94fce26b655caULL},
    {0x9e3779b97f4a7c15ULL, 9, 0xf34fe8941e353d09ULL},
    {0x9e3779b97f4a7c15ULL, 15, 0x2f9fe6f047a072fdULL},
    {0x9e3779b97f4a7c15ULL, 16, 0x3537dfda37fee18aULL},
    {0x9e3779b97f4a7c15ULL, 17, 0x58928e859695978cULL},
    {0x9e3779b97f4a7c15ULL, 23, 0x7c986cc22905dab8ULL},
    {0x9e3779b97f4a7c15ULL, 31, 0x149d5078e8315650ULL},
    {0x9e3779b97f4a7c15ULL, 32, 0x5a0122b8832da4fbULL},
    {0x9e3779b97f4a7c15ULL, 33, 0x5f01bc5148436f11ULL},
    {0x9e3779b97f4a7c15ULL, 40, 0xc08f8c0fb3e3931cULL},
    {0x9e3779b97f4a7c15ULL, 48, 0xc527472ef726f9deULL},
    {0x9e3779b97f4a7c15ULL, 63, 0x4f9d2af93d9d5118ULL},
    {0x9e3779b97f4a7c15ULL, 64, 0x45b7233b6601bf6eULL},
    {0x9e3779b97f4a7c15ULL, 65, 0x0561eb8a475b6732ULL},
    {0x9e3779b97f4a7c15ULL, 80, 0xa9247a21677d31faULL},
    {0x9e3779b97f4a7c15ULL, 96, 0xdd7fe16d833dc574ULL},
    {0x9e3779b97f4a7c15ULL, 127, 0xce1071dff1e3f5ebULL},
    {0x9e3779b97f4a7c15ULL, 128, 0x4f6ac4845af3a2f7ULL},
    {0x9e3779b97f4a7c15ULL, 129, 0x40b3ba8e245567c4ULL},
    {0x9e3779b97f4a7c15ULL, 200, 0x59b03b03483e0ad9ULL},
    {0x9e3779b97f4a7c15ULL, 256, 0x0b7d6f99dfa40fd9ULL},
    {0x9e3779b97f4a7c15ULL, 257, 0x53ebd6562342dca2ULL},
    {0x9e3779b97f4a7c15ULL, 512, 0xcbe1b3b3a47e6411ULL},
    {0x9e3779b97f4a7c15ULL, 1000, 0x5fbe7ff66fc1df4cULL},
};

/* ---- FIPS-197 single-round anchor -------------------------------------- */
/* AES-128, PT = 00112233445566778899aabbccddeeff, cipher key CK = 000102..0f.
 * FIPS-197 App. B: round-1 input (after initial AddRoundKey) is
 *   00102030405060708090a0b0c0d0e0f0, and the round-1 key schedule word is
 *   K1 = d6aa74fdd2af72fadaa678f1d6ab76fe. A full AES encryption round is
 *   MixColumns.SubBytes.ShiftRows(state) ^ K1, i.e. exactly aesenc(state,K1).
 * FIPS-197 lists "Start of Round 2" = 89d810e8855ace682d1843d8cb128fe4,
 * which is the output of round 1 == aesenc(round1_in, K1).            */
static u128 h2u128_be(const char* hex){ /* hex is big-endian byte string */
    uint8_t b[16];
    for (int i=0;i<16;i++){ unsigned x; sscanf(hex+2*i,"%2x",&x); b[i]=(uint8_t)x; }
    u128 v; std::memcpy(&v,b,16); return v;
}

AHASH_TARGET
static int fips197_ok(){
    u128 state = h2u128_be("00102030405060708090a0b0c0d0e0f0");
    u128 k1    = h2u128_be("d6aa74fdd2af72fadaa678f1d6ab76fe");
    u128 got   = aesenc(state, k1);
    u128 want  = h2u128_be("89d810e8855ace682d1843d8cb128fe4");
    return got == want;
}

int main(){
    int fails = 0;

    if (!fips197_ok()) { printf("FIPS-197 AES round KAT: FAIL\n"); fails++; }
    else               printf("FIPS-197 AES round KAT: OK\n");

    size_t n = sizeof(VECS)/sizeof(VECS[0]);
    int vfail = 0;
    for (size_t i = 0; i < n; i++){
        auto in = gen_input(VECS[i].len);
        uint64_t h = ahash64(in.data(), VECS[i].len, VECS[i].seed);
        if (h != VECS[i].expect){
            if (vfail < 8)
                printf("MISMATCH seed=%016llx len=%zu got=%016llx want=%016llx\n",
                       (unsigned long long)VECS[i].seed, VECS[i].len,
                       (unsigned long long)h, (unsigned long long)VECS[i].expect);
            vfail++; fails++;
        }
    }
    printf("aHash 0.8.10 gold vectors: %zu/%zu matched\n", n - vfail, n);
    printf("%s (%d failures)\n", fails ? "SELFTEST FAILED" : "SELFTEST PASSED", fails);
    return fails ? 1 : 0;
}
