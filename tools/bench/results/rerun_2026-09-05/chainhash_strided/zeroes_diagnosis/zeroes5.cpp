// Zeroes delta-distribution bias (SMHasher3 testDeltas(1) statistic) for design variants, 256 B S=1 and 1 KB S=2.
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <algorithm>
#include "chainhash_ref.h"
using namespace chainhash_ref;

enum LenMode { LEN_A = 0, LEN_AB = 1, LEN_MUL_A = 2 };
static inline uint64_t enc(uint64_t len, int mode) { return mode == LEN_MUL_A ? len * 0x9E3779B97F4A7C15ull : len; }

template <int BW, int S>
struct ZeroEval {
    typedef Key<BW, 5, S> K;
    const K& key; int gran; int mode;
    static constexpr int SW = BW / S;            // words per sub-block
    std::vector<uint64_t> A[S], B[S];            // per sub-block PH prefix over pair-units (zero data)
    std::vector<uint64_t> Pfull;                 // P after i full zero blocks
    int units;
    ZeroEval(const K& k, int g, int m) : key(k), gran(g), mode(m) {
        units = 8 * SW / gran;
        for (int i = 0; i < S; i++) {
            A[i].assign(units + 1, 0); B[i].assign(units + 1, 0);
            u128 acc = 0; const uint64_t* kk = key.k + i * SW;
            for (int G = 1; G <= units; G++) {
                if (gran == 16) acc ^= clmul(kk[2*(G-1)], kk[2*(G-1)+1]);
                else { int g0 = 4*(G-1); acc ^= clmul(kk[g0], kk[g0+2]); acc ^= clmul(kk[g0+1], kk[g0+3]); }
                A[i][G] = (uint64_t)acc; B[i][G] = (uint64_t)(acc >> 64);
            }
        }
        Pfull.assign(4096, 0); Pfull[0] = key.z;
        for (int i = 1; i < 4096; i++) { uint64_t P = Pfull[i-1]; for (int s = 0; s < S; s++) P = A[s][units] ^ gfmul(B[s][units] ^ key.y, P ^ key.u); Pfull[i] = P; }
    }
    uint64_t hash(size_t len) const {
        const size_t BB = 8 * BW, SB = 8 * SW;
        size_t n = (len == 0) ? 1 : (len + BB - 1) / BB;
        size_t r = len - BB * (n - 1);
        uint64_t P = Pfull[n-1];
        for (int s = 0; s < S; s++) {
            size_t rs = std::min(SB, (r > (size_t)s * SB) ? r - s * SB : 0);
            size_t G = (rs + gran - 1) / gran;
            uint64_t a = A[s][G], b = B[s][G];
            if (s + 1 == S) { a ^= enc(len, mode); if (mode == LEN_AB) b ^= len; }
            P = a ^ gfmul(b ^ key.y, P ^ key.u);
        }
        return chain<5>(key.c, P + key.t_in);
    }
};

static inline uint32_t window(uint64_t h, int start, int width) {
    uint64_t r = (h >> start) | (start ? (h << (64 - start)) : 0);
    return (uint32_t)(r & ((1ull << width) - 1));
}
static double bias(const std::vector<uint64_t>& h, int* pw, int* pb) {   // SMHasher3 display value
    size_t N = h.size(); std::vector<uint64_t> d(N);
    for (size_t i = 0; i + 1 < N; i++) d[i] = h[i] ^ h[i+1];
    d[N-1] = h[N-1] ^ h[0];
    double worst = -1; *pw = *pb = -1;
    for (int w = 8; w <= 15; w++) for (int b = 0; b < 64; b++) {
        std::vector<uint32_t> cnt(1u << w, 0);
        for (size_t i = 0; i < N; i++) cnt[window(d[i], b, w)]++;
        double sumsq = 0; for (uint32_t c : cnt) sumsq += (double)c * c;
        double n = (double)(1u << w), m = (double)N, lambda = m / n;
        double rr = (sqrt(sumsq / m - lambda) - 1.0) * sqrt(2.0 * n) / sqrt(2.0 * w);
        if (rr > worst) { worst = rr; *pb = b; *pw = w; }
    }
    return worst;
}

template <int BW, int S>
static void run(const char* cfg, uint64_t seed) {
    typename ZeroEval<BW,S>::K key = ZeroEval<BW,S>::K::from_seed(seed);
    size_t N = 200 * 1024;
    struct V { const char* name; int gran; int mode; } vs[] = {
        {"adjacent 16B, len->a       ", 16, LEN_A}, {"strided 32B, len->a  (now)", 32, LEN_A},
        {"strided 32B, len->a,b      ", 32, LEN_AB}, {"strided 32B, len*odd->a    ", 32, LEN_MUL_A},
        {"adjacent 16B, len->a,b     ", 16, LEN_AB} };
    for (auto& v : vs) {
        ZeroEval<BW,S> ev(key, v.gran, v.mode);
        if (seed == 0 && v.gran == 32 && v.mode == LEN_A) {   // sanity against the bit-serial reference
            std::vector<uint8_t> z(5000, 0);
            for (size_t l : {0ul, 1ul, 9ul, 16ul, 17ul, 31ul, 32ul, 33ul, 255ul, 256ul, 257ul, 511ul, 512ul, 513ul, 1023ul, 1024ul, 1025ul, 1536ul, 1537ul, 4999ul})
                if (hash<BW,5,S>(key, z.data(), l) != ev.hash(l)) { printf("MISMATCH %s len %zu\n", cfg, l); exit(1); }
        }
        std::vector<uint64_t> h(N); for (size_t i = 0; i < N; i++) h[i] = ev.hash(i);
        int w, b; double x = bias(h, &w, &b);
        printf("%s seed %llu  %s : %.2fx (width %d bit %d)%s\n", cfg, (unsigned long long)seed, v.name, x, w, b, x > 1.5 ? "  <-- fails" : "");
    }
}
int main(int argc, char** argv) {
    int nseeds = argc > 1 ? atoi(argv[1]) : 4;
    for (uint64_t s = 0; s < (uint64_t)nseeds; s++) { run<32,1>("256B/S=1", s); run<128,2>("1KB/S=2 ", s); }
    return 0;
}
