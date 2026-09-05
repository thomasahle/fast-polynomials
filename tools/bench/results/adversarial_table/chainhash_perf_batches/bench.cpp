// Small-key / bulk microbenchmark for one version of chainhash.h (path in CH_HEADER).
//   tp   : independent back-to-back calls (result XOR-accumulated)
//   lat4 : SMHasher3 timehash_small style: 4-byte store of (i ^ hash) into key[0..4) before the next call
// Cycles = time x calibrated GHz (dependent 1-cycle ADD chain, interleaved with every trial; see common.h).
// Per length: min over trials x max GHz (robust under contention) and the median of per-trial products.
// Usage: bench [trials] [filter: 256|1k|64]
#include CH_HEADER
#include "common.h"
#include <cstring>
#include <cstdlib>
#include <vector>
using namespace chainhash;

typedef uint64_t (*hfn)(const void* key, const uint8_t* p, size_t len);
template <class KeyT>
static __attribute__((noinline)) uint64_t hcall(const void* key, const uint8_t* p, size_t len) { return chainhash::hash(*(const KeyT*)key, p, len); }

struct R { double mn, md; };
static R meas(hfn f, const void* key, uint8_t* p, size_t len, int mode, int trials, long reps) {
    uint64_t h = 0, acc = 0;
    double c = bench_cycles([&]() {
        double t0 = now_s();
        if (mode == 0) for (long r = 0; r < reps; r++) acc ^= f(key, p, len);
        else           for (long r = 0; r < reps; r++) { h = f(key, p, len); uint32_t j = (uint32_t)r ^ (uint32_t)h; memcpy(p, &j, 4); }
        return (now_s() - t0) / reps; }, trials);
    g_sink += h + acc;
    return R{c, g_last_med};
}

template <class KeyT>
static void run(const char* name, int trials) {
    KeyT key = KeyT::from_seed(1);
    uint8_t* buf = (uint8_t*)aligned_alloc(64, 65536 + 64);
    for (int i = 0; i < 65536 + 64; i++) buf[i] = (uint8_t)(i * 131 + 7);
    hfn f = hcall<KeyT>;
    size_t lens[] = {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,
                     47,48,63,64,100,127,128,255,256,257,511,512,513,1024,1025,4096,16384};
    printf("\n== %s ==  cycles per call: tp (independent) | lat4 (SMHasher3-style serialization); min-based / median; GB/s from tp at the measured GHz\n", name);
    printf("%7s | %8s %8s | %8s %8s | %8s | %s\n", "len", "tp.min", "tp.med", "lat.min", "lat.med", "GB/s", "GHz");
    double sum_lat = 0, sum_lat_med = 0; int n_small = 0;
    for (size_t len : lens) {
        long reps = len >= 16384 ? 400 : (len >= 4096 ? 1500 : (len >= 256 ? 20000 : 60000));
        meas(f, &key, buf, len, 0, 1, reps);
        R tp = meas(f, &key, buf, len, 0, trials, reps);
        double g = g_last_ghz;
        R lat = meas(f, &key, buf, len, 1, trials, reps);
        printf("%7zu | %8.1f %8.1f | %8.1f %8.1f | %8.2f | %.2f\n", len, tp.mn, tp.md, lat.mn, lat.md, len / tp.mn * g, g);
        if (len >= 1 && len <= 31) { sum_lat += lat.mn; sum_lat_med += lat.md; n_small++; }
    }
    printf("   avg lat4 over 1..31 B: %.2f (min-based)  %.2f (median)\n", sum_lat / n_small, sum_lat_med / n_small);
    free(buf);
}

int main(int argc, char** argv) {
    pin_pcore();
    int trials = argc > 1 ? atoi(argv[1]) : 21;
    const char* filter = argc > 2 ? argv[2] : "all";
    printf("header: %s; calibrated core frequency: %.3f GHz; trials %d\n", CH_HEADER, calib_ghz(5), trials);
    if (!strcmp(filter, "all") || !strcmp(filter, "256")) run<Key<32, 5, 1>>("chainhash-256 <32,5,1>", trials);
    if (!strcmp(filter, "all") || !strcmp(filter, "1k"))  run<Key<128, 5, 2>>("chainhash-1k <128,5,2>", trials);
    if (!strcmp(filter, "all") || !strcmp(filter, "64"))  run<Key<8, 5, 1>>("64-byte blocks <8,5,1>", trials);
    return (int)(g_sink & 1) * 0;
}
