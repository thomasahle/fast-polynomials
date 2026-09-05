// Microbenchmark of the ChainHash finalizer variants (goldilocks_finalizer experiment).
//  Small keys: SMHasher3's timehash_small protocol -- the hash output is XORed into the first 4 bytes
//   of the key so that consecutive calls serialize; TINY_SAMPLES = 15000 hashes per trial, NTRIALS
//   trials, median cycles/hash; lengths 1..31 and 64.  Overhead of an empty hash reported separately
//   (SMHasher3 subtracts it; the tables below are RAW, the overhead line lets you subtract).
//  Bulk: 16 KB and 512 B buffers, independent calls, median GB/s (and bytes/cycle) of NTRIALS trials.
//  Cycles: x86-64 rdtsc/rdtscp (TSC ticks, as SMHasher3); AArch64: nanoseconds x cycles/ns calibrated
//   with SMHasher3's dependent-add loop (one add per cycle on the running core).
// Functions: the SMHasher3 experimental file (chainhash_goldi_exp.cpp through shim/) on both machines;
// on AArch64 additionally the experimental header chainhash_goldi.h and the shipped chainhash.h.
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstring>
#include <vector>
#include <sys/resource.h>
#include "chainhash_goldi_exp.cpp"
#if defined(__aarch64__)
#include "chainhash_shipped.h"
#include "chainhash_goldi.h"
#endif

typedef uint64_t (*HashFn)(const void*, size_t);
static const int TINY_SAMPLES = 15000;
static int NTRIALS = 50;

static inline uint64_t now_ns() {
    return (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now().time_since_epoch()).count();
}
#if defined(__x86_64__)
#include <x86intrin.h>
static inline uint64_t cyc_start() { unsigned lo, hi; __asm__ volatile("cpuid\n\trdtsc" : "=a"(lo), "=d"(hi) : "a"(0) : "rbx", "rcx"); return ((uint64_t)hi << 32) | lo; }
static inline uint64_t cyc_end() { unsigned lo, hi; __asm__ volatile("rdtscp\n\tmov %%edx, %1\n\tmov %%eax, %0\n\tcpuid" : "=r"(lo), "=r"(hi) :: "rax", "rbx", "rcx", "rdx"); return ((uint64_t)hi << 32) | lo; }
static double cycles_per_ns = 0;
static void calibrate() {   // TSC rate, for the bytes/cycle column only
    uint64_t t0 = now_ns(), c0 = cyc_start();
    while (now_ns() - t0 < 200000000ULL) {}
    uint64_t c1 = cyc_end(), t1 = now_ns();
    cycles_per_ns = (double)(c1 - c0) / (double)(t1 - t0);
}
#else
static double cycles_per_ns = 0;
static inline uint64_t cyc_start() { return now_ns(); }
static inline uint64_t cyc_end() { return now_ns(); }
#define INST0 __asm__ volatile("" : "+r"(count)); count++;
#define INST1 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0
#define INST2 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1
__attribute__((noinline)) static void calibrate() {
    const uint64_t N = 1000000000ULL;
    double best = 0;
    for (int rep = 0; rep < 3; rep++) {
        uint64_t count = 0, t0 = now_ns();
        while (count < N) { INST2 }
        uint64_t t1 = now_ns();
        best = std::max(best, (double)count / (double)(t1 - t0));   // adds per ns == cycles per ns
    }
    cycles_per_ns = best;
}
#endif
static inline double to_cycles(uint64_t ticks) {
#if defined(__x86_64__)
    return (double)ticks;
#else
    return (double)ticks * cycles_per_ns;
#endif
}

// ---- functions under test ----
static uint64_t hash_nothing(const void* p, size_t len) { (void)len; return *(const uint8_t*)p; }

template <int BW, int K, int S, int FIN> struct Smh {
    static uintptr_t sp;
    static void init(uint64_t seed) { sp = chg_seed_init<BW, K, FIN>((seed_t)seed); }
    static uint64_t hash(const void* p, size_t len) { uint64_t out; ChainHashG<BW, K, S, FIN, false>(p, len, (seed_t)sp, &out); return out; }
};
template <int BW, int K, int S, int FIN> uintptr_t Smh<BW, K, S, FIN>::sp;
#if defined(__aarch64__)
template <int BW, int K, int S, int FIN> struct Hdr {
    static chainhash_goldi::Key<BW, K, S, FIN> key;
    static void init(uint64_t seed) { key = chainhash_goldi::Key<BW, K, S, FIN>::from_seed(seed); }
    static uint64_t hash(const void* p, size_t len) { return chainhash_goldi::hash(key, p, len); }
};
template <int BW, int K, int S, int FIN> chainhash_goldi::Key<BW, K, S, FIN> Hdr<BW, K, S, FIN>::key;
template <int BW, int K, int S> struct Shp {
    static chainhash::Key<BW, K, S> key;
    static void init(uint64_t seed) { key = chainhash::Key<BW, K, S>::from_seed(seed); }
    static uint64_t hash(const void* p, size_t len) { return chainhash::hash(key, p, len); }
};
template <int BW, int K, int S> chainhash::Key<BW, K, S> Shp<BW, K, S>::key;
#endif

struct Entry { const char* name; void (*init)(uint64_t); HashFn fn; };

__attribute__((noinline)) static uint64_t timehash_small(HashFn hash, uint8_t* key, int len) {
    const uint64_t incr = 0x1000001ULL;
    const uint64_t maxi = incr * (uint64_t)TINY_SAMPLES;
    uint64_t begin = cyc_start();
    for (uint64_t i = 0; i < maxi; i += incr) {
        uint64_t h = hash(key, (size_t)len);
        uint32_t j = (uint32_t)i ^ (uint32_t)h;
        memcpy(key, &j, 4);
    }
    return cyc_end() - begin;
}
__attribute__((noinline)) static uint64_t timehash_bulk(HashFn hash, const uint8_t* buf, size_t len, int reps, uint64_t& sink) {
    uint64_t begin = now_ns();
    for (int i = 0; i < reps; i++) sink += hash(buf, len);
    return now_ns() - begin;
}
static double median(std::vector<double>& v) { std::sort(v.begin(), v.end()); return v[v.size() / 2]; }

int main(int argc, char** argv) {
    if (argc > 1) NTRIALS = atoi(argv[1]);
    calibrate();
    printf("bench_goldi: backend %s, NTRIALS %d, TINY_SAMPLES %d, cycles/ns %.3f (%s)\n", CHG_IMPL_STR, NTRIALS, TINY_SAMPLES, cycles_per_ns,
#if defined(__x86_64__)
           "TSC rate; small-key cycles are TSC ticks via rdtsc/rdtscp as in SMHasher3"
#else
           "dependent-add calibration as in SMHasher3; small-key cycles = ns x this"
#endif
    );
    std::vector<Entry> entries = {
        {"nothing(overhead)", nullptr, hash_nothing},
        {"smh CHAR2-256", Smh<32, 5, 1, CHG_FIN_CHAR2>::init, Smh<32, 5, 1, CHG_FIN_CHAR2>::hash},
        {"smh G4-256", Smh<32, 5, 1, CHG_FIN_G4>::init, Smh<32, 5, 1, CHG_FIN_G4>::hash},
        {"smh G5-256", Smh<32, 5, 1, CHG_FIN_G5>::init, Smh<32, 5, 1, CHG_FIN_G5>::hash},
        {"smh CHAR2-1k", Smh<128, 5, 2, CHG_FIN_CHAR2>::init, Smh<128, 5, 2, CHG_FIN_CHAR2>::hash},
        {"smh G5-1k", Smh<128, 5, 2, CHG_FIN_G5>::init, Smh<128, 5, 2, CHG_FIN_G5>::hash},
#if defined(__aarch64__)
        {"hdr CHAR2-256", Hdr<32, 5, 1, chainhash_goldi::FIN_CHAR2>::init, Hdr<32, 5, 1, chainhash_goldi::FIN_CHAR2>::hash},
        {"hdr G4-256", Hdr<32, 5, 1, chainhash_goldi::FIN_G4>::init, Hdr<32, 5, 1, chainhash_goldi::FIN_G4>::hash},
        {"hdr G5-256", Hdr<32, 5, 1, chainhash_goldi::FIN_G5>::init, Hdr<32, 5, 1, chainhash_goldi::FIN_G5>::hash},
        {"hdr CHAR2-1k", Hdr<128, 5, 2, chainhash_goldi::FIN_CHAR2>::init, Hdr<128, 5, 2, chainhash_goldi::FIN_CHAR2>::hash},
        {"hdr G5-1k", Hdr<128, 5, 2, chainhash_goldi::FIN_G5>::init, Hdr<128, 5, 2, chainhash_goldi::FIN_G5>::hash},
        {"shipped chainhash-256", Shp<32, 5, 1>::init, Shp<32, 5, 1>::hash},
        {"shipped chainhash-1k", Shp<128, 5, 2>::init, Shp<128, 5, 2>::hash},
#endif
    };
    const int lens[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 64};
    const int NL = sizeof(lens) / sizeof(lens[0]);
    alignas(64) static uint8_t key[128];
    alignas(64) static uint8_t bulk[16384];
    uint64_t s = 0x1234567;
    for (size_t i = 0; i < sizeof(bulk); i++) bulk[i] = (uint8_t)chg_splitmix64(s);
    for (size_t i = 0; i < sizeof(key); i++) key[i] = (uint8_t)chg_splitmix64(s);
    uint64_t sink = 0;

    printf("\n== small keys: median cycles/hash (raw, incl. loop overhead) ==\n%-22s", "function");
    for (int l = 0; l < NL; l++) printf(" %5d", lens[l]);
    printf("  | avg1-31\n");
    for (auto& e : entries) {
        if (e.init) e.init(0xC0FFEE);
        double sum = 0;
        printf("%-22s", e.name);
        // warm-up
        for (int w = 0; w < 3; w++) timehash_small(e.fn, key, 16);
        for (int l = 0; l < NL; l++) {
            std::vector<double> t;
            for (int tr = 0; tr < NTRIALS; tr++) t.push_back(to_cycles(timehash_small(e.fn, key, lens[l])) / TINY_SAMPLES);
            double m = median(t);
            if (lens[l] <= 31) sum += m;
            printf(" %5.1f", m);
        }
        printf("  | %6.2f\n", sum / 31.0);
        fflush(stdout);
    }
    printf("\n== bulk: median GB/s (bytes/cycle) ==\n%-22s %14s %14s\n", "function", "16KB", "512B");
    for (auto& e : entries) {
        if (!e.init) continue;
        e.init(0xC0FFEE);
        double r[2];
        const size_t bl[2] = {16384, 512};
        const int reps[2] = {200, 4000};
        for (int b = 0; b < 2; b++) {
            std::vector<double> t;
            for (int w = 0; w < 3; w++) timehash_bulk(e.fn, bulk, bl[b], reps[b], sink);
            for (int tr = 0; tr < NTRIALS; tr++) {
                uint64_t ns = timehash_bulk(e.fn, bulk, bl[b], reps[b], sink);
                t.push_back((double)bl[b] * reps[b] / (double)ns);   // bytes/ns == GB/s
            }
            r[b] = median(t);
        }
        printf("%-22s %6.2f (%5.2f) %6.2f (%5.2f)\n", e.name, r[0], r[0] / cycles_per_ns, r[1], r[1] / cycles_per_ns);
        fflush(stdout);
    }
    printf("(sink %llx)\n", (unsigned long long)sink);
    return 0;
}
