// Isolated finalizer latency: a dependent chain of N evaluations, the state round-tripping through a
// general register each iteration (as in the hash: the chain value leaves a vector register for G4/G5,
// the CHAR2 result leaves it at the end).  cycles = ns x calibrated rate (arm64) / TSC (x86).
// Also: CHAR2 with the state kept in the vector register (no GPR round trip) to price the moves.
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include "chainhash_goldi_exp.cpp"
static inline uint64_t now_ns() { return (uint64_t)std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
#if defined(__x86_64__)
static double rate() { uint64_t t0 = now_ns(); unsigned lo, hi; __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi)); uint64_t c0 = ((uint64_t)hi << 32) | lo; while (now_ns() - t0 < 200000000ULL) {} __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi)); uint64_t c1 = ((uint64_t)hi << 32) | lo; return (double)(c1 - c0) / (double)(now_ns() - t0); }
#else
#define INST0 __asm__ volatile("" : "+r"(count)); count++;
#define INST1 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0 INST0
#define INST2 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1 INST1
__attribute__((noinline)) static double rate() { double best = 0; for (int r = 0; r < 3; r++) { uint64_t count = 0, t0 = now_ns(); while (count < 1000000000ULL) { INST2 } uint64_t t1 = now_ns(); double v = (double)count / (double)(t1 - t0); if (v > best) best = v; } return best; }
#endif
__attribute__((noinline)) uint64_t run_char2(const chg_key<32, 5>* key, uint64_t x, long N) {
    for (long i = 0; i < N; i++) x = chg_fin<CHG_FIN_CHAR2>::apply(key, chg_gf_from(x));   // GPR -> vec, twist + circuit, -> GPR
    return x;
}
__attribute__((noinline)) uint64_t run_char2_vec(const chg_key<32, 5>* key, uint64_t x, long N) {
    chg_gf v = chg_gf_from(x);
    const chg_v128 tin = chg_v_load2(key->tin);
    for (long i = 0; i < N; i++) v = chg_finalize<5>::apply(key->c, chg_v_add64(v, tin));   // state stays in the vector register
    return chg_gf_to(v);
}
__attribute__((noinline)) uint64_t run_g4(const chg_key<32, 5>* key, uint64_t x, long N) {
    for (long i = 0; i < N; i++) x = chg_fin<CHG_FIN_G4>::apply(key, chg_gf_from(x));   // GPR -> vec -> GPR (as in the hash), fold, quartic
    return x;
}
__attribute__((noinline)) uint64_t run_g5(const chg_key<32, 5>* key, uint64_t x, long N) {
    for (long i = 0; i < N; i++) x = chg_fin<CHG_FIN_G5>::apply(key, chg_gf_from(x));
    return x;
}
__attribute__((noinline)) uint64_t run_g4_scalar(const chg_key<32, 5>* key, uint64_t x, long N) {
    for (long i = 0; i < N; i++) x = chg_gl_fin_g4(key->g, key->ng, chg_gl_fold(x));   // no vector round trip
    return x;
}
__attribute__((noinline)) uint64_t run_g5_scalar(const chg_key<32, 5>* key, uint64_t x, long N) {
    for (long i = 0; i < N; i++) x = chg_gl_fin_g5(key->g, key->ng, chg_gl_fold(x));
    return x;
}
__attribute__((noinline)) uint64_t run_mul(const chg_key<32, 5>* key, uint64_t x, long N) {
    for (long i = 0; i < N; i++) x = chg_gl_mul(x, key->g[0]);   // one lazy field multiply (mul + reduce), no fold
    return x;
}
__attribute__((noinline)) uint64_t run_add(const chg_key<32, 5>* key, uint64_t x, long N) {
    for (long i = 0; i < N; i++) x = chg_gl_add_nb(x, key->g[0], key->ng[0]);   // one subtraction-form add
    return x;
}
__attribute__((noinline)) uint64_t run_gfmul(const chg_key<32, 5>* key, uint64_t x, long N) {
    chg_gf v = chg_gf_from(x); const chg_gf c = chg_gf_from(key->c[0]);
    for (long i = 0; i < N; i++) v = chg_gf_mul(v, c);   // one GF(2^64) multiply (PMULL/PCLMUL + 2-fold reduction)
    return chg_gf_to(v);
}
int main(int argc, char** argv) {
    const long N = argc > 1 ? atol(argv[1]) : 20000000L;
    const double cpn = rate();
    const chg_key<32, 5>* k5 = (const chg_key<32, 5>*)chg_seed_init<32, 5, CHG_FIN_G5>(0xC0FFEE);
    printf("fin_latency: backend %s, N %ld, cycles/ns %.3f\n", CHG_IMPL_STR, N, cpn);
    struct { const char* name; uint64_t (*fn)(const chg_key<32, 5>*, uint64_t, long); } tests[] = {
        {"CHAR2 (GPR->vec, twist+circuit, ->GPR)", run_char2}, {"CHAR2 state in vector reg (no moves)", run_char2_vec},
        {"G4 (GPR->vec->GPR, fold, quartic)", run_g4}, {"G5 (GPR->vec->GPR, fold, quintic)", run_g5},
        {"G4 scalar only (fold + quartic)", run_g4_scalar}, {"G5 scalar only (fold + quintic)", run_g5_scalar},
        {"one F_p multiply (lazy)", run_mul}, {"one F_p add (subtraction form)", run_add}, {"one GF(2^64) multiply", run_gfmul}};
    uint64_t sink = 0;
    for (auto& t : tests) {
        double best = 1e30;
        for (int rep = 0; rep < 7; rep++) {
            uint64_t t0 = now_ns(); sink += t.fn(k5, 0x123456789ULL + rep, N); uint64_t t1 = now_ns();
            double c = (double)(t1 - t0) * cpn / (double)N; if (c < best) best = c;
        }
        printf("  %-42s %6.2f cycles/eval (min of 7)\n", t.name, best);
    }
    printf("(sink %llx)\n", (unsigned long long)sink);
    return 0;
}
