// Single-thread throughput for every hash in speed_hashes.h (JSON lines on stdout).
//   selftests first (exit 1 on any mismatch), then each row: median of RUNS timed
//   runs of `reps` calls on one L1-resident random buffer.
// Build: see Makefile target `speed` (C++ TU with -mcpu=native so the framework's
//   PMULL intrinsics compile on Apple clang; UMASH as a separate C TU).
// Run from a directory containing bytes1.bin (framework randomgen.h reads it).
#include "speed_hashes.h"
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <pthread.h>
#include <sys/qos.h>

/* ------------------------------------------------------------------ */
/*  selftests                                                           */
/* ------------------------------------------------------------------ */
static int fails = 0, exact_bad = 0, exact_n = 0;
#define CHECK(cond, ...) do { if (!(cond)) { fails++; fprintf(stderr, "SELFTEST FAIL: "); fprintf(stderr, __VA_ARGS__); fprintf(stderr, "\n"); } } while (0)

static void selftest() {
    Rng r(2024);
    // 1. framework Mersenne primitives vs reference, on the operand ranges the hashes use
    for (int t = 0; t < 200000; t++) {
        u128 a = r.next128() % (3 * M89P);            // < 3p (state + x^2)
        uint64_t x = r.next();
        u128 b = (t & 1) ? (u128)r.next() : (r.next128() >> 40);   // 64-bit word or 88-bit word
        u128 got = fast_large_mult_mod(a, b, x);
        u128 want = (m89_ref_mulmod(a, x) + m89_reduce(b)) % M89P;
        CHECK(m89_reduce(got) == want, "fast_large_mult_mod value t=%d", t);
        CHECK(got < ((u128)1 << 90), "fast_large_mult_mod range t=%d", t);
        u128 a2 = a % (2 * M89P);                       // informational: the framework's _exact variant (not used by any hash here)
        u128 got2 = fast_large_mult_mod_exact(a2, b, x);
        u128 want2 = (m89_ref_mulmod(a2, x) + m89_reduce(b)) % M89P;
        exact_n++; if (m89_reduce(got2) != want2) exact_bad++;
        // extra_large_mult_add_mod: a < 2^90 + 2^89, b < 2^64 + 2^89, d < 2^64
        u128 A = r.next128() % (((u128)3) << 89), B = (r.next128() >> 39) + r.next(), D = r.next();
        u128 got3 = extra_large_mult_add_mod(A, B, D);
        u128 want3 = (m89_ref_mulmod(A, B) + m89_reduce(D)) % M89P;
        CHECK(m89_reduce(got3) == want3, "extra_large_mult_add_mod value t=%d", t);
        CHECK(got3 < ((u128)1 << 90), "extra_large_mult_add_mod range t=%d", t);
    }
    // 2. hashes vs straightforward reference implementations on random messages
    for (int t = 0; t < 300; t++) {
        size_t len = (t < 40) ? (size_t)t : (size_t)(r.next() % 3000);
        std::vector<uint8_t> m(len + 16); for (size_t i = 0; i < len; i++) m[i] = (uint8_t)r.next();
        Rng s1(t + 1), s2(t + 1), s3(t + 1), s4(t + 1), s5(t + 1), s6(t + 1);
        // GF(2^64): NEON-resident three-key recurrence vs a scalar reference built on hashes.h gf64_mul
        // (hashes.h PaperGF64 itself is the single-key recurrence of the adversarial experiments and is left unchanged;
        //  it is the special case (u, y, z) = (x^2, x^3, x), checked in selftest 3 below)
        { PaperGF64Opt h; h.seed(s1); uint64_t P = h.z;
          for (size_t i = 0; i + 16 <= len; i += 16) P = rd64(m.data() + i) ^ gf64_mul(rd64(m.data() + i + 8) ^ h.y, P ^ h.u);
          CHECK(h(m.data(), len) == P, "PaperGF64Opt len=%zu", len); (void)s2; }
        // Mersenne Horner W=8 / W=11 vs reference (exact arithmetic, same word packing)
        { MersHorner89<8> h; h.seed(s3); u128 ref = 0; size_t i = 0;
          for (; i + 8 <= len; i += 8) ref = (m89_ref_mulmod(ref, h.x) + rd64(m.data() + i)) % M89P;
          if (i < len) ref = (m89_ref_mulmod(ref, h.x) + MersHorner89<8>::word(m.data() + i, len - i)) % M89P;
          CHECK(h(m.data(), len) == (uint64_t)ref, "MersHorner89<8> len=%zu", len); }
        { MersHorner89<11> h; h.seed(s3); u128 ref = 0; size_t i = 0;
          for (; i < len; i += 11) ref = (m89_ref_mulmod(ref, h.x) + MersHorner89<11>::word(m.data() + i, std::min<size_t>(11, len - i))) % M89P;
          CHECK(h(m.data(), len) == (uint64_t)ref, "MersHorner89<11> len=%zu", len); }
        // Paper injective over F_{2^89-1}, smart (15-byte) and general (16-byte)
        { PaperMers89Smart h; h.seed(s4); u128 P = h.x; size_t i = 0;
          auto step = [&](uint64_t a, uint64_t b) { P = (m89_ref_mulmod((b + h.y), (P + h.x2)) + a) % M89P; };
          for (; i + 15 <= len; i += 15) { uint64_t b = 0; memcpy(&b, m.data() + i + 8, 7); step(rd64(m.data() + i), b); }
          if (i < len) { uint64_t a = 0, b = 0; size_t n = len - i; if (n >= 8) { a = rd64(m.data() + i); memcpy(&b, m.data() + i + 8, n - 8); } else memcpy(&a, m.data() + i, n); step(a, b); }
          CHECK(h(m.data(), len) == (uint64_t)P, "PaperMers89Smart len=%zu", len); }
        { PaperMers89General h; h.seed(s5); u128 P = h.x;
          for (size_t i = 0; i + 16 <= len; i += 16) P = (m89_ref_mulmod(rd64(m.data() + i + 8) + h.x3, P + h.x2) + rd64(m.data() + i)) % M89P;
          CHECK(h(m.data(), len) == (uint64_t)P, "PaperMers89General len=%zu", len); }
        // lanes variant vs explicit lane reference
        { PaperGF64Lanes<4> h; h.seed(s6); uint64_t P[4] = {h.z, h.z, h.z, h.z}; size_t np = len / 16;
          for (size_t k = 0; k < np; k++) P[k % 4] = rd64(m.data() + 16 * k) ^ gf64_mul(rd64(m.data() + 16 * k + 8) ^ h.y, P[k % 4] ^ h.u);
          uint64_t H = P[3]; for (int j = 2; j >= 0; j--) H = gf64_mul(H, h.w) ^ P[j];
          CHECK(h(m.data(), len) == H, "PaperGF64Lanes<4> len=%zu", len); }
        // system XXH3 vs the hashes.h port on its supported range (9..240)
        if (len >= 9 && len <= 240) { uint64_t sd = r.next(); CHECK(XXH3_64bits_withSeed(m.data(), len, sd) == xxh3_64_ref(m.data(), len, sd), "xxh3 len=%zu", len); }
    }
    // 3. framework univ_injective_64 (single key x) == PaperGF64Opt with (u, y, z) = (x^2, x^3, x) on the interleaved message
    {   const size_t N = 128; FW<univ_injective_64<N>, 2 * N> f; Rng s(99); f.seed(s);
        static_assert(sizeof(f.c) == 2 * N * 8, "univ_injective_64 layout");
        uint64_t w[2 * N]; memcpy(w, &f.c, sizeof w);                    // m_a[0..N-1], m_b[0..N-1]
        std::vector<uint8_t> m(16 * N); for (size_t i = 0; i < N; i++) { wr64(&m[16 * i], w[i]); wr64(&m[16 * i + 8], w[N + i]); }
        uint64_t x2 = gf64_mul(f.x, f.x), x3 = gf64_mul(x2, f.x);
        PaperGF64Opt h; h.set_key(x2, x3, f.x);
        CHECK(f(nullptr, 0) == h(m.data(), m.size()), "univ_injective_64 vs PaperGF64Opt (u,y,z)=(x^2,x^3,x)");
        PaperGF64 g; g.x = f.x; g.x2 = x2; g.x3 = x3;
        CHECK(g(m.data(), m.size()) == h(m.data(), m.size()), "hashes.h PaperGF64 vs PaperGF64Opt (u,y,z)=(x^2,x^3,x)"); }
    // 4. UMASH / komihash: published vectors (vendor selftests reproduce them; here just the README vector)
    {   struct umash_params prm; static const char key[32] = "hello example.c"; umash_params_derive(&prm, 0, key);
        const char* in = "the quick brown fox";
        CHECK(umash_full(&prm, 42, 0, in, strlen(in)) == 0x398c5bb5cc113d03ULL, "umash README vector");
        CHECK(umash_fprint(&prm, 42, in, strlen(in)).hash[1] == 0x3a52693519575abaULL, "umash fprint vector");
        CHECK(komihash("This is a 32-byte testing string", 32, 0) == 0x05ad960802903a9dULL, "komihash README vector"); }
    fprintf(stderr, "info: fast_large_mult_mod_exact mismatches vs reference: %d/%d (not used by any benchmarked hash)\n", exact_bad, exact_n);
    if (fails) { fprintf(stderr, "%d selftest failures\n", fails); exit(1); }
    fprintf(stderr, "selftests passed\n");
}

/* ------------------------------------------------------------------ */
/*  timing                                                              */
/* ------------------------------------------------------------------ */
static int RUNS = 9; static double TARGET = 0.15;
static const char* FILTER = nullptr;   // argv[4]: only time rows whose name contains this substring
template <class H>
static void row(const char* name, size_t BUF, const char* impl, const char* extra = "") {
    if (FILTER && !strstr(name, FILTER)) return;
    std::vector<uint8_t> buf(BUF + 64); Rng r(12345); for (size_t i = 0; i < BUF; i++) buf[i] = (uint8_t)r.next();
    H h; Rng sr(7); h.seed(sr);
    volatile uint64_t sink = 0;
    auto timed = [&](long reps) {
        auto t0 = std::chrono::steady_clock::now();
        for (long i = 0; i < reps; i++) sink ^= h(buf.data(), BUF);
        auto t1 = std::chrono::steady_clock::now();
        return std::chrono::duration<double>(t1 - t0).count();
    };
    long reps = 8; double sec;
    for (;;) { sec = timed(reps); if (sec >= 0.02) break; reps *= 4; }     // warm-up + calibration
    reps = (long)(reps * TARGET / sec) + 1;
    std::vector<double> v;
    for (int k = 0; k < RUNS; k++) v.push_back((double)BUF * reps / timed(reps));
    std::sort(v.begin(), v.end());
    double med = v[RUNS / 2];
    printf("{\"name\":\"%s\",\"size_bytes\":%zu,\"gbps\":%.4f,\"gbps_min\":%.4f,\"gbps_max\":%.4f,\"ns_per_call\":%.2f,\"reps\":%ld,\"runs\":%d,\"impl_source\":\"%s\"%s}\n",
           name, BUF, med / 1e9, v.front() / 1e9, v.back() / 1e9, BUF / med * 1e9, reps, RUNS, impl, extra);
    fflush(stdout);
    (void)sink;
}

int main(int argc, char** argv) {
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);   // bias scheduling to a performance core
    if (argc > 1) RUNS = atoi(argv[1]);
    if (argc > 2) TARGET = atof(argv[2]);
    selftest();
    if (argc > 3 && !strcmp(argv[3], "selftest")) return 0;
    if (argc > 4) FILTER = argv[4];

    const char* H = "tools/bench/adversarial/speed_hashes.h";
    for (size_t BUF : {(size_t)16384, (size_t)512}) {
        row<PaperGF64Opt>("Paper GF(2^64) injective, sequential", BUF, H, ",\"arith\":\"framework/multiplication_arm.h gf64_mult (3x PMULL, r=27); three keys u,y,z\"");
        row<PaperGF64Lanes<2>>("Paper GF(2^64) injective, 2 lanes", BUF, H, ",\"arith\":\"framework gf64_mult; three keys u,y,z; tree-in-w lane combine\"");
        row<PaperGF64Lanes<4>>("Paper GF(2^64) injective, 4 lanes", BUF, H, ",\"arith\":\"framework gf64_mult; three keys u,y,z; tree-in-w lane combine\"");
        row<PaperGF64Lanes<8>>("Paper GF(2^64) injective, 8 lanes", BUF, H, ",\"arith\":\"framework gf64_mult; three keys u,y,z; tree-in-w lane combine\"");
        row<PaperMers89Smart>("Paper injective over F_{2^89-1} (smart reduction, 15 B/step)", BUF, H, ",\"arith\":\"framework/multiplication_arm.h fast_large_mult_mod\"");
        row<PaperMers89General>("Paper injective over F_{2^89-1} (89x89 product, 16 B/step)", BUF, H, ",\"arith\":\"framework/multiplication_arm.h extra_large_mult_add_mod\"");
        row<MersHorner89<8>>("Mersenne 2^89-1 Horner, 8-byte words", BUF, H, ",\"arith\":\"framework/multiplication_arm.h fast_large_mult_mod\"");
        row<MersHorner89<11>>("Mersenne 2^89-1 Horner, 11-byte words", BUF, H, ",\"arith\":\"framework/multiplication_arm.h fast_large_mult_mod\"");
        row<Umash64>("UMASH 64 (umash_full)", BUF, "tools/bench/adversarial/vendor/umash (umash.c via umash_impl.c)");
        row<Umash128>("UMASH 128 (umash_fprint)", BUF, "tools/bench/adversarial/vendor/umash (umash.c via umash_impl.c)");
        row<Wyhash<true>>("wyhash 4.3 (random secret)", BUF, "tools/bench/adversarial/hashes.h Wyhash<true>");
        row<Rapidhash<true>>("rapidhash v1 (random secret)", BUF, "tools/bench/adversarial/hashes.h Rapidhash<true>");
        row<Mum<8>>("MUM v3 (unroll 8)", BUF, "tools/bench/adversarial/hashes.h Mum<8>");
        row<Mum<16>>("MUM v3 (unroll 16)", BUF, "tools/bench/adversarial/hashes.h Mum<16>");
        row<Xxh3Seeded>("XXH3-64 withSeed (random seed)", BUF, "/opt/homebrew/include/xxhash.h 0.8.3 XXH_INLINE_ALL");
        row<Xxh3Secret>("XXH3-64 withSecret (random 192-byte secret)", BUF, "/opt/homebrew/include/xxhash.h 0.8.3 XXH_INLINE_ALL");
        row<Komihash>("komihash 5.34 (random seed)", BUF, "tools/bench/adversarial/vendor/komihash/komihash.h");
        row<Xxh3_128Seeded>("XXH3-128 withSeed (random seed)", BUF, "/opt/homebrew/include/xxhash.h 0.8.3 XXH_INLINE_ALL");
        row<Polymur>("Polymur (random k, s)", BUF, "tools/bench/adversarial/vendor/polymur/polymur-hash.h");
        row<ChainHashRow<8, 5, 1>>("ChainHash, 64 B blocks, K=5+twist", BUF, "tools/bench/chainhash/chainhash.h");
        row<ChainHashRow<32, 5, 1>>("ChainHash, 256 B blocks, K=5+twist", BUF, "tools/bench/chainhash/chainhash.h");
        row<ChainHashRow<128, 5, 2>>("ChainHash, 1 KB blocks, K=5+twist, S=2", BUF, "tools/bench/chainhash/chainhash.h");
        if (BUF == 512) row<VectorMultShift>("Vector multiply-shift (Dietzfelbinger)", BUF, "tools/bench/adversarial/hashes.h VectorMultShift (64-word key cap)");
    }
    // framework universal-hash classes: message stored in the object, key = argument
    const char* FI = "tools/bench/framework/injective_hashing_arm.h";
#define FWR(label, CLS, N, WORDS) row<FW<CLS<N>, WORDS>>(label, (WORDS) * 8, FI, ",\"template\":\"" #CLS "<" #N ">\"")
    // 16384-byte messages
    FWR("univ_injective_64 (single key)", univ_injective_64, 1024, 2048);
    FWR("univ_horner_64", univ_horner_64, 1024, 2048);
    FWR("univ_brw_64", univ_brw_64, 2048, 2048);
    FWR("univ_c2_decbrw_64", univ_c2_decbrw_64, 2048, 2048);
    FWR("univ_c4_decbrw_64", univ_c4_decbrw_64, 2048, 2048);
    FWR("clnh_64", clnh_64, 1024, 2048);
    FWR("horner_unrolled_64", horner_unrolled_64, 2048, 2048);
    FWR("horner_parallel_64", horner_parallel_64, 2048, 2048);
    FWR("univ_injective_parallel_64 (single key)", univ_injective_parallel_64, 1024, 2048);
    // 2048-byte messages
    FWR("univ_injective_64 (single key)", univ_injective_64, 128, 256);
    FWR("univ_horner_64", univ_horner_64, 128, 256);
    FWR("univ_brw_64", univ_brw_64, 256, 256);
    FWR("univ_c2_decbrw_64", univ_c2_decbrw_64, 256, 256);
    FWR("univ_c4_decbrw_64", univ_c4_decbrw_64, 256, 256);
    FWR("clnh_64", clnh_64, 128, 256);
    FWR("horner_unrolled_64", horner_unrolled_64, 256, 256);
    FWR("horner_parallel_64", horner_parallel_64, 256, 256);
    FWR("univ_injective_parallel_64 (single key)", univ_injective_parallel_64, 128, 256);
    // 512-byte messages
    FWR("univ_injective_64 (single key)", univ_injective_64, 32, 64);
    FWR("univ_horner_64", univ_horner_64, 32, 64);
    FWR("univ_brw_64", univ_brw_64, 64, 64);
    FWR("univ_c2_decbrw_64", univ_c2_decbrw_64, 64, 64);
    FWR("univ_c4_decbrw_64", univ_c4_decbrw_64, 64, 64);
    FWR("clnh_64", clnh_64, 32, 64);
    FWR("horner_unrolled_64", horner_unrolled_64, 64, 64);
    FWR("horner_parallel_64", horner_parallel_64, 64, 64);
    FWR("univ_injective_parallel_64 (single key)", univ_injective_parallel_64, 32, 64);
    return 0;
}
