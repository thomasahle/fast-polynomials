/* ***********************************************************************
 * Adversarial collision experiments: proven polynomial hashes vs. heuristic
 * multiply-fold hashes.  See notes/smhasher_adversarial.md for the write-up.
 *
 * Build:  clang++ -O3 -std=c++17 -march=native adversarial.cpp -o adversarial
 * Usage:  ./adversarial <experiment> [threads] [log2trials] [extra...]
 *   random            random-input control: collision rate of random message pairs
 *   scan              32-byte site scan: which single/double word differentials collide
 *   length <kind> <w> collision rate of one differential at several message lengths
 *                     kind in {xorM, addA, addAnegA}; w = comma-separated word indices
 *   determ            deterministic (seed-independent) constructions and blocking sets
 *   all               random + scan + determ
 *
 * All collision probabilities are over the hash's own randomness (seed /
 * key), drawn fresh for every trial; messages are fixed unless stated.
 * ***********************************************************************/
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <string>
#include <vector>
#include <thread>
#include <atomic>
#include <functional>
#include <algorithm>
#include "hashes.h"

static int g_threads = 12;
static int g_log2trials = 30;

/* ------------------------------------------------------------------ */
struct Msg {
    uint8_t b[256]; size_t len;
    uint64_t w(int i) const { return rd64(b + 8 * i); }
    void setw(int i, uint64_t v) { wr64(b + 8 * i, v); }
    int nwords() const { return (int)(len / 8); }
};
static Msg base_msg(size_t len, uint64_t salt = 12345) {
    Msg m; m.len = len; Rng r(salt);
    for (size_t i = 0; i < len; i += 8) wr64(m.b + i, r.next());
    return m;
}
enum DiffKind { XOR_M, ADD_A, ADD_NEG_A };
static const uint64_t ALT = 0x5555555555555555ull;
static void apply(Msg& m, int word, DiffKind k) {
    uint64_t v = m.w(word);
    if (k == XOR_M) v = ~v; else if (k == ADD_A) v += ALT; else v -= ALT;
    m.setw(word, v);
}
static const char* kind_name(DiffKind k) { return k == XOR_M ? "xor M" : k == ADD_A ? "add A" : "add -A"; }

/* ------------------------------------------------------------------ */
/* Trial loops                                                          */
/* ------------------------------------------------------------------ */
template <class H>
static uint64_t count_fixed(const Msg& m1, const Msg& m2, uint64_t trials, uint64_t salt) {
    std::atomic<uint64_t> total{0};
    std::vector<std::thread> th;
    for (int t = 0; t < g_threads; t++)
        th.emplace_back([&, t]() {
            Rng r(salt * 0x9E3779B97F4A7C15ull + 7919 * t + 1);
            H h; uint64_t cnt = 0, per = trials / g_threads;
            for (uint64_t i = 0; i < per; i++) { h.seed(r); cnt += h(m1.b, m1.len) == h(m2.b, m2.len); }
            total += cnt;
        });
    for (auto& x : th) x.join();
    return total;
}
template <class H>
static uint64_t count_random(size_t len, uint64_t trials, uint64_t salt) {
    std::atomic<uint64_t> total{0};
    std::vector<std::thread> th;
    for (int t = 0; t < g_threads; t++)
        th.emplace_back([&, t]() {
            Rng r(salt * 0x9E3779B97F4A7C15ull + 104729 * t + 3);
            H h; Msg m1, m2; m1.len = m2.len = len; uint64_t cnt = 0, per = trials / g_threads;
            for (uint64_t i = 0; i < per; i++) {
                for (size_t j = 0; j < len; j += 8) { wr64(m1.b + j, r.next()); wr64(m2.b + j, r.next()); }
                h.seed(r); cnt += h(m1.b, len) == h(m2.b, len);
            }
            total += cnt;
        });
    for (auto& x : th) x.join();
    return total;
}

static std::string rate_str(uint64_t hits, uint64_t trials) {
    char buf[96];
    if (!hits) snprintf(buf, sizeof buf, "0 / 2^%.0f", log2((double)trials));
    else snprintf(buf, sizeof buf, "%llu / 2^%.0f = 2^%.1f", (unsigned long long)hits, log2((double)trials), log2((double)hits / trials));
    return buf;
}

/* ------------------------------------------------------------------ */
/* Hash registry                                                        */
/* ------------------------------------------------------------------ */
#define PROVEN_HASHES(X) X(PaperGF64) X(PaperMersenne) X(VectorMultShift)
#define HEURISTIC_HASHES(X) X(PaperMumXor) X(PaperMumAdd) X(Wyhash<false>) X(Wyhash<true>) X(Rapidhash<false>) X(Rapidhash<true>) X(Mum<8>) X(Mum<16>) X(Xxh3<false>) X(Xxh3<true>)
#define ALL_HASHES(X) PROVEN_HASHES(X) HEURISTIC_HASHES(X)
template <class H> static constexpr bool is_proven() {
    return std::is_same<H, PaperGF64>::value || std::is_same<H, PaperMersenne>::value || std::is_same<H, VectorMultShift>::value;
}

static bool name_selected(const char* name, const std::vector<std::string>& filt) {
    if (filt.empty()) return true;
    for (auto& f : filt) if (strstr(name, f.c_str())) return true;
    return false;
}

/* ================================================================== */
/* E0: random inputs                                                    */
/* ================================================================== */
static void exp_random() {
    printf("\n## Random-input control\n\nTwo uniformly random messages of the given length and a fresh random seed/key per trial.\n\n");
    printf("| hash | len (bytes) | collisions / trials |\n|---|---|---|\n");
    size_t lens[] = {32, 160};
#define X(H) for (size_t len : lens) { uint64_t tr = 1ull << (is_proven<H>() ? g_log2trials - 2 : g_log2trials); \
        uint64_t c = count_random<H>(len, tr, 11 + len); printf("| %s | %zu | %s |\n", H::name, len, rate_str(c, tr).c_str()); fflush(stdout); }
    ALL_HASHES(X)
#undef X
}

/* ================================================================== */
/* E1: site scan at 32 bytes                                            */
/* ================================================================== */
struct Site { DiffKind k[2]; int w[2]; int n; };
static std::string site_name(const Site& s) {
    std::string r;
    for (int i = 0; i < s.n; i++) { if (i) r += " & "; r += "w" + std::to_string(s.w[i]) + " " + kind_name(s.k[i]); }
    return r;
}
static void make_pair(const Msg& base, const Site& s, Msg& m1, Msg& m2) {
    m1 = base; m2 = base; for (int i = 0; i < s.n; i++) apply(m2, s.w[i], s.k[i]);
}

static void exp_scan() {
    const size_t len = 32;
    Msg base = base_msg(len);
    std::vector<Site> sites;
    for (int j = 0; j < 4; j++) sites.push_back({{XOR_M, XOR_M}, {j, 0}, 1});
    for (int j = 0; j < 3; j++) sites.push_back({{XOR_M, XOR_M}, {j, j + 1}, 2});
    sites.push_back({{XOR_M, XOR_M}, {0, 3}, 2});
    for (int j = 0; j < 4; j++) sites.push_back({{ADD_A, ADD_A}, {j, 0}, 1});
    sites.push_back({{ADD_A, ADD_A}, {0, 3}, 2});
    sites.push_back({{ADD_A, ADD_NEG_A}, {0, 3}, 2});
    sites.push_back({{ADD_A, ADD_A}, {0, 1}, 2});

    printf("\n## Differential site scan, 32-byte messages (4 words w0..w3)\n\n");
    printf("Base message: fixed pseudo-random 32 bytes.  The second message applies the listed differential(s):\n");
    printf("'xor M' complements the word (XOR with 2^64-1); 'add A' adds 0x5555...5 mod 2^64; 'add -A' subtracts it.\n");
    printf("For the paper's recurrence the words are (a1,b1,a2,b2) = (w0,w1,w2,w3); the step-2 multiplication\n");
    printf("has multiplicands (b2 + x^3) and (P1 + x^2) with P1 = a1 + ..., so the pair (w0,w3) is its (delta,eps) site.\n");
    printf("Entries: collisions / trials over random seeds (random secret where applicable).\n\n");

    std::vector<std::string> hnames; std::vector<std::vector<std::string>> cells(sites.size());
#define X(H) { hnames.push_back(H::name); uint64_t tr = 1ull << (is_proven<H>() ? g_log2trials - 2 : g_log2trials); \
        for (size_t si = 0; si < sites.size(); si++) { Msg m1, m2; make_pair(base, sites[si], m1, m2); \
            uint64_t c = count_fixed<H>(m1, m2, tr, 1000 + si); cells[si].push_back(rate_str(c, tr)); } \
        fprintf(stderr, "scan: %s done\n", H::name); }
    ALL_HASHES(X)
#undef X
    printf("| site |"); for (auto& n : hnames) printf(" %s |", n.c_str()); printf("\n|---|"); for (size_t i = 0; i < hnames.size(); i++) printf("---|"); printf("\n");
    for (size_t si = 0; si < sites.size(); si++) {
        printf("| %s |", site_name(sites[si]).c_str());
        for (auto& c : cells[si]) printf(" %s |", c.c_str());
        printf("\n");
    }
    fflush(stdout);
}

/* ================================================================== */
/* E3: one differential at several lengths                              */
/* ================================================================== */
// one differential, one length, high trial count (precision run)
static void exp_pair(const Site& s, size_t len, const std::vector<std::string>& filt) {
    Msg base = base_msg(len), m1, m2; make_pair(base, s, m1, m2);
    printf("\n## Differential '%s' at %zu bytes (precision run)\n\n| hash | collisions / trials |\n|---|---|\n", site_name(s).c_str(), len);
#define X(H) if (name_selected(H::name, filt)) { uint64_t tr = 1ull << (is_proven<H>() ? g_log2trials - 2 : g_log2trials); \
        uint64_t c = count_fixed<H>(m1, m2, tr, 9000 + len); printf("| %s | %s |\n", H::name, rate_str(c, tr).c_str()); fflush(stdout); }
    ALL_HASHES(X)
#undef X
}

static void exp_length(const Site& s, const std::vector<std::string>& filt) {
    size_t lens[] = {32, 48, 64, 96, 160};
    printf("\n## Differential '%s' at several message lengths\n\n", site_name(s).c_str());
    printf("| hash | 32 B | 48 B | 64 B | 96 B | 160 B |\n|---|---|---|---|---|---|\n");
#define X(H) if (name_selected(H::name, filt)) { printf("| %s |", H::name); \
        uint64_t tr = 1ull << (is_proven<H>() ? g_log2trials - 2 : g_log2trials); \
        for (size_t len : lens) { Msg base = base_msg(len), m1, m2; make_pair(base, s, m1, m2); \
            uint64_t c = count_fixed<H>(m1, m2, tr, 5000 + len); printf(" %s |", rate_str(c, tr).c_str()); fflush(stdout); } \
        printf("\n"); }
    ALL_HASHES(X)
#undef X
}

/* ================================================================== */
/* E2: deterministic constructions                                      */
/* ================================================================== */
// Report a fixed pair on every hash (heuristic hashes at 2^20 seeds, proven at 2^lt-4).
static void report_pair(const char* title, const Msg& m1, const Msg& m2, const std::vector<std::string>& filt, int lt_heur = 20) {
    printf("\n**%s** (len %zu)\n\n| hash | collisions / trials |\n|---|---|\n", title, m1.len);
#define X(H) if (name_selected(H::name, filt)) { uint64_t tr = 1ull << (is_proven<H>() ? std::max(lt_heur, g_log2trials - 4) : lt_heur); \
        uint64_t c = count_fixed<H>(m1, m2, tr, 777); printf("| %s | %s |\n", H::name, rate_str(c, tr).c_str()); fflush(stdout); }
    ALL_HASHES(X)
#undef X
}

// Brent's cycle finding on f(w) = mum_add(w, p): returns w1 != w2 with f(w1) == f(w2).
static bool rho_collision(uint64_t p, uint64_t start, uint64_t& w1, uint64_t& w2, uint64_t& steps) {
    auto f = [p](uint64_t w) { return mum_add(w, p); };
    uint64_t power = 1, lam = 1, tortoise = start, hare = f(start); steps = 1;
    while (tortoise != hare) {
        if (power == lam) { tortoise = hare; power *= 2; lam = 0; }
        hare = f(hare); lam++; steps++;
    }
    tortoise = hare = start;
    for (uint64_t i = 0; i < lam; i++) hare = f(hare);
    steps += lam;
    uint64_t mu = 0, pt = 0, ph = 0;
    while (tortoise != hare) { pt = tortoise; ph = hare; tortoise = f(tortoise); hare = f(hare); mu++; steps += 2; }
    if (mu == 0) return false;
    w1 = pt; w2 = ph; return true;
}

// blocking-set check: K messages, over S seeds: fraction of pairs that collide (all seeds)
template <class H>
static void blocking_set(const char* title, const std::vector<Msg>& ms, int log2seeds) {
    uint64_t S = 1ull << log2seeds, K = ms.size(), pairs = K * (K - 1) / 2;
    uint64_t per = S / g_threads, seeds = per * (uint64_t)g_threads;   // actual seeds run (denominator)
    std::atomic<uint64_t> coll{0};
    std::vector<std::thread> th;
    for (int t = 0; t < g_threads; t++)
        th.emplace_back([&, t]() {
            Rng r(31337 + t); H h; uint64_t c = 0; std::vector<uint64_t> hv(K);
            for (uint64_t s = 0; s < per; s++) {
                h.seed(r);
                for (uint64_t i = 0; i < K; i++) hv[i] = h(ms[i].b, ms[i].len);
                std::sort(hv.begin(), hv.end());
                for (uint64_t i = 0, j; i < K; i = j) { j = i; while (j < K && hv[j] == hv[i]) j++; c += (j - i) * (j - i - 1) / 2; }
            }
            coll += c;
        });
    for (auto& x : th) x.join();
    printf("| %s | %s | %llu | %llu | %.6f |\n", title, H::name, (unsigned long long)K, (unsigned long long)seeds, (double)coll / (double)(pairs * seeds));
    fflush(stdout);
}

static void exp_determ() {
    std::vector<std::string> all;
    printf("\n## Deterministic (seed-independent) constructions\n\n");
    printf("Each construction exploits PUBLIC constants (default secret / primes) or seed-independent combining.\n");
    printf("Collision counts are over random seeds; a rate of 1 means the pair collides for every seed.\n");

    // ---- wyhash / rapidhash: word at offset len-16 equal to secret[1]
    {
        Msg m1 = base_msg(32, 1), m2 = base_msg(32, 2);   // two unrelated random messages
        m1.setw(2, WYHASH_SECRET_DEFAULT[1]); m2.setw(2, WYHASH_SECRET_DEFAULT[1]);
        report_pair("wyhash/rapidhash: two otherwise-random 32-byte messages whose word at offset len-16 equals secret[1] = 0x8bb84b93962eacc9 (final a^secret[1] = 0 annihilates the last multiplication)", m1, m2, all);
        Msg l1 = base_msg(160, 3), l2 = base_msg(160, 4);
        l1.setw(18, WYHASH_SECRET_DEFAULT[1]); l2.setw(18, WYHASH_SECRET_DEFAULT[1]);
        report_pair("same at 160 bytes (three-lane path): word at offset 144 equals secret[1]", l1, l2, all);
        Msg a1 = base_msg(32, 5), a2 = a1; a1.setw(0, WYHASH_SECRET_DEFAULT[1]); a2.setw(0, WYHASH_SECRET_DEFAULT[1]); a2.setw(1, ~a1.w(1));
        report_pair("wyhash: w0 = secret[1] zeroes the block state (_wymix(0, .) = 0); messages differ only in w1", a1, a2, all);
        Msg r1 = base_msg(32, 6), r2 = r1; r1.setw(0, RAPID_SECRET_DEFAULT[2]); r2.setw(0, RAPID_SECRET_DEFAULT[2]); r2.setw(1, ~r1.w(1));
        report_pair("rapidhash: w0 = secret[2] zeroes the block state; messages differ only in w1", r1, r2, all);
    }
    // ---- XXH3 with seed 0: w0 equal to the first secret word
    {
        Msg m1 = base_msg(32, 7), m2 = m1; uint64_t s0 = rd64(XXH3_KSECRET);
        m1.setw(0, s0); m2.setw(0, s0); m2.setw(1, ~m1.w(1));
        report_pair("XXH3: w0 = kSecret[0..8] = 0xbe4ba423396cfeb8 makes mix16B(chunk 0) = 0 for seed 0; messages differ only in w1", m1, m2, all);
    }
    // ---- MUM: rho collision on a single-word term (short-message path)
    {
        uint64_t p = MUM_PRIMES[1], w1, w2, steps = 0, start = 1;
        // Cached pair from a previous Brent rho run (found at ~2^37 evaluations);
        // set env ADV_RHO=search to re-run the search from scratch (~minutes).
        const char* rho = getenv("ADV_RHO");
        if (rho && std::string(rho) == "search") {
            while (!rho_collision(p, start, w1, w2, steps)) start++;
            printf("\nMUM single-word term: Brent rho on f(w) = _mum(w, primes[1]) found w=%016llx, w'=%016llx with f(w)=f(w')=%016llx after %.2e evaluations (~2^%.1f).\n",
                   (unsigned long long)w1, (unsigned long long)w2, (unsigned long long)mum_add(w1, p), (double)steps, log2((double)steps));
        } else {
            w1 = 0x0a3c39b967d06be6ull; w2 = 0xf3c66c5c0a025090ull;   // cached; verified below
            printf("\nMUM single-word term: cached Brent-rho collision on f(w) = _mum(w, primes[1]) (found at ~2^37 evaluations; ADV_RHO=search to reproduce): w=%016llx, w'=%016llx, f(w)=%016llx, f(w')=%016llx %s.\n",
                   (unsigned long long)w1, (unsigned long long)w2, (unsigned long long)mum_add(w1, p), (unsigned long long)mum_add(w2, p),
                   mum_add(w1, p) == mum_add(w2, p) ? "(equal, verified)" : "(MISMATCH!)");
        }
        Msg m1 = base_msg(32, 8), m2 = m1; m1.setw(1, w1); m2.setw(1, w2);
        report_pair("MUM: 32-byte messages differing only in w1 by the rho-found pair (term _mum(w1, primes[1]) identical)", m1, m2, all);
        // paired path: complement both words of a pair (P = 2/3 over base messages, seed-independent)
        {
            Rng r(99); uint64_t coll = 0, N = 1 << 16;
            for (uint64_t i = 0; i < N; i++) { uint64_t a = r.next(), b = r.next();
                coll += mum_add(_mum_xor(a, MUM_PRIMES[0]), _mum_xor(b, MUM_PRIMES[1])) == mum_add(_mum_xor(~a, MUM_PRIMES[0]), _mum_xor(~b, MUM_PRIMES[1])); }
            printf("\nMUM paired-word term (len > 8*UNROLL bytes): complementing both words of a pair leaves _mum(w0^p0, w1^p1) unchanged for %llu / %llu = %.4f random word pairs (deterministic: each pair either always or never collides).\n",
                   (unsigned long long)coll, (unsigned long long)N, (double)coll / N);
            Msg b = base_msg(160, 9); Msg c = b; apply(c, 0, XOR_M); apply(c, 1, XOR_M);
            // pick a base for which the pair collides
            for (uint64_t salt = 9; ; salt++) { b = base_msg(160, salt); c = b; apply(c, 0, XOR_M); apply(c, 1, XOR_M);
                if (mum_add(_mum_xor(b.w(0), MUM_PRIMES[0]), _mum_xor(b.w(1), MUM_PRIMES[1])) == mum_add(_mum_xor(c.w(0), MUM_PRIMES[0]), _mum_xor(c.w(1), MUM_PRIMES[1]))) break; }
            report_pair("MUM: 160-byte messages with (w0,w1) complemented (a base for which the pair term coincides; unroll 16 uses the paired path only for len > 128, unroll 8 for len > 64)", b, c, all);
        }
    }
    // ---- blocking sets
    printf("\n### Blocking sets: K messages, fraction of the K(K-1)/2 pairs that collide, averaged over S seeds\n\n");
    printf("| construction | hash | K | S | colliding-pair fraction |\n|---|---|---|---|---|\n");
    {
        std::vector<Msg> ms; for (int i = 0; i < 256; i++) { Msg m = base_msg(32, 10000 + i); m.setw(2, WYHASH_SECRET_DEFAULT[1]); ms.push_back(m); }
        blocking_set<Wyhash<false>>("32-byte, w2 = secret[1], rest random", ms, 10);
        blocking_set<Wyhash<true>>("32-byte, w2 = secret[1], rest random", ms, 10);
        blocking_set<Rapidhash<false>>("32-byte, w2 = secret[1], rest random", ms, 10);
        blocking_set<Rapidhash<true>>("32-byte, w2 = secret[1], rest random", ms, 10);
        blocking_set<PaperGF64>("32-byte, w2 = secret[1], rest random", ms, 10);
        blocking_set<PaperMersenne>("32-byte, w2 = secret[1], rest random", ms, 10);
        blocking_set<VectorMultShift>("32-byte, w2 = secret[1], rest random", ms, 10);
    }
    {
        // seed-0 clique: w0 = kSecret[0..8] makes mix16B(chunk 0) = 0 regardless of w1;
        // fixing (w2,w3) too, all messages that vary only in w1 share the same accumulator.
        std::vector<Msg> ms; uint64_t s0 = rd64(XXH3_KSECRET); Msg proto = base_msg(32, 20000);
        for (int i = 0; i < 256; i++) { Msg m = proto; m.setw(0, s0); m.setw(1, 0x1000 + (uint64_t)i * 0x9E3779B97F4A7C15ull); ms.push_back(m); }
        blocking_set<Xxh3<false>>("32-byte, w0 = kSecret[0..8], w2,w3 fixed, vary w1", ms, 10);
        blocking_set<Xxh3<true>>("32-byte, w0 = kSecret[0..8], w2,w3 fixed, vary w1", ms, 10);
        blocking_set<PaperGF64>("32-byte, w0 = kSecret[0..8], w2,w3 fixed, vary w1", ms, 10);
    }
    {
        // MUM rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1 => term = rotl(rotr(Q,k),k) = Q for all k
        std::vector<Msg> ms; Msg b = base_msg(160, 30000); uint64_t Q = 0x0123456789abcdefull;
        for (int k = 0; k < 64; k++) { Msg m = b; m.setw(0, MUM_PRIMES[0] ^ (1ull << k)); m.setw(1, ((Q >> k) | (Q << ((64 - k) & 63))) ^ MUM_PRIMES[1]); if (k == 0) m.setw(1, Q ^ MUM_PRIMES[1]); ms.push_back(m); }
        blocking_set<Mum<8>>("160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63", ms, 10);
        blocking_set<Mum<16>>("160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63", ms, 10);
        blocking_set<PaperGF64>("160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63", ms, 10);
        blocking_set<PaperMersenne>("160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63", ms, 10);
        blocking_set<VectorMultShift>("160-byte rotation clique: w0 = p0 ^ 2^k, w1 = rotr(Q,k) ^ p1, k=0..63", ms, 10);
    }
    {
        // a random blocking set (control): 256 random 32-byte messages
        std::vector<Msg> ms; for (int i = 0; i < 256; i++) ms.push_back(base_msg(32, 40000 + i));
        blocking_set<Wyhash<false>>("control: 256 random 32-byte messages", ms, 10);
        blocking_set<Mum<8>>("control: 256 random 32-byte messages", ms, 10);
        blocking_set<PaperGF64>("control: 256 random 32-byte messages", ms, 10);
    }
}

/* ================================================================== */
int main(int argc, char** argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s random|scan|length|determ|all [threads] [log2trials] [kind words] [hashfilter...]\n", argv[0]); return 1; }
    std::string e = argv[1];
    if (argc > 2) g_threads = atoi(argv[2]);
    if (argc > 3) g_log2trials = atoi(argv[3]);
    printf("# adversarial experiments: %s (threads=%d, log2 trials=%d for heuristic hashes, %d for proven ones)\n", e.c_str(), g_threads, g_log2trials, g_log2trials - 2);
    if (e == "random" || e == "all") exp_random();
    if (e == "scan" || e == "all") exp_scan();
    if (e == "determ" || e == "all") exp_determ();
    if (e == "length" || e == "pair") {
        if (argc < 6) { fprintf(stderr, "length needs: threads log2trials kind words [hashfilter...]; pair needs: threads log2trials kind words len [hashfilter...]\n"); return 1; }
        std::string kind = argv[4]; std::string ws = argv[5];
        Site s; s.n = 0;
        DiffKind k0 = kind == "xorM" ? XOR_M : ADD_A, k1 = kind == "addAnegA" ? ADD_NEG_A : k0;
        for (size_t pos = 0; pos < ws.size() && s.n < 2;) { size_t nx = ws.find(',', pos); std::string tok = ws.substr(pos, nx == std::string::npos ? std::string::npos : nx - pos);
            s.w[s.n] = atoi(tok.c_str()); s.k[s.n] = s.n == 0 ? k0 : k1; s.n++; if (nx == std::string::npos) break; pos = nx + 1; }
        int first = e == "pair" ? 7 : 6;
        std::vector<std::string> filt; for (int i = first; i < argc; i++) filt.push_back(argv[i]);
        if (e == "pair") exp_pair(s, (size_t)atoi(argv[6]), filt); else exp_length(s, filt);
    }
    return 0;
}
