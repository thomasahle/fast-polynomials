/* Tests for ChainHash (tools/bench/chainhash/chainhash.h) against the bit-serial
 * reference (chainhash_ref.h).  No benchmarking here.
 *
 *  Grid (K = 5 is the only shipped finalizer): the shipped configurations
 *  (32,5,1) = chainhash-256 and (128,5,2) = chainhash-1k, the 64-byte-block
 *  (8,5,1), and the remaining splits (32,5,2), (32,5,4), (128,5,1), (128,5,4).
 *
 *  Length set L (394 lengths, built once at startup): all of 0..200,
 *  1000..1100, 2030..2070, 4080..4110, plus 20 seeded-random lengths in
 *  4111..70000.  The fixed ranges hit every length residue mod 16 and mod 64
 *  (every partial-pair / whole-pair / 64-byte-group combination of the last
 *  block, and every last-block size for BLOCK_WORDS = 8) and cross the
 *  1024/2048/4096-byte boundaries byte by byte.  Last-block sizes 201..231
 *  (BLOCK_WORDS = 32) and 201..999 (BLOCK_WORDS = 128) are reached only by
 *  the random lengths.  For S > 1 the ranges 0..200 (sub-blocks of 64 and
 *  128 bytes at BLOCK_WORDS = 32) and 1000..1100 / 2030..2070 (sub-blocks
 *  of 256 and 512 bytes at BLOCK_WORDS = 128) cross sub-block boundaries
 *  byte by byte.
 *
 *  T1  fast == reference: for every grid point, 50 random keys x EVERY
 *      length in L (one random message per (key,len)), random pointer
 *      misalignment 0..15, exact-size heap allocations.
 *  T2  determinism (key derivation and hashing), fast key == reference key
 *      (k[], u, y, z, c[], t_in).
 *  T3  length sensitivity: m, m||0, m||00 pairwise distinct (incl. empty m).
 *  T4  no over-/under-read: (a) whole binary under ASAN when built with it,
 *      (b) mprotect guard page directly AFTER every message in L, and
 *          directly BEFORE it (message at the start of the mapping), for
 *          every grid point; fast == reference on each.
 *      (c) Guard Malloc run from build.sh.
 *  T5  chain == explicit monic degree-5 polynomial (symbolic expansion of
 *      the transcribed circuit + Horner, fast == ref == Horner), leading
 *      coeff 1; the coefficient map c[0..5) -> lower coefficients is a
 *      bijection, shown by the EXPLICIT decoder (verify5.py / the paper's
 *      eq:ph:chain5-decoder: unit pivots only in the coordinates
 *      q = (c2, c0+c1, c0, c3, c4), no square roots), cross-checked against
 *      the generic top-down pivot loop of website/js/char2.js
 *      (decodeUnitriangular with KEYS_FROM_Q[5], all root depths 0):
 *      decode(encode(c)) == c and encode(decode(p)) == p for random c and
 *      random monic p; and the twist: finalize(key, v) == Horner(p, v + t_in)
 *      with v + t_in the 64-bit integer sum (fast NEON add == ref scalar add,
 *      including carry-wrapping edge values).
 *  T6  1,000,000 random distinct short message pairs (1..64 B), zero
 *      collisions; plus 1,000,000 distinct messages (4..64 B), all distinct.
 *      Run at BLOCK_WORDS = 8 (one full 64-byte block or a pure tail) and 128.
 *  T7  gf64 multiply fast vs bit-serial reference (1e5 random + edge cases).
 */

#include <sys/mman.h>
#include <unistd.h>

#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <vector>

#include "chainhash.h"
#include "chainhash_ref.h"

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define HAVE_ASAN 1
#endif
#endif
#ifndef HAVE_ASAN
#define HAVE_ASAN 0
#endif

static long g_checks = 0, g_fail = 0;
#define CHECK(cond, ...)                                          \
    do {                                                          \
        g_checks++;                                               \
        if (!(cond)) {                                            \
            g_fail++;                                             \
            if (g_fail <= 20) {                                   \
                std::printf("FAIL %s:%d: ", __FILE__, __LINE__);  \
                std::printf(__VA_ARGS__);                         \
                std::printf("\n");                                \
            }                                                     \
        }                                                         \
    } while (0)

static std::mt19937_64 rng(0x5EED5EEDULL);

/* The length set L: fixed ranges + 20 seeded-random lengths (deterministic). */
static std::vector<size_t> g_lengths;
static const int N_RANDOM_LENGTHS = 20;
static const size_t MAX_RANDOM_LENGTH = 70000;
static void build_lengths() {
    g_lengths.clear();
    for (size_t l = 0; l <= 200; l++) g_lengths.push_back(l);
    for (size_t l = 1000; l <= 1100; l++) g_lengths.push_back(l);
    for (size_t l = 2030; l <= 2070; l++) g_lengths.push_back(l);
    for (size_t l = 4080; l <= 4110; l++) g_lengths.push_back(l);
    for (int i = 0; i < N_RANDOM_LENGTHS; i++)  // 4111..70000: outside the fixed ranges
        g_lengths.push_back(4111 + (size_t)(rng() % (MAX_RANDOM_LENGTH - 4111 + 1)));
}
static size_t random_length() { return g_lengths[rng() % g_lengths.size()]; }

static void fill_random(uint8_t* p, size_t n) {
    for (size_t i = 0; i < n; i++) p[i] = (uint8_t)rng();
}

/* exact-size heap buffer (ASAN redzones start right after len+off bytes) */
struct ExactBuf {
    uint8_t* base;
    size_t total;
    ExactBuf(size_t n) : base(new uint8_t[n]), total(n) {}
    ~ExactBuf() { delete[] base; }
    ExactBuf(const ExactBuf&) = delete;
    ExactBuf& operator=(const ExactBuf&) = delete;
};

/* ------------------------------------------------------------------ */
/* T1: fast == reference, every length in L for every key              */
/* ------------------------------------------------------------------ */
template <int BW, int K, int S>
static long test_fast_vs_ref(int n_keys) {
    using FKey = chainhash::Key<BW, K, S>;
    using RKey = chainhash_ref::Key<BW, K, S>;
    long count = 0;
    for (int ki = 0; ki < n_keys; ki++) {
        uint64_t seed = rng();
        FKey fk = FKey::from_seed(seed);
        RKey rk = RKey::from_seed(seed);
        for (size_t li = 0; li < g_lengths.size(); li++) {
            size_t len = g_lengths[li];
            size_t off = rng() % 16;
            ExactBuf buf(len + off);
            fill_random(buf.base, len + off);
            const uint8_t* m = buf.base + off;
            uint64_t hf = chainhash::hash(fk, m, len);
            uint64_t hr = chainhash_ref::hash(rk, m, len);
            CHECK(hf == hr, "BW=%d K=%d S=%d key %d len %zu off %zu: fast %016llx ref %016llx", BW, K, S, ki, len,
                  off, (unsigned long long)hf, (unsigned long long)hr);
            count++;
        }
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* T2: determinism                                                     */
/* ------------------------------------------------------------------ */
template <int BW, int K, int S>
static long test_determinism(int n_seeds) {
    using FKey = chainhash::Key<BW, K, S>;
    using RKey = chainhash_ref::Key<BW, K, S>;
    long count = 0;
    for (int i = 0; i < n_seeds; i++) {
        uint64_t seed = rng();
        FKey a = FKey::from_seed(seed), b = FKey::from_seed(seed);
        RKey r = RKey::from_seed(seed);
        CHECK(std::memcmp(a.k, b.k, sizeof(a.k)) == 0 && a.u == b.u && a.y == b.y && a.z == b.z &&
                  std::memcmp(a.c, b.c, sizeof(a.c)) == 0 && a.t_in == b.t_in,
              "BW=%d K=%d S=%d key derivation not deterministic (seed %llx)", BW, K, S, (unsigned long long)seed);
        CHECK(std::memcmp(a.k, r.k, sizeof(a.k)) == 0 && a.u == r.u && a.y == r.y && a.z == r.z &&
                  std::memcmp(a.c, r.c, sizeof(a.c)) == 0 && a.t_in == r.t_in,
              "BW=%d K=%d S=%d fast key != reference key (seed %llx)", BW, K, S, (unsigned long long)seed);
        size_t len = random_length();
        ExactBuf buf(len);
        fill_random(buf.base, len);
        uint64_t h1 = chainhash::hash(a, buf.base, len);
        uint64_t h2 = chainhash::hash(b, buf.base, len);
        std::vector<uint8_t> copy(buf.base, buf.base + len);
        uint64_t h3 = chainhash::hash(a, copy.data(), len);
        CHECK(h1 == h2 && h1 == h3, "BW=%d K=%d S=%d hash not deterministic (seed %llx len %zu)", BW, K, S,
              (unsigned long long)seed, len);
        count++;
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* T3: length sensitivity                                              */
/* ------------------------------------------------------------------ */
template <int BW, int K, int S>
static long test_length_sensitivity(int n_keys, int msgs_per_key) {
    using FKey = chainhash::Key<BW, K, S>;
    long count = 0;
    for (int ki = 0; ki < n_keys; ki++) {
        FKey fk = FKey::from_seed(rng());
        for (int mi = 0; mi < msgs_per_key; mi++) {
            size_t len;
            if (mi == 0) len = 0;  // empty message
            else if (mi == 1) len = random_length();
            else len = rng() % 3000;
            std::vector<uint8_t> m(len + 2, 0);
            fill_random(m.data(), len);
            m[len] = 0;
            m[len + 1] = 0;
            uint64_t h0 = chainhash::hash(fk, m.data(), len);
            uint64_t h1 = chainhash::hash(fk, m.data(), len + 1);
            uint64_t h2 = chainhash::hash(fk, m.data(), len + 2);
            CHECK(h0 != h1, "BW=%d K=%d S=%d len %zu: h(m) == h(m||0)", BW, K, S, len);
            CHECK(h0 != h2, "BW=%d K=%d S=%d len %zu: h(m) == h(m||00)", BW, K, S, len);
            CHECK(h1 != h2, "BW=%d K=%d S=%d len %zu: h(m||0) == h(m||00)", BW, K, S, len);
            count++;
        }
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* T4b: guard pages directly after and before the message              */
/* ------------------------------------------------------------------ */
template <int BW, int K, int S>
static long test_guard_page() {
    using FKey = chainhash::Key<BW, K, S>;
    using RKey = chainhash_ref::Key<BW, K, S>;
    long count = 0;
    const size_t page = (size_t)sysconf(_SC_PAGESIZE);
    uint64_t seed = rng();
    FKey fk = FKey::from_seed(seed);
    RKey rk = RKey::from_seed(seed);
    for (size_t li = 0; li < g_lengths.size(); li++) {
        size_t len = g_lengths[li];
        size_t data_pages = (len + page - 1) / page + 1;  // >= 1 page of data
        size_t total = (data_pages + 2) * page;           // [guard][data pages][guard]
        uint8_t* region = (uint8_t*)mmap(nullptr, total, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        CHECK(region != MAP_FAILED, "mmap failed");
        if (region == MAP_FAILED) continue;
        uint8_t* lead = region;
        uint8_t* data = region + page;
        uint8_t* guard = region + (data_pages + 1) * page;
        CHECK(mprotect(lead, page, PROT_NONE) == 0, "mprotect (leading) failed");
        CHECK(mprotect(guard, page, PROT_NONE) == 0, "mprotect (trailing) failed");

        // (i) message ends exactly at the trailing guard page
        uint8_t* m = guard - len;
        fill_random(m, len);
        uint64_t hf = chainhash::hash(fk, m, len);
        uint64_t hr = chainhash_ref::hash(rk, m, len);
        CHECK(hf == hr, "guard-page(after) BW=%d K=%d S=%d len %zu: fast %016llx ref %016llx", BW, K, S, len,
              (unsigned long long)hf, (unsigned long long)hr);
        if (len == 0) {  // pointer AT the guard page with len 0 must not be touched
            uint64_t hg = chainhash::hash(fk, guard, 0);
            CHECK(hg == hf, "guard-page BW=%d K=%d S=%d len 0 at guard: %016llx vs %016llx", BW, K, S,
                  (unsigned long long)hg, (unsigned long long)hf);
        }
        // (ii) message starts exactly after the leading guard page
        fill_random(data, len);
        hf = chainhash::hash(fk, data, len);
        hr = chainhash_ref::hash(rk, data, len);
        CHECK(hf == hr, "guard-page(before) BW=%d K=%d S=%d len %zu: fast %016llx ref %016llx", BW, K, S, len,
              (unsigned long long)hf, (unsigned long long)hr);
        munmap(region, total);
        count++;
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* T5: chain_5 == monic degree-5 polynomial (symbolic expansion), its   */
/*     coefficient map is a bijection (explicit decoder), and the twist */
/* ------------------------------------------------------------------ */
typedef std::vector<uint64_t> Poly;  // coefficient i = coefficient of X^i, over GF(2^64)
static Poly padd(Poly a, const Poly& b) {
    if (a.size() < b.size()) a.resize(b.size(), 0);
    for (size_t i = 0; i < b.size(); i++) a[i] ^= b[i];
    return a;
}
static Poly pmul(const Poly& a, const Poly& b) {
    Poly r(a.size() + b.size() - 1, 0);
    for (size_t i = 0; i < a.size(); i++)
        for (size_t j = 0; j < b.size(); j++) r[i + j] ^= chainhash_ref::gfmul(a[i], b[j]);
    return r;
}
static Poly pconst(uint64_t c) { return Poly{c}; }
static uint64_t pcoeff(const Poly& p, size_t d) { return d < p.size() ? p[d] : 0; }
static uint64_t horner(const Poly& p, uint64_t v) {
    uint64_t h = 0;
    for (size_t i = p.size(); i-- > 0;) h = chainhash_ref::gfmul(h, v) ^ p[i];
    return h;
}

/* Symbolic expansion of the degree-5 circuit (a third transcription of
 * char2.js CIRCUITS[5], over GF(2^64)[X]; the same gate order as
 * chainhash.h / chainhash_ref.h). */
template <int K>
static Poly chain_poly(const uint64_t* c) {
    static_assert(K == 5, "only the degree-5 circuit is shipped");
    const Poly X{0, 1};
    Poly y = pmul(X, X);                                              // x x
    Poly z = pmul(padd(y, pconst(c[0])), padd(padd(X, y), pconst(c[1])));  // (y + c0)(x + y + c1)
    Poly t = pmul(padd(X, pconst(c[2])), padd(z, pconst(c[3])));      // (x + c2)(z + c3)
    return padd(t, pconst(c[4]));
}

/* EXPLICIT decoder (verify5.py; the paper's eq:ph:chain5-decoder).  With
 * b = c0 + c1 and d = c0 c1 the circuit's coefficients are
 *   e4 = 1 + c2,  e3 = b + c2,  e2 = c0 + c2 b,  e1 = d + c3 + c0 c2,
 *   e0 = c4 + c2 (d + c3),
 * and in the pivot coordinates q = (c2, b, c0, c3, c4), with
 * delta = q2 (q1 + q2) = c0 c1, the rows X^4 .. X^0 read
 *   e4 = q0 + 1,  e3 = q1 + q0,  e2 = q2 + q0 q1,  e1 = q3 + delta + q0 q2,
 *   e0 = q4 + q0 (delta + q3):
 * every row is q_i plus a polynomial in q_0..q_{i-1} (a unit pivot, no
 * Frobenius power), so the top-down solve below is a polynomial map valid
 * over every field of characteristic 2.  c = (q2, q1 + q2, q0, q3, q4). */
static void decode_chain5(const Poly& p, uint64_t* c_out) {
    using chainhash_ref::gfmul;
    const uint64_t e0 = pcoeff(p, 0), e1 = pcoeff(p, 1), e2 = pcoeff(p, 2), e3 = pcoeff(p, 3), e4 = pcoeff(p, 4);
    const uint64_t q0 = e4 ^ 1;                       // c2
    const uint64_t q1 = e3 ^ q0;                      // c0 + c1
    const uint64_t q2 = e2 ^ gfmul(q0, q1);           // c0
    const uint64_t dl = gfmul(q2, q1 ^ q2);           // delta = c0 c1
    const uint64_t q3 = e1 ^ dl ^ gfmul(q0, q2);      // c3
    const uint64_t q4 = e0 ^ gfmul(q0, dl ^ q3);      // c4
    c_out[0] = q2;
    c_out[1] = q1 ^ q2;
    c_out[2] = q0;
    c_out[3] = q3;
    c_out[4] = q4;
}

/* The same decoder in the generic form of website/js/char2.js
 * (decodeUnitriangular with KEYS_FROM_Q[5], all root depths 0): the pivot
 * coordinates q with c = A(q) = (q2, q1 + q2, q0, q3, q4); with
 * q_i = q_{i+1} = ... = 0 the circuit reproduces the constant part K_i of
 * row X^{4-i}, and the residual is q_i itself (unit pivot). */
static void keys_from_q5(const uint64_t* q, uint64_t* k) {
    k[0] = q[2];         // c0
    k[1] = q[1] ^ q[2];  // c1 = b + c0
    k[2] = q[0];         // c2
    k[3] = q[3];         // c3
    k[4] = q[4];         // c4
}
static void decode_chain5_pivot_loop(const Poly& p, uint64_t* k_out) {
    uint64_t q[5], kk[5];
    for (int i = 0; i < 5; i++) q[i] = 0;
    for (int i = 0; i < 5; i++) {
        keys_from_q5(q, kk);
        Poly base = chain_poly<5>(kk);  // q_i = q_{i+1} = ... = 0: row 4-i is K_i
        q[i] = pcoeff(p, 4 - i) ^ pcoeff(base, 4 - i);  // unit pivot: residual = q_i
    }
    keys_from_q5(q, k_out);
}

template <int BW, int K>
static long test_chain_is_monic_poly(int n_params, int n_points) {
    using FKey = chainhash::Key<BW, K, 1>;
    using RKey = chainhash_ref::Key<BW, K, 1>;
    long count = 0;
    for (int i = 0; i < n_params; i++) {
        uint64_t seed = rng();
        FKey fk = FKey::from_seed(seed);
        RKey rk = RKey::from_seed(seed);
        Poly p = chain_poly<K>(fk.c);
        CHECK(p.size() == (size_t)K + 1 && p[K] == 1, "K=%d: chain polynomial not monic of degree K (size %zu, lead %llx)",
              K, p.size(), (unsigned long long)p[K]);
        for (int j = 0; j < n_points; j++) {
            // pure chain: fast == ref == Horner
            uint64_t v = rng();
            uint64_t hp = horner(p, v);
            uint64_t hf = chainhash::chain<K>(fk.c, v);
            uint64_t hr = chainhash_ref::chain<K>(fk.c, v);
            CHECK(hp == hf && hp == hr, "K=%d: chain(%llx) fast %llx ref %llx horner %llx", K,
                  (unsigned long long)v, (unsigned long long)hf, (unsigned long long)hr, (unsigned long long)hp);
            // twisted finalizer: finalize(key, w) == Horner(p, w + t_in), integer add mod 2^64
            // (random w, plus carry-wrapping edge values around -t_in)
            uint64_t w;
            switch (j % 6) {
                case 0: w = 0; break;
                case 1: w = ~0ULL; break;
                case 2: w = 0 - fk.t_in; break;          // w + t_in wraps to 0
                case 3: w = ~fk.t_in; break;             // w + t_in = 2^64 - 1
                case 4: w = 0x8000000000000000ULL; break;
                default: w = rng(); break;
            }
            uint64_t tp = horner(p, w + fk.t_in);
            uint64_t tf = chainhash::finalize(fk, w);
            uint64_t tr = chainhash_ref::finalize(rk, w);
            CHECK(tp == tf && tp == tr, "K=%d: finalize(%llx) fast %llx ref %llx horner(w + t_in) %llx", K,
                  (unsigned long long)w, (unsigned long long)tf, (unsigned long long)tr, (unsigned long long)tp);
            count++;
        }
    }
    return count;
}
/* Bijectivity by explicit decoding: decode(encode(c)) == c for random c, and
 * encode(decode(p)) == p for random monic p (so the map is onto as well);
 * the closed-form decoder and the char2.js pivot loop agree. */
static long test_chain_bijective(int n_rounds) {
    const int K = 5;
    long count = 0;
    for (int i = 0; i < n_rounds; i++) {
        uint64_t c[K], d[K], d2[K];
        for (int t = 0; t < K; t++) c[t] = rng();
        Poly p = chain_poly<K>(c);
        decode_chain5(p, d);
        decode_chain5_pivot_loop(p, d2);
        CHECK(std::memcmp(c, d, sizeof(c)) == 0, "K=%d: decode(encode(c)) != c (round %d)", K, i);
        CHECK(std::memcmp(d, d2, sizeof(d)) == 0, "K=%d: closed-form decoder != pivot-loop decoder (round %d)", K, i);
        Poly p2 = chain_poly<K>(d);
        CHECK(p2 == p, "K=%d: encode(decode(encode(c))) != encode(c) (round %d)", K, i);
        // random monic target
        Poly r(K + 1, 0);
        for (int t = 0; t < K; t++) r[t] = rng();
        r[K] = 1;
        decode_chain5(r, d);
        decode_chain5_pivot_loop(r, d2);
        Poly r2 = chain_poly<K>(d);
        CHECK(r2 == r, "K=%d: encode(decode(p)) != p for random monic p (round %d)", K, i);
        CHECK(std::memcmp(d, d2, sizeof(d)) == 0, "K=%d: decoders disagree on random monic p (round %d)", K, i);
        count++;
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* T6: collision sanity                                                */
/* ------------------------------------------------------------------ */
template <int BW, int K>
static long test_collisions_pairs(long n_pairs) {
    using FKey = chainhash::Key<BW, K, 1>;
    FKey fk = FKey::from_seed(rng());
    long collisions = 0, regenerated = 0;
    uint8_t m1[64], m2[64];
    for (long i = 0; i < n_pairs; i++) {
        size_t l1 = 1 + rng() % 64, l2 = 1 + rng() % 64;
        fill_random(m1, l1);
        fill_random(m2, l2);
        while (l1 == l2 && std::memcmp(m1, m2, l1) == 0) {  // ensure distinct
            regenerated++;
            fill_random(m2, l2);
        }
        if (chainhash::hash(fk, m1, l1) == chainhash::hash(fk, m2, l2)) collisions++;
    }
    CHECK(collisions == 0, "BW=%d K=%d: %ld collisions among %ld random distinct pairs", BW, K, collisions, n_pairs);
    std::printf("  T6 BW=%d K=%d pairs: %ld pairs, %ld collisions, %ld pairs regenerated (were equal)\n", BW, K,
                n_pairs, collisions, regenerated);
    return n_pairs;
}
template <int BW, int K>
static long test_collisions_set(long n_msgs) {
    using FKey = chainhash::Key<BW, K, 1>;
    FKey fk = FKey::from_seed(rng());
    std::vector<uint64_t> hs;
    hs.reserve(n_msgs);
    uint8_t m[64];
    for (long i = 0; i < n_msgs; i++) {
        size_t len = 4 + (size_t)(i % 61);  // 4..64 bytes
        uint32_t ctr = (uint32_t)(i / 61);   // distinct within each length class
        fill_random(m, len);
        std::memcpy(m, &ctr, 4);  // little-endian counter -> all messages distinct
        hs.push_back(chainhash::hash(fk, m, len));
    }
    std::sort(hs.begin(), hs.end());
    long dup = 0;
    for (long i = 1; i < n_msgs; i++) dup += (hs[i] == hs[i - 1]);
    CHECK(dup == 0, "BW=%d K=%d: %ld duplicate hashes among %ld distinct messages", BW, K, dup, n_msgs);
    std::printf("  T6 BW=%d K=%d set: %ld distinct messages (4..64 B), %ld duplicate hashes\n", BW, K, n_msgs, dup);
    return n_msgs;
}

/* ------------------------------------------------------------------ */
/* T7: gf64 multiply fast vs reference                                 */
/* ------------------------------------------------------------------ */
static long test_gfmul(long n) {
    long count = 0;
    const uint64_t edge[] = {0, 1, 2, 27, 0x8000000000000000ULL, 0xFFFFFFFFFFFFFFFFULL, 0x8000000000000001ULL};
    for (uint64_t a : edge)
        for (uint64_t b : edge) {
            CHECK(chainhash::gfmul(a, b) == chainhash_ref::gfmul(a, b), "gfmul(%llx,%llx)", (unsigned long long)a,
                  (unsigned long long)b);
            count++;
        }
    for (long i = 0; i < n; i++) {
        uint64_t a = rng(), b = rng();
        uint64_t f = chainhash::gfmul(a, b), r = chainhash_ref::gfmul(a, b);
        CHECK(f == r, "gfmul(%llx,%llx): fast %llx ref %llx", (unsigned long long)a, (unsigned long long)b,
              (unsigned long long)f, (unsigned long long)r);
        count++;
    }
    // commutativity / associativity spot checks on the fast multiply
    for (long i = 0; i < 1000; i++) {
        uint64_t a = rng(), b = rng(), c = rng();
        CHECK(chainhash::gfmul(a, b) == chainhash::gfmul(b, a), "gfmul not commutative");
        CHECK(chainhash::gfmul(chainhash::gfmul(a, b), c) == chainhash::gfmul(a, chainhash::gfmul(b, c)),
              "gfmul not associative");
    }
    return count;
}

/* ------------------------------------------------------------------ */
/* Grid drivers: T1-T4 for one (BLOCK_WORDS, K, S)                     */
/* ------------------------------------------------------------------ */
static long g_t1_msgs = 0, g_t1_points = 0, g_t4_lengths = 0, g_t4_points = 0;
static long g_t2 = 0, g_t3 = 0;

template <int BW, int K, int S>
static void run_point(long scale) {
    int n_keys = (int)std::max(1L, 50 / scale);
    long n1 = test_fast_vs_ref<BW, K, S>(n_keys);
    long n2 = test_determinism<BW, K, S>(100);
    long n3 = test_length_sensitivity<BW, K, S>(500, 4);
    long n4 = test_guard_page<BW, K, S>();
    std::printf("  BW=%3d K=%2d S=%d: T1 %ld messages (%d keys x %zu lengths), T2 %ld seeds, T3 %ld messages, "
                "T4 %ld lengths\n", BW, K, S, n1, n_keys, g_lengths.size(), n2, n3, n4);
    g_t1_msgs += n1; g_t1_points++;
    g_t2 += n2; g_t3 += n3;
    g_t4_lengths += n4; g_t4_points++;
}

int main(int argc, char** argv) {
    long scale = (argc > 1) ? std::atol(argv[1]) : 1;  // optional divisor for quick runs
    if (scale < 1) scale = 1;
    std::setvbuf(stdout, nullptr, _IONBF, 0);
    build_lengths();
    std::printf("ChainHash tests: K = 5 (char2.js CIRCUITS[5]) behind the additive input twist; grid (8,5,1), "
                "(32,5,1), (32,5,2), (32,5,4), (128,5,1), (128,5,2), (128,5,4); ASAN build: %s\n",
                HAVE_ASAN ? "yes" : "no");
    std::printf("length set: %zu lengths = 0..200, 1000..1100, 2030..2070, 4080..4110, and %d random:",
                g_lengths.size(), N_RANDOM_LENGTHS);
    for (size_t i = g_lengths.size() - N_RANDOM_LENGTHS; i < g_lengths.size(); i++)
        std::printf(" %zu", g_lengths[i]);
    std::printf("\n");

    long n;
    n = test_gfmul(100000 / scale);
    std::printf("T7 gfmul fast vs ref: %ld products checked\n", n);

    std::printf("-- shipped: (32,5,1) = chainhash-256, (128,5,2) = chainhash-1k; plus (8,5,1) and the other splits\n");
    run_point<8, 5, 1>(scale);
    run_point<32, 5, 1>(scale);
    run_point<32, 5, 2>(scale);
    run_point<32, 5, 4>(scale);
    run_point<128, 5, 1>(scale);
    run_point<128, 5, 2>(scale);
    run_point<128, 5, 4>(scale);
    std::printf("T1 fast == reference: %ld grid points, %ld messages total\n", g_t1_points, g_t1_msgs);
    std::printf("T2 determinism: %ld seeds total;  T3 length sensitivity: %ld messages total\n", g_t2, g_t3);
    std::printf("T4 guard page after+before message: %ld grid points, %ld lengths total; ASAN: %s\n", g_t4_points,
                g_t4_lengths, HAVE_ASAN ? "yes" : "no");

    std::printf("T5 chain == monic degree-5 polynomial, coefficient map bijective (explicit unit-pivot decoder), "
                "twist = integer add:\n");
    {
        long n5 = test_chain_is_monic_poly<128, 5>(200, 24);
        long b5 = test_chain_bijective(200);
        std::printf("  K= 5 (%d mults): monic degree-5, fast == ref == Horner: %ld points (200 parameter sets; each "
                    "point also checks finalize == Horner(p, w + t_in)); explicit decoder round trips: %ld rounds "
                    "(x2: random params, random monic target; closed form == char2.js pivot loop)\n",
                    chainhash::chain_mults(5), n5, b5);
    }

    long p8 = test_collisions_pairs<8, 5>(1000000 / scale);
    long s8 = test_collisions_set<8, 5>(1000000 / scale);
    std::printf("T6 BW=8 collisions: pairs %ld; set %ld\n", p8, s8);
    long p128 = test_collisions_pairs<128, 5>(1000000 / scale);
    long s128 = test_collisions_set<128, 5>(1000000 / scale);
    std::printf("T6 BW=128 collisions: pairs %ld; set %ld\n", p128, s128);

    std::printf("checks run: %ld, failed: %ld\n", g_checks, g_fail);
    std::printf(g_fail == 0 ? "ALL TESTS PASSED\n" : "SOME TESTS FAILED\n");
    return g_fail == 0 ? 0 : 1;
}
