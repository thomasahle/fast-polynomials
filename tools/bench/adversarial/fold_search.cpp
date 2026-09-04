/* ***********************************************************************
 * Differential characterization of the multiply-fold
 *     fold_n(u, Q) = lo_n(u*Q) (+/^) hi_n(u*Q)
 * for n-bit operands (2n-bit product).
 *
 * In every multiply-fold hash the two multiplicands are
 *     u = (message word) (+/^) (secret/state),  Q = (message word) (+/^) (state).
 * An attacker who does not know the secret controls only the DIFFERENCE
 * (delta, eps) between the multiplicands of two messages, while (u, Q) are
 * uniform.  We therefore measure, for candidate differences,
 *     P(delta,eps) = Pr_{u,Q}[ fold(u, Q) = fold(u ^ delta, Q ^ eps) ]
 * (and the additive analogue with u + delta, Q + eps).  A random function
 * would give P ~ 2^-n.
 *
 * Part 1: n = 8: EXHAUSTIVE over all (delta,eps) != (0,0) and all (u,Q),
 *         for the four combinations {xor,add}-difference x {xor,add}-fold.
 * Part 2: the best structured differences, at n = 8..64, sampled
 *         (n = 8,12,16 exact), to obtain the scaling exponent of P in n.
 *
 * Build: clang++ -O3 -std=c++17 -march=native fold_search.cpp -o fold_search
 * ***********************************************************************/
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <thread>
#include <atomic>
#include <cmath>
#include <string>
#include "hashes.h"

typedef unsigned __int128 u128;

template <int N> struct Ops {
    static constexpr uint64_t mask = (N == 64) ? ~0ull : ((1ull << N) - 1);
    static inline uint64_t fold(uint64_t u, uint64_t q, bool addfold) {
        u128 r = (u128)u * q;
        uint64_t lo = (uint64_t)r & mask, hi = (uint64_t)(r >> N) & mask;
        return addfold ? ((lo + hi) & mask) : (lo ^ hi);
    }
};

/* ---------- Part 1: exhaustive n = 8 ---------- */
struct Cand { uint32_t d, e; uint64_t cnt; };

static void exhaustive8(bool adddiff, bool addfold, const char* label) {
    const int N = 8; const uint64_t M = 255;
    std::vector<Cand> res;
    res.reserve(65535);
    for (uint32_t d = 0; d < 256; d++)
        for (uint32_t e = 0; e < 256; e++) {
            if (!d && !e) continue;
            uint64_t cnt = 0;
            for (uint32_t u = 0; u < 256; u++)
                for (uint32_t q = 0; q < 256; q++) {
                    uint64_t u2 = adddiff ? ((u + d) & M) : (u ^ d);
                    uint64_t q2 = adddiff ? ((q + e) & M) : (q ^ e);
                    cnt += Ops<N>::fold(u, q, addfold) == Ops<N>::fold(u2, q2, addfold);
                }
            res.push_back({d, e, cnt});
        }
    std::sort(res.begin(), res.end(), [](const Cand& a, const Cand& b) { return a.cnt > b.cnt; });
    double total = 65536.0;
    // statistics: mean over all differences, and how many exceed 4x the random rate
    double sum = 0; size_t above = 0;
    for (auto& c : res) { sum += c.cnt; if (c.cnt >= 4 * 256) above++; }
    printf("\n### n=8, %s\n\n", label);
    printf("mean P over all 65535 differences = %.4f (random-function reference 2^-8 = %.4f); %zu differences with P >= 4*2^-8\n\n",
           sum / res.size() / total, 1.0 / 256, above);
    printf("| rank | delta | eps | #(u,Q) colliding / 65536 | P | log2 P |\n|---|---|---|---|---|---|\n");
    for (int i = 0; i < 12; i++) {
        auto& c = res[i];
        printf("| %d | 0x%02x | 0x%02x | %llu | %.4f | %.2f |\n", i + 1, c.d, c.e, (unsigned long long)c.cnt, c.cnt / total, log2(c.cnt / total));
    }
}

/* ---------- Part 2: structured differences at larger n ---------- */
struct DiffSpec { const char* label; bool adddiff; bool addfold; int kind; };
// kind: how (delta,eps) depends on n:
//   0: (M, M)      1: (M, 0)      2: (0, M)     3: (2^(n-1), 2^(n-1))
//   4: (M, M-1)    5: (M-1, M)    6: (2^(n-1), 0)   7: (M, 2^(n-1))
//   8: (A, 0)  A = 0101...01 alternating   9: (A, A)   10: (-A, 0) (additive negation)  11: (A, -A)
static inline void diff_of(int kind, int n, uint64_t& d, uint64_t& e) {
    uint64_t M = (n == 64) ? ~0ull : ((1ull << n) - 1), T = 1ull << (n - 1);
    uint64_t A = 0x5555555555555555ull & M, nA = (0 - A) & M;
    switch (kind) {
        case 0: d = M; e = M; break;   case 1: d = M; e = 0; break;
        case 2: d = 0; e = M; break;   case 3: d = T; e = T; break;
        case 4: d = M; e = M - 1; break; case 5: d = M - 1; e = M; break;
        case 6: d = T; e = 0; break;   case 7: d = M; e = T; break;
        case 8: d = A; e = 0; break;   case 9: d = A; e = A; break;
        case 10: d = nA; e = 0; break; case 11: d = A; e = nA; break;
        default: d = e = 0;
    }
}
static const char* kind_name(int k) {
    static const char* nm[] = {"(M,M)", "(M,0)", "(0,M)", "(T,T)", "(M,M-1)", "(M-1,M)", "(T,0)", "(M,T)", "(A,0)", "(A,A)", "(-A,0)", "(A,-A)"};
    return nm[k];
}

template <int N>
static uint64_t count_sampled(bool adddiff, bool addfold, uint64_t d, uint64_t e, uint64_t samples, int nthreads) {
    std::atomic<uint64_t> total{0};
    std::vector<std::thread> th;
    uint64_t M = Ops<N>::mask;
    for (int t = 0; t < nthreads; t++)
        th.emplace_back([&, t]() {
            Rng r(0x1234567 + 977 * t + 31 * N);
            uint64_t per = samples / nthreads, cnt = 0;
            for (uint64_t i = 0; i < per; i++) {
                uint64_t u = r.next() & M, q = r.next() & M;
                uint64_t u2 = adddiff ? ((u + d) & M) : (u ^ d);
                uint64_t q2 = adddiff ? ((q + e) & M) : (q ^ e);
                cnt += Ops<N>::fold(u, q, addfold) == Ops<N>::fold(u2, q2, addfold);
            }
            total += cnt;
        });
    for (auto& x : th) x.join();
    return total;
}

template <int N>
static uint64_t count_exact(bool adddiff, bool addfold, uint64_t d, uint64_t e, int nthreads) {
    std::atomic<uint64_t> total{0};
    std::vector<std::thread> th;
    uint64_t M = Ops<N>::mask;
    for (int t = 0; t < nthreads; t++)
        th.emplace_back([&, t]() {
            uint64_t cnt = 0;
            for (uint64_t u = t; u <= M; u += nthreads)
                for (uint64_t q = 0; q <= M; q++) {
                    uint64_t u2 = adddiff ? ((u + d) & M) : (u ^ d);
                    uint64_t q2 = adddiff ? ((q + e) & M) : (q ^ e);
                    cnt += Ops<N>::fold(u, q, addfold) == Ops<N>::fold(u2, q2, addfold);
                }
            total += cnt;
        });
    for (auto& x : th) x.join();
    return total;
}

template <int N>
static void row(bool adddiff, bool addfold, int kind, uint64_t samples, int nthreads) {
    uint64_t d, e; diff_of(kind, N, d, e);
    uint64_t hits; double P; std::string how;
    if (N <= 16) { hits = count_exact<N>(adddiff, addfold, d, e, nthreads); P = (double)hits / ldexp(1.0, 2 * N); how = "exact"; }
    else { hits = count_sampled<N>(adddiff, addfold, d, e, samples, nthreads); P = (double)hits / samples; how = "2^" + std::to_string((int)log2((double)samples)) + " samples"; }
    printf("| %d | %s | %s | %llu | %s | %.3e | %.2f | %.3f |\n", N, kind_name(kind), how.c_str(), (unsigned long long)hits,
           hits ? "" : "(none)", P, hits ? log2(P) : -INFINITY, hits ? -log2(P) / N : 0.0);
    fflush(stdout);
}

int main(int argc, char** argv) {
    int nthreads = argc > 1 ? atoi(argv[1]) : (int)std::thread::hardware_concurrency();
    uint64_t samples = argc > 2 ? (1ull << atoi(argv[2])) : (1ull << 34);
    printf("# Multiply-fold differential search (threads=%d)\n", nthreads);

    printf("\n## Part 1: exhaustive search over all differences, n = 8\n");
    exhaustive8(false, false, "XOR-difference, XOR-fold (wyhash/rapidhash/xxh3/paper-MUM-xor)");
    exhaustive8(true, false, "ADD-difference, XOR-fold (paper-MUM-add)");
    exhaustive8(false, true, "XOR-difference, ADD-fold (MUM v3 fold)");
    exhaustive8(true, true, "ADD-difference, ADD-fold");

    printf("\n## Part 2: scaling of the best structured differences with n\n");
    printf("\nM = 2^n - 1 (all ones), T = 2^(n-1) (top bit), A = 0101...0101 (alternating), -A = 2^n - A.  Column -log2(P)/n is the exponent c in P = 2^(-c n) (c = 1 for a random function).\n\n");
    struct Cfg { bool adddiff, addfold; const char* label; int kinds[6]; int nk; };
    Cfg cfgs[] = {
        {false, false, "XOR-difference, XOR-fold (wyhash / rapidhash / XXH3 / paper-MUM-xor)", {0, 1, 9, 4, 7}, 5},
        {true, false, "ADD-difference, XOR-fold (paper-MUM-add)", {8, 10, 9, 11, 0, 3}, 6},
        {false, true, "XOR-difference, ADD-fold (MUM v3 _mum)", {0, 1, 8, 9}, 4},
        {true, true, "ADD-difference, ADD-fold", {8, 10, 11, 0}, 4},
    };
    for (auto& c : cfgs) {
        printf("\n### %s\n\n| n | (delta,eps) | method | hits | | P | log2 P | -log2(P)/n |\n|---|---|---|---|---|---|---|---|\n", c.label);
        for (int ki = 0; ki < c.nk; ki++) {
            int k = c.kinds[ki];
            row<8>(c.adddiff, c.addfold, k, samples, nthreads);
            row<12>(c.adddiff, c.addfold, k, samples, nthreads);
            row<16>(c.adddiff, c.addfold, k, samples, nthreads);
            row<24>(c.adddiff, c.addfold, k, samples, nthreads);
            row<32>(c.adddiff, c.addfold, k, samples, nthreads);
            row<48>(c.adddiff, c.addfold, k, samples, nthreads);
            row<64>(c.adddiff, c.addfold, k, samples, nthreads);
        }
    }
    return 0;
}
