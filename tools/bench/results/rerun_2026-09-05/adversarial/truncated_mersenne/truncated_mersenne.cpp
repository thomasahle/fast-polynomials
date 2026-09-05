/* Truncated Mersenne outputs (appendix_adversarial.tex, "Truncated Mersenne outputs").
 *
 * Hash A: the paper's injective recurrence over F_p, p = 2^89-1, two keys
 *   x in [0,p) and y in [0,2^63):  P_0 = x,  P_i = a_i + (b_i + y)(P_{i-1} + x^2),
 *   a_i an 8-byte word, b_i a 7-byte word (15 bytes per step; speed_hashes.h::PaperMers89Smart),
 *   OUTPUT = low 64 bits of the fully reduced residue.
 *   Message pair: two 30-byte (2-step) messages equal except the final a-word (a_2):
 *   0 vs 0xFFFFFFFFFFFFFFFF, i.e. residues differing by exactly 2^64-1 mod p.
 *   Expected truncated-collision rate ~ 2^64/p = 2^-25.
 * Hash B: the same recurrence over p = 2^61-1 with 32-bit field elements
 *   (hashes.h::PaperMersenne: each 64-bit word w -> a = low32(w), b = high32(w);
 *   P = a + (b + x^3)(P + x^2), single key x in [0,p)), OUTPUT = low 32 bits of the residue.
 *   Message pair: two 32-byte (4-word) messages equal except the low 32 bits (a_4) of the
 *   last word: 0 vs 0xFFFFFFFF.  Expected rate ~ 2^32/p = 2^-29.
 * All arithmetic is exact reference arithmetic (binary-method mulmod for p = 2^89-1,
 * __int128 product + Mersenne folding for p = 2^61-1).  Both hashes also report the
 * FULL-residue collision count (control; must be 0) and the count of residues in the
 * top window [p - (2^w - 1), p) (which is exactly the truncated-collision event).
 *
 * Usage: ./truncated_mersenne [threads=8] [log2keysA=26] [log2keysB=30] [salt=1]
 *        (threads must divide both key counts).  Per-thread RNG seeding follows
 *        adversarial.cpp::count_fixed: Rng(salt*0x9E3779B97F4A7C15 + 7919*t + 1).
 * Build: clang++ -O3 -std=c++17 truncated_mersenne.cpp -o truncated_mersenne
 */
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <thread>
#include <vector>
typedef unsigned __int128 u128;

struct Rng {   // xoshiro256** seeded by splitmix64, as in tools/bench/adversarial/hashes.h
    uint64_t s[4];
    static uint64_t splitmix(uint64_t& x) {
        uint64_t z = (x += 0x9e3779b97f4a7c15ull);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ull;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebull;
        return z ^ (z >> 31);
    }
    explicit Rng(uint64_t seed = 1) { for (int i = 0; i < 4; i++) s[i] = splitmix(seed); }
    static inline uint64_t rotl(uint64_t x, int k) { return (x << k) | (x >> (64 - k)); }
    uint64_t next() {
        uint64_t r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
        s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3]; s[2] ^= t; s[3] = rotl(s[3], 45);
        return r;
    }
    u128 next128() { return ((u128)next() << 64) | next(); }
};

/* ---------------- p = 2^89 - 1, exact reference arithmetic ---------------- */
static const u128 M89P = (((u128)1) << 89) - 1;
static inline u128 m89_reduce(u128 h) {            // any 128-bit h -> [0, p)
    h = (h & M89P) + (h >> 89);
    h = (h & M89P) + (h >> 89);
    if (h >= M89P) h -= M89P;
    return h;
}
static inline u128 m89_mulmod(u128 a, u128 b) {    // binary method, exact
    a = m89_reduce(a); b = m89_reduce(b);
    u128 r = 0;
    for (int i = 0; i < 89; i++) {
        if ((b >> i) & 1) { r += a; if (r >= M89P) r -= M89P; }
        a <<= 1; if (a >= M89P) a -= M89P;
    }
    return r;
}
static inline u128 m89_random_key(Rng& r) { u128 x; do { x = r.next128() >> 39; } while (x >= M89P); return x; }

/* ---------------- p = 2^61 - 1, exact ---------------- */
static const uint64_t M61P = (1ull << 61) - 1;
static inline uint64_t m61_reduce128(u128 h) {     // h < 2^122 -> [0, p)
    uint64_t r = (uint64_t)(h & M61P) + (uint64_t)(h >> 61);   // < 2^61 + 2^61
    r = (r & M61P) + (r >> 61);
    if (r >= M61P) r -= M61P;
    return r;
}
static inline uint64_t m61_mul(uint64_t a, uint64_t b) { return m61_reduce128((u128)a * b); }
static inline uint64_t m61_add(uint64_t a, uint64_t b) { uint64_t r = a + b; if (r >= M61P) r -= M61P; return r; }

struct Counts { uint64_t trunc = 0, full = 0, window = 0; };

/* Hash A over 2^lg keys: returns collision counts (truncated / full / top-window). */
static Counts runA(int threads, int lg, uint64_t salt, uint64_t a1, uint64_t b1, uint64_t b2) {
    uint64_t total = 1ull << lg, per = total / threads;
    std::vector<Counts> cs(threads); std::vector<std::thread> th;
    const u128 topA = M89P - ((((u128)1) << 64) - 1);        // residues >= topA wrap when 2^64-1 is added
    for (int t = 0; t < threads; t++) th.emplace_back([&, t] {
        Rng r(salt * 0x9E3779B97F4A7C15ull + 7919 * t + 1);
        Counts c;
        for (uint64_t i = 0; i < per; i++) {
            u128 x = m89_random_key(r); u128 x2 = m89_mulmod(x, x); uint64_t y = r.next() >> 1;
            u128 P1 = m89_reduce(a1 + m89_mulmod((u128)b1 + y, x + x2));          // step 1 (shared)
            u128 T = m89_mulmod((u128)b2 + y, P1 + x2);                           // step 2 product (shared)
            u128 R0 = m89_reduce(T + 0);                                          // a_2 = 0
            u128 R1 = m89_reduce(T + 0xFFFFFFFFFFFFFFFFull);                      // a_2 = 2^64-1
            c.full += (R0 == R1);
            c.trunc += ((uint64_t)R0 == (uint64_t)R1);
            c.window += (R0 >= topA);
        }
        cs[t] = c;
    });
    for (auto& x : th) x.join();
    Counts s; for (auto& c : cs) { s.trunc += c.trunc; s.full += c.full; s.window += c.window; }
    return s;
}

/* Hash B over 2^lg keys. words w[0..3] fixed; the last word's low 32 bits are 0 vs 0xFFFFFFFF. */
static Counts runB(int threads, int lg, uint64_t salt, const uint64_t w[4]) {
    uint64_t total = 1ull << lg, per = total / threads;
    std::vector<Counts> cs(threads); std::vector<std::thread> th;
    const uint64_t topB = M61P - 0xFFFFFFFFull;
    for (int t = 0; t < threads; t++) th.emplace_back([&, t] {
        Rng r(salt * 0x9E3779B97F4A7C15ull + 7919 * t + 1);
        Counts c;
        for (uint64_t i = 0; i < per; i++) {
            uint64_t x; do { x = r.next() >> 3; } while (x >= M61P);
            uint64_t x2 = m61_mul(x, x), x3 = m61_mul(x2, x);
            uint64_t P = x;
            for (int k = 0; k < 3; k++) {
                uint64_t a = (uint32_t)w[k], b = w[k] >> 32;
                P = m61_add(a, m61_mul(m61_add(b, x3), m61_add(P, x2)));
            }
            uint64_t b4 = w[3] >> 32;
            uint64_t T = m61_mul(m61_add(b4, x3), m61_add(P, x2));               // shared final product
            uint64_t R0 = m61_add(0, T), R1 = m61_add(0xFFFFFFFFull, T);
            c.full += (R0 == R1);
            c.trunc += ((uint32_t)R0 == (uint32_t)R1);
            c.window += (R0 >= topB);
        }
        cs[t] = c;
    });
    for (auto& x : th) x.join();
    Counts s; for (auto& c : cs) { s.trunc += c.trunc; s.full += c.full; s.window += c.window; }
    return s;
}

int main(int argc, char** argv) {
    int threads = argc > 1 ? atoi(argv[1]) : 8;
    int lgA = argc > 2 ? atoi(argv[2]) : 26, lgB = argc > 3 ? atoi(argv[3]) : 30;
    uint64_t salt = argc > 4 ? strtoull(argv[4], 0, 0) : 1;
    if ((1ull << lgA) % threads || (1ull << lgB) % threads) { fprintf(stderr, "threads must divide 2^lgA and 2^lgB\n"); return 1; }
    // self-check of the p = 2^89-1 reference product against Python-verifiable triples
    { Rng r(7); for (int i = 0; i < 3; i++) { u128 a = m89_random_key(r), b = m89_random_key(r), c = m89_mulmod(a, b);
        printf("selfcheck m89: a=0x%016llx%016llx b=0x%016llx%016llx (a*b) mod (2^89-1) = 0x%016llx%016llx\n",
               (unsigned long long)(a >> 64), (unsigned long long)a, (unsigned long long)(b >> 64), (unsigned long long)b,
               (unsigned long long)(c >> 64), (unsigned long long)c); } }
    { Rng r(7); for (int i = 0; i < 3; i++) { uint64_t a, b; do { a = r.next() >> 3; } while (a >= M61P); do { b = r.next() >> 3; } while (b >= M61P);
        printf("selfcheck m61: a=0x%016llx b=0x%016llx (a*b) mod (2^61-1) = 0x%016llx\n", (unsigned long long)a, (unsigned long long)b, (unsigned long long)m61_mul(a, b)); } }
    // fixed pseudo-random base message words (salt 12345 as in adversarial.cpp::base_msg)
    Rng mr(12345);
    uint64_t a1 = mr.next(), b1 = mr.next() >> 8, b2 = mr.next() >> 8;     // 8-byte a, 7-byte b's
    uint64_t w[4]; for (int i = 0; i < 4; i++) w[i] = mr.next();
    printf("threads=%d salt=%llu\n", threads, (unsigned long long)salt);
    printf("Hash A: F_{2^89-1} injective recurrence (PaperMers89Smart), 30-byte messages a1=0x%016llx b1=0x%014llx a2={0, 2^64-1} b2=0x%014llx, low-64-bit output, 2^%d random keys (x,y)\n",
           (unsigned long long)a1, (unsigned long long)b1, (unsigned long long)b2, lgA);
    Counts A = runA(threads, lgA, salt, a1, b1, b2);
    printf("  truncated (low 64 bits) collisions: %llu / 2^%d  (expected 2^%d * 2^64/p = %.2f)\n", (unsigned long long)A.trunc, lgA, lgA, (double)(1ull << lgA) * 18446744073709551616.0 / 618970019642690137449562111.0);
    printf("  full-residue collisions (control):  %llu / 2^%d\n", (unsigned long long)A.full, lgA);
    printf("  residues in the top window [p-(2^64-1), p): %llu\n", (unsigned long long)A.window);
    printf("Hash B: F_{2^61-1} recurrence with 32-bit words (PaperMersenne), 32-byte messages w=(0x%016llx,0x%016llx,0x%016llx,0x%08llx|{0,0xFFFFFFFF}), low-32-bit output, 2^%d random keys x\n",
           (unsigned long long)w[0], (unsigned long long)w[1], (unsigned long long)w[2], (unsigned long long)(w[3] >> 32), lgB);
    Counts B = runB(threads, lgB, salt, w);
    printf("  truncated (low 32 bits) collisions: %llu / 2^%d  (expected 2^%d * 2^32/p = %.2f)\n", (unsigned long long)B.trunc, lgB, lgB, (double)(1ull << lgB) * 4294967296.0 / 2305843009213693951.0);
    printf("  full-residue collisions (control):  %llu / 2^%d\n", (unsigned long long)B.full, lgB);
    printf("  residues in the top window [p-(2^32-1), p): %llu\n", (unsigned long long)B.window);
    return 0;
}
