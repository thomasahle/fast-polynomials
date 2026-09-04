/* ***********************************************************************
 * ChainHash -- SLOW REFERENCE implementation (plain C++, no intrinsics).
 *
 * Bit-by-bit carry-less multiply, bit-by-bit reduction modulo
 * x^64 + x^4 + x^3 + x + 1, a single PH accumulator, byte-wise word
 * assembly with implicit zero padding (never reads past the input).
 *
 * Must compute exactly the same function as chainhash.h:
 *   n = max(1, ceil(len / (8*BLOCK_WORDS))) blocks.  Blocks 1..n-1 are
 *   full (BLOCK_WORDS/2 pairs).  The last block holds r = len - (n-1)*
 *   8*BLOCK_WORDS bytes and only W' = ceil(r/16) pairs (W' = 0 for the
 *   empty message); its final partial pair is zero-padded to 16 bytes.
 *   Each block is cut into S sub-blocks of BLOCK_WORDS/(2S) pairs; sub-block
 *   i of block j covers the block's pairs [i*BLOCK_WORDS/(2S), (i+1)*
 *   BLOCK_WORDS/(2S)) and its PH sum runs over those of its pairs that
 *   exist (index < W'), so a sub-block beyond the data has PH sum 0:
 *     (a_{j,i}, b_{j,i}) = (lo64, hi64) of
 *        XOR_{pairs p of sub-block i, p < W'} clmul64(w[2p]^k[2p], w[2p+1]^k[2p+1]);
 *   the n*S pairs are fed to the recurrence in order (j, i);
 *   a_{n,S-1} ^= len (byte length, into the LAST pair);
 *   P_0 = z,  P_m = a_m + (b_m + y)(P_{m-1} + u)     (three-key recurrence
 *   of injective.tex; u, y, z independent uniform field elements)
 *   v = P_{nS} + t_in   (INTEGER 64-bit addition mod 2^64: the input twist)
 *   out = chain_5(v)    with the degree-5 circuit of chainhash.h
 *   (CIRCUITS[5] of website/js/char2.js, 3 multiplications).
 *   S = 1 (the default) is the original single-pair-per-block function.
 * Key: k[0..BLOCK_WORDS), u, y, z, c[0..5), t_in  (BLOCK_WORDS + 9 words).
 * *********************************************************************** */

#ifndef CHAINHASH_REF_H
#define CHAINHASH_REF_H

#include <cstddef>
#include <cstdint>

namespace chainhash_ref {

typedef unsigned __int128 u128;

static inline uint64_t splitmix64(uint64_t& state) {
    uint64_t z = (state += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

/* 64x64 -> 128 carry-less product, bit by bit. */
static inline u128 clmul(uint64_t a, uint64_t b) {
    u128 r = 0;
    for (int i = 0; i < 64; i++)
        if ((b >> i) & 1) r ^= (u128)a << i;
    return r;
}

/* Reduce a 128-bit polynomial modulo x^64 + x^4 + x^3 + x + 1, bit by bit. */
static inline uint64_t reduce(u128 r) {
    const u128 P = ((u128)1 << 64) | 27u;  // x^64 + x^4 + x^3 + x + 1
    for (int i = 127; i >= 64; i--)
        if ((r >> i) & 1) r ^= P << (i - 64);
    return (uint64_t)r;
}

static inline uint64_t gfmul(uint64_t a, uint64_t b) { return reduce(clmul(a, b)); }

static constexpr bool valid_degree(int K) { return K == 5; }

/* Defaults as in chainhash.h: 256-byte blocks, degree-5 finalizer, S = 1
 * (chainhash-256); the 1 KB configuration (chainhash-1k) is <128, 5, 2>. */
template <int BLOCK_WORDS = 32, int K = 5, int S = 1>
struct Key {
    static_assert(S == 1 || S == 2 || S == 4, "S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 2 * S && BLOCK_WORDS % (2 * S) == 0, "BLOCK_WORDS must be a multiple of 2*S");
    static_assert(valid_degree(K), "K must be 5 (the only shipped chain)");
    static constexpr int block_words = BLOCK_WORDS;
    static constexpr int block_bytes = 8 * BLOCK_WORDS;
    static constexpr int split = S;

    uint64_t k[BLOCK_WORDS];
    uint64_t u, y, z;
    uint64_t c[K];
    uint64_t t_in;  // input twist word

    /* Derivation order from the seed: k[0..BLOCK_WORDS), u, y, z, c[0..K), t_in. */
    static Key from_seed(uint64_t seed) {
        Key key;
        uint64_t s = seed;
        for (int i = 0; i < BLOCK_WORDS; i++) key.k[i] = splitmix64(s);
        key.u = splitmix64(s);
        key.y = splitmix64(s);
        key.z = splitmix64(s);
        for (int i = 0; i < K; i++) key.c[i] = splitmix64(s);
        key.t_in = splitmix64(s);
        return key;
    }
};

/* Degree-5 chain with parameters c[] (same gate order as the fast version):
 * char2.js CIRCUITS[5]. */
template <int K>
static inline uint64_t chain(const uint64_t* c, uint64_t v) {
    static_assert(valid_degree(K), "chain: only K = 5 is shipped");
    uint64_t y = gfmul(v, v);                    // x x
    uint64_t z = gfmul(y ^ c[0], v ^ y ^ c[1]);  // (y + c0)(x + y + c1)
    uint64_t t = gfmul(v ^ c[2], z ^ c[3]);      // (x + c2)(z + c3)
    return t ^ c[4];
}

/* finalize(key, v) = chain_K(c, v + t_in), the twist as a plain integer add. */
template <int BLOCK_WORDS, int K, int S>
static inline uint64_t finalize(const Key<BLOCK_WORDS, K, S>& key, uint64_t v) {
    return chain<K>(key.c, v + key.t_in);
}

/* Little-endian 64-bit word number `idx` of the zero-padded message. */
static inline uint64_t word_at(const uint8_t* m, size_t len, size_t idx) {
    uint64_t w = 0;
    for (size_t t = 0; t < 8; t++) {
        size_t byte = 8 * idx + t;
        if (byte < len) w |= (uint64_t)m[byte] << (8 * t);
    }
    return w;
}

template <int BLOCK_WORDS, int K, int S>
static inline uint64_t hash(const Key<BLOCK_WORDS, K, S>& key, const void* data, size_t len) {
    const uint8_t* m = static_cast<const uint8_t*>(data);
    const size_t BB = (size_t)Key<BLOCK_WORDS, K, S>::block_bytes;
    const size_t WPS = (size_t)BLOCK_WORDS / (2 * S);  // pairs per sub-block
    const size_t n = (len == 0) ? 1 : (len + BB - 1) / BB;

    uint64_t P = key.z;  // P_0 = z
    for (size_t j = 0; j < n; j++) {
        // bytes in this block: BB for blocks 0..n-2, r = len - (n-1)*BB for the last
        // (r = 0 for the empty message); the block has W' = ceil(r/16) pairs.
        const size_t r = (j + 1 == n) ? len - j * BB : BB;
        const size_t W = (r + 15) / 16;
        for (int i = 0; i < S; i++) {
            u128 acc = 0;  // single accumulator; sub-block i = pairs [i*WPS, (i+1)*WPS) of the block
            for (size_t pi = (size_t)i * WPS; pi < (size_t)(i + 1) * WPS && pi < W; pi++) {
                uint64_t wa = word_at(m, len, j * BLOCK_WORDS + 2 * pi) ^ key.k[2 * pi];
                uint64_t wb = word_at(m, len, j * BLOCK_WORDS + 2 * pi + 1) ^ key.k[2 * pi + 1];
                acc ^= clmul(wa, wb);
            }
            uint64_t a = (uint64_t)acc;
            uint64_t b = (uint64_t)(acc >> 64);
            if (j + 1 == n && i + 1 == S) a ^= (uint64_t)len;
            P = a ^ gfmul(b ^ key.y, P ^ key.u);  // P_m = a_m + (b_m + y)(P_{m-1} + u)
        }
    }
    return chain<K>(key.c, P + key.t_in);  // twist (integer add), then the degree-5 chain
}

}  // namespace chainhash_ref

#endif  // CHAINHASH_REF_H
