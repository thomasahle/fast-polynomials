/* ============================================================================
 * ahash.h  --  Faithful C/C++ port of aHash 0.8.10 (the AES-NI / ARM-AES path)
 *
 * Upstream:  https://github.com/tkaitchuck/aHash  (MIT OR Apache-2.0)
 * Version:   0.8.10   (Cargo.toml `version = "0.8.10"`)
 * Ported by transcribing, line for line, the reference Rust source:
 *     src/aes_hash.rs      (AHasher::{from_random_state,hash_in,hash_in_2,write,finish})
 *     src/operations.rs    (aesenc, aesdec, shuffle, shuffle_and_add,
 *                           add_by_64s, add_in_length, read_small, folded_multiply)
 *     src/convert.rs       (read_u16/32/64/128 + read_last_* little-endian reads)
 *     src/random_state.rs  (PI2 constants, RandomState::with_seeds)
 *     smhasher/ahash-cbindings/src/lib.rs  (the exported `ahash64` entry point)
 *
 * This reproduces exactly the value returned by the crate's own C binding
 *
 *     #[no_mangle] pub extern "C" fn ahash64(buf, len, seed: u64) -> u64 {
 *         let bh = RandomState::with_seeds(seed, seed, seed, seed);
 *         bh.hash_one(&buf)            // default-features = false  =>  specialize OFF
 *     }
 *
 * With `specialize` off (as in the cbindings crate) `hash_one(&buf)` reduces to
 *   let mut h = AHasher::from_random_state(&rs);
 *   <[u8] as Hash>::hash(buf, &mut h);   //  h.write_usize(len); h.write(buf);
 *   h.finish()
 *
 * PLATFORM NOTE (faithfulness): aHash's `shuffle` is NOT platform independent.
 *   - x86/x86-64 (ssse3):  shuffle(a) = _mm_shuffle_epi8(a, SHUFFLE_MASK)
 *   - everything else:     shuffle(a) = a.swap_bytes()   (full 16-byte reverse)
 * so the aHash output on aarch64 differs from x86.  This port selects the same
 * branch the Rust crate selects for the architecture it is compiled on, so it
 * byte-matches the real crate built for that same architecture.  The `aesenc`/
 * `aesdec` rounds are mathematically identical on x86 (_mm_aesenc/_mm_aesdec)
 * and ARM (vaesmcq_u8(vaeseq_u8(.,0)) ^ k), so only `shuffle` differs.
 *
 * The ARM path corresponds to the crate's `nightly-arm-aes` feature (which
 * routes aarch64 through src/aes_hash.rs instead of the scalar fallback).
 * ==========================================================================*/
#ifndef VENDOR_AHASH_0810_H
#define VENDOR_AHASH_0810_H

#include <cstdint>
#include <cstddef>
#include <cstring>

namespace ahash_0810 {

typedef unsigned __int128 u128;

/* ---- PI2 constants (src/random_state.rs) -------------------------------- */
static const uint64_t AHASH_PI2[4] = {
    0x452821e638d01377ULL,
    0xbe5466cf34e90c6cULL,
    0xc0ac29b7c97c50ddULL,
    0x3f84d5b5b5470917ULL,
};

/* ---- little-endian helpers ---------------------------------------------- */
static inline uint16_t rd_u16(const uint8_t* p){ uint16_t v; std::memcpy(&v,p,2); return v; }
static inline uint32_t rd_u32(const uint8_t* p){ uint32_t v; std::memcpy(&v,p,4); return v; }
static inline uint64_t rd_u64(const uint8_t* p){ uint64_t v; std::memcpy(&v,p,8); return v; }
static inline u128    rd_u128(const uint8_t* p){ u128    v; std::memcpy(&v,p,16); return v; }

static inline u128 mk_u128(uint64_t lo, uint64_t hi){ return (u128)lo | ((u128)hi << 64); }
static inline uint64_t lo64(u128 x){ return (uint64_t)x; }
static inline uint64_t hi64(u128 x){ return (uint64_t)(x >> 64); }

/* ========================================================================= */
/* aesenc / aesdec  --  one AES round, then XOR the argument.                 */
/*   x86  : _mm_aesenc_si128(value, xor)  =  MixColumns.SubBytes.ShiftRows ^ k*/
/*   arm  : xor ^ vaesmcq_u8(vaeseq_u8(value, 0))  =  same round             */
/* ========================================================================= */
#if defined(__aarch64__)
#include <arm_neon.h>

__attribute__((target("aes")))
static inline u128 aesenc(u128 value, u128 xr){
    uint8x16_t v; std::memcpy(&v,&value,16);
    uint8x16_t r = vaesmcq_u8(vaeseq_u8(v, vdupq_n_u8(0)));
    u128 rv; std::memcpy(&rv,&r,16);
    return xr ^ rv;
}
__attribute__((target("aes")))
static inline u128 aesdec(u128 value, u128 xr){
    uint8x16_t v; std::memcpy(&v,&value,16);
    uint8x16_t r = vaesimcq_u8(vaesdq_u8(v, vdupq_n_u8(0)));
    u128 rv; std::memcpy(&rv,&r,16);
    return xr ^ rv;
}
#define AHASH_TARGET __attribute__((target("aes")))

/* aarch64: shuffle == u128::swap_bytes()  (reverse all 16 bytes) */
static inline u128 shuffle(u128 a){
    return mk_u128(__builtin_bswap64(hi64(a)), __builtin_bswap64(lo64(a)));
}

#elif defined(__x86_64__) || defined(__i386__)
#include <immintrin.h>

__attribute__((target("aes")))
static inline u128 aesenc(u128 value, u128 xr){
    __m128i v; std::memcpy(&v,&value,16);
    __m128i k; std::memcpy(&k,&xr,16);
    __m128i r = _mm_aesenc_si128(v, k);
    u128 rv; std::memcpy(&rv,&r,16); return rv;
}
__attribute__((target("aes")))
static inline u128 aesdec(u128 value, u128 xr){
    __m128i v; std::memcpy(&v,&value,16);
    __m128i k; std::memcpy(&k,&xr,16);
    __m128i r = _mm_aesdec_si128(v, k);
    u128 rv; std::memcpy(&rv,&r,16); return rv;
}
#define AHASH_TARGET __attribute__((target("aes,ssse3")))

/* x86: shuffle == _mm_shuffle_epi8(a, SHUFFLE_MASK) with the searched mask
 *      SHUFFLE_MASK = 0x020a0700_0c01030e_050f0d08_06090b04  (src/operations.rs) */
__attribute__((target("ssse3")))
static inline u128 shuffle(u128 a){
    static const u128 MASK = ((u128)0x020a07000c01030eULL << 64) | (u128)0x050f0d0806090b04ULL;
    __m128i v; std::memcpy(&v,&a,16);
    __m128i m; std::memcpy(&m,&MASK,16);
    __m128i r = _mm_shuffle_epi8(v, m);
    u128 rv; std::memcpy(&rv,&r,16); return rv;
}
#else
#error "ahash.h: unsupported architecture (need aarch64 or x86)"
#endif

#ifndef AHASH_TARGET
#define AHASH_TARGET
#endif

/* ---- add_by_64s / shuffle_and_add / add_in_length ----------------------- */
static inline u128 add_by_64s(u128 a, u128 b){
    return mk_u128(lo64(a) + lo64(b), hi64(a) + hi64(b));
}
AHASH_TARGET
static inline u128 shuffle_and_add(u128 base, u128 to_add){
    return add_by_64s(shuffle(base), to_add);
}
static inline void add_in_length(u128* enc, uint64_t len){
    *enc = mk_u128(lo64(*enc) + len, hi64(*enc));
}

/* ---- read_small (src/operations.rs) : <=8 bytes into two u64s ----------- */
static inline u128 read_small(const uint8_t* d, size_t len){
    uint64_t a, b;
    if (len >= 2) {
        if (len >= 4) { a = rd_u32(d); b = rd_u32(d + len - 4); }     /* 4..8 */
        else          { a = rd_u16(d); b = d[len - 1]; }              /* 2..3 */
    } else {
        if (len > 0)  { a = d[0]; b = d[0]; }                         /* 1    */
        else          { a = 0;    b = 0;   }                          /* 0    */
    }
    return mk_u128(a, b);
}

/* ========================================================================= */
/* AHasher (src/aes_hash.rs)                                                  */
/* ========================================================================= */
struct AHasher {
    u128 enc;
    u128 sum;
    u128 key;

    AHASH_TARGET
    inline void hash_in(u128 v){
        enc = aesdec(enc, v);
        sum = shuffle_and_add(sum, v);
    }
    AHASH_TARGET
    inline void hash_in_2(u128 v1, u128 v2){
        enc = aesdec(enc, v1);
        sum = shuffle_and_add(sum, v1);
        enc = aesdec(enc, v2);
        sum = shuffle_and_add(sum, v2);
    }

    /* Hasher::write (src/aes_hash.rs) */
    AHASH_TARGET
    inline void write(const uint8_t* data, size_t length){
        add_in_length(&enc, (uint64_t)length);

        if (length <= 8) {
            hash_in(read_small(data, length));
        } else {
            if (length > 32) {
                if (length > 64) {
                    /* current[] seeded from the last 64 bytes */
                    const uint8_t* tailp = data + length - 64;
                    u128 t0 = rd_u128(tailp), t1 = rd_u128(tailp+16),
                         t2 = rd_u128(tailp+32), t3 = rd_u128(tailp+48);
                    u128 current[4] = { key, key, key, key };
                    current[0] = aesenc(current[0], t0);
                    current[1] = aesdec(current[1], t1);
                    current[2] = aesenc(current[2], t2);
                    current[3] = aesdec(current[3], t3);
                    u128 sum2[2] = { key, ~key };
                    sum2[0] = add_by_64s(sum2[0], t0);
                    sum2[1] = add_by_64s(sum2[1], t1);
                    sum2[0] = shuffle_and_add(sum2[0], t2);
                    sum2[1] = shuffle_and_add(sum2[1], t3);

                    const uint8_t* p = data;
                    size_t remaining = length;
                    while (remaining > 64) {
                        u128 b0 = rd_u128(p),    b1 = rd_u128(p+16),
                             b2 = rd_u128(p+32), b3 = rd_u128(p+48);
                        current[0] = aesdec(current[0], b0);
                        current[1] = aesdec(current[1], b1);
                        current[2] = aesdec(current[2], b2);
                        current[3] = aesdec(current[3], b3);
                        sum2[0] = shuffle_and_add(sum2[0], b0);
                        sum2[1] = shuffle_and_add(sum2[1], b1);
                        sum2[0] = shuffle_and_add(sum2[0], b2);
                        sum2[1] = shuffle_and_add(sum2[1], b3);
                        p += 64; remaining -= 64;
                    }
                    hash_in_2(current[0], current[1]);
                    hash_in_2(current[2], current[3]);
                    hash_in_2(sum2[0], sum2[1]);
                } else {
                    /* len 33..64 */
                    u128 h0 = rd_u128(data), h1 = rd_u128(data + 16);
                    const uint8_t* tailp = data + length - 32;
                    u128 t0 = rd_u128(tailp), t1 = rd_u128(tailp + 16);
                    hash_in_2(h0, h1);
                    hash_in_2(t0, t1);
                }
            } else {
                if (length > 16) {
                    /* len 17..32 */
                    hash_in_2(rd_u128(data), rd_u128(data + length - 16));
                } else {
                    /* len 9..16 */
                    hash_in(mk_u128(rd_u64(data), rd_u64(data + length - 8)));
                }
            }
        }
    }

    /* Hasher::finish (src/aes_hash.rs) */
    AHASH_TARGET
    inline uint64_t finish() const {
        u128 combined = aesenc(sum, enc);
        u128 result   = aesdec(aesdec(combined, key), combined);
        return lo64(result);
    }
};

/* AHasher::from_random_state (src/aes_hash.rs) : keys straight from k0..k3   */
AHASH_TARGET
static inline AHasher from_keys(uint64_t k0, uint64_t k1, uint64_t k2, uint64_t k3){
    u128 key1 = mk_u128(k0, k1);
    u128 key2 = mk_u128(k2, k3);
    AHasher h;
    h.enc = key1;
    h.sum = key2;
    h.key = key1 ^ key2;
    return h;
}

/* ========================================================================= */
/* ahash64 : the exact entry point exported by smhasher/ahash-cbindings      */
/*   RandomState::with_seeds(seed,seed,seed,seed).hash_one(&buf)              */
/* ========================================================================= */
AHASH_TARGET
static inline uint64_t ahash64(const uint8_t* buf, size_t len, uint64_t seed){
    /* RandomState::with_seeds(s,s,s,s) : k_i = s ^ PI2[i] */
    AHasher h = from_keys(seed ^ AHASH_PI2[0], seed ^ AHASH_PI2[1],
                          seed ^ AHASH_PI2[2], seed ^ AHASH_PI2[3]);
    /* <[u8] as Hash>::hash : write_usize(len) then write(buf)               */
    h.hash_in((u128)(uint64_t)len);   /* write_usize -> write_u64 -> write_u128 -> hash_in */
    h.write(buf, len);
    return h.finish();
}

} /* namespace ahash_0810 */

#endif /* VENDOR_AHASH_0810_H */
