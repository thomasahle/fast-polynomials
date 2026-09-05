"""Derive chainhash_goldi_exp.cpp (SMHasher3 experimental hash file) from the mr/chainhash
hashes/chainhash.cpp: identifiers renamed (chg_ prefix, family chainhash_goldi), the finalizer
template parameter FIN, the Goldilocks field layer pasted verbatim from goldi_field.h."""
import re, pathlib
S = pathlib.Path(__file__).resolve().parent
src = (S/'chainhash_smh_shipped.cpp').read_text()
field = (S/'goldi_field.h').read_text()

def sub(old, new, s, count=1):
    assert s.count(old) == count, (old[:70], s.count(old))
    return s.replace(old, new)

s = src
s = re.sub(r'\bchainhash_(?=[A-Za-z0-9])', 'chg_', s)
s = re.sub(r'\bCHAINHASH_', 'CHG_', s)
s = re.sub(r'\bChainHash(?=\s*[<(])', 'ChainHashG', s)

s = sub('/*\n * ChainHash: a 64-bit hash over GF(2^64)', '''/*
 * EXPERIMENTAL (goldilocks_finalizer, 2026-09-05): ChainHash with a
 * finalizer over the Goldilocks prime field F_p, p = 2^64 - 2^32 + 1,
 * instead of the characteristic-2 degree-5 circuit.  Derived from
 * hashes/chainhash.cpp (branch mr/chainhash) by derive_exp.py of the
 * experiment directory; PH and recurrence levels unchanged; every identifier
 * renamed (chg_ prefix, family chainhash_goldi) so that both files link into
 * one binary.  Registrations:
 *   chainhash-g4-256  256-byte blocks, S = 1, finalizer G4 (Motzkin's quartic,
 *                     2 multiplications, 4-wise independent)
 *   chainhash-g5-256  256-byte blocks, S = 1, finalizer G5 (the paper's
 *                     degree-5 scheme, 3 multiplications, 5-wise independent)
 *   chainhash-g5-1k   1 KB blocks, S = 2, finalizer G5
 * Finalizer input: x = P_n folded into F_p by one conditional subtraction
 * (v >= p -> v - p); no twist.  Keys g[] uniform in F_p by rejection sampling
 * of further splitmix64 words, appended after t_in (c[], t_in unused by G4/G5).
 * Reference: goldi_ref.py / chainhash_goldi.h of the experiment directory.
 *
 * ChainHash: a 64-bit hash over GF(2^64)''', s)

s = sub('''    uint64_t c[K];
    uint64_t t_in;
    // derived (chg_key_setup)''', '''    uint64_t c[K];
    uint64_t t_in;
    uint64_t g[5];                 // G4 / G5 finalizer parameters, uniform in F_p (4 or 5 used)
    uint64_t ng[5];                // derived: p - g[i], the subtraction-form addition operands
    // derived (chg_key_setup)''', s)

gl = field.split('#include <stdint.h>\n', 1)[1].rsplit('#endif', 1)[0]
gl = re.sub(r'\bgl_', 'chg_gl_', gl)
gl = re.sub(r'\bGL_', 'CHG_GL_', gl)
gl = gl.replace('static inline ', 'static FORCE_INLINE ')
s = sub('''//------------------------------------------------------------
// Backend primitives.  Every backend provides''', '''//------------------------------------------------------------
// Goldilocks prime field F_p, p = 2^64 - 2^32 + 1 (scalar), and the two
// experimental finalizers.  Verbatim goldi_field.h of the experiment
// (checked against Python big-int arithmetic on 10^6 inputs).
enum { CHG_FIN_CHAR2 = 0, CHG_FIN_G4 = 1, CHG_FIN_G5 = 2 };
''' + gl + '''
//------------------------------------------------------------
// Backend primitives.  Every backend provides''', s)

s = sub('''template <int BLOCK_WORDS, int K>
static uintptr_t chg_seed_init( const seed_t seed ) {
    static thread_local chg_key<BLOCK_WORDS, K> key;''', '''template <int BLOCK_WORDS, int K, int FIN>
static uintptr_t chg_seed_init( const seed_t seed ) {
    static thread_local chg_key<BLOCK_WORDS, K> key;''', s)
s = sub('''    key.t_in = chg_splitmix64(s);
    chg_key_setup(key);
    return (uintptr_t)&key;''', '''    key.t_in = chg_splitmix64(s);
    for (int i = 0; i < 5; i++) { key.g[i] = 0; key.ng[i] = CHG_GL_P; }
    for (int i = 0; i < (FIN == CHG_FIN_G4 ? 4 : FIN == CHG_FIN_G5 ? 5 : 0); i++) {
        key.g[i]  = chg_gl_uniform(&s);
        key.ng[i] = CHG_GL_P - key.g[i];
    }
    chg_key_setup(key);
    return (uintptr_t)&key;''', s)

s = sub('''#if !defined(CHG_IMPL_PORTABLE)

// Recurrence step on the state Q = P + u''', '''// The selected finalizer on the chain value P_n: the 64-bit hash.
//   CHAR2: the shipped twist + degree-5 circuit (backend-specific below);
//   G4 / G5: lane 0 out, fold into F_p, scalar circuit (backend independent).
template <int FIN>
struct chg_fin;

template <>
struct chg_fin<CHG_FIN_G4> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gl_fin_g4(key->g, key->ng, chg_gl_fold(chg_gf_to(P)));
    }
};

template <>
struct chg_fin<CHG_FIN_G5> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gl_fin_g5(key->g, key->ng, chg_gl_fold(chg_gf_to(P)));
    }
};

#if !defined(CHG_IMPL_PORTABLE)

template <>
struct chg_fin<CHG_FIN_CHAR2> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gf_to(chg_finalize<K>::apply(key->c, chg_v_add64(P, chg_v_load2(key->tin))));   // chain(c, P + t_in)
    }
};

// Recurrence step on the state Q = P + u''', s)

s = sub('''template <int BLOCK_WORDS, int K, int S, bool bswap>
static FORCE_INLINE chg_gf chg_small_v( const chg_key<BLOCK_WORDS, K> * key, const uint8_t * p,
        const size_t len ) {''', '''template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static FORCE_INLINE uint64_t chg_small_v( const chg_key<BLOCK_WORDS, K> * key, const uint8_t * p,
        const size_t len ) {''', s)
s = sub('''    return chg_finalize<K>::apply(key->c, chg_v_add64(P, chg_v_load2(key->tin)));   // chain(c, P_S + t_in)
}''', '''    return chg_fin<FIN>::apply(key, P);   // the selected finalizer on P_S
}''', s)
s = sub('''template <int BLOCK_WORDS, int K, int S, bool bswap>
static NEVER_INLINE void chg_multi(''', '''template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static NEVER_INLINE void chg_multi(''', s)
s = sub('''    // Input twist (integer add of t_in, a fixed bijection), then the degree-K chain.
    const chg_gf v = chg_v_add64(Q, chg_v_load2(key->tin));
    PUT_U64<bswap>(chg_gf_to(chg_finalize<K>::apply(key->c, v)), (uint8_t *)out, 0);
}''', '''    PUT_U64<bswap>(chg_fin<FIN>::apply(key, Q), (uint8_t *)out, 0);   // the selected finalizer on P_n
}''', s)
s = sub('''template <int BLOCK_WORDS, int K, int S, bool bswap>
static void ChainHashG( const void * in, const size_t len, const seed_t seed, void * out ) {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
            "BLOCK_WORDS must be a positive multiple of 8*S (4 pairs per inner iteration, per sub-block)");
    static_assert(K == 5, "only the degree-5 finalizer is shipped");

    const chg_key<BLOCK_WORDS, K> * key = (const chg_key<BLOCK_WORDS, K> *)(uintptr_t)seed;
    const uint8_t * p = (const uint8_t *)in;
    constexpr size_t SB = 8 * (size_t)(BLOCK_WORDS / S);          // bytes per sub-block

    if (unlikely(len > SB)) {
        return chg_multi<BLOCK_WORDS, K, S, bswap>(key, p, len, out);   // tail call
    }
    PUT_U64<bswap>(chg_gf_to(chg_small_v<BLOCK_WORDS, K, S, bswap>(key, p, len)), (uint8_t *)out, 0);
}''', '''template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static void ChainHashG( const void * in, const size_t len, const seed_t seed, void * out ) {
    static_assert(S == 1 || S == 2 || S == 4, "sub-block split S must be 1, 2 or 4");
    static_assert(BLOCK_WORDS >= 8 * S && BLOCK_WORDS % (8 * S) == 0,
            "BLOCK_WORDS must be a positive multiple of 8*S (4 pairs per inner iteration, per sub-block)");
    static_assert(K == 5, "only the degree-5 finalizer is shipped");
    static_assert(FIN == CHG_FIN_CHAR2 || FIN == CHG_FIN_G4 || FIN == CHG_FIN_G5, "FIN must be CHAR2, G4 or G5");

    const chg_key<BLOCK_WORDS, K> * key = (const chg_key<BLOCK_WORDS, K> *)(uintptr_t)seed;
    const uint8_t * p = (const uint8_t *)in;
    constexpr size_t SB = 8 * (size_t)(BLOCK_WORDS / S);          // bytes per sub-block

    if (unlikely(len > SB)) {
        return chg_multi<BLOCK_WORDS, K, S, FIN, bswap>(key, p, len, out);   // tail call
    }
    PUT_U64<bswap>(chg_small_v<BLOCK_WORDS, K, S, FIN, bswap>(key, p, len), (uint8_t *)out, 0);
}''', s)
s = sub('''#else // CHG_IMPL_PORTABLE: the definition, evaluated literally

template <int BLOCK_WORDS, int K, int S, bool bswap>
static void ChainHashG( const void * in, const size_t len, const seed_t seed, void * out ) {''', '''#else // CHG_IMPL_PORTABLE: the definition, evaluated literally

template <>
struct chg_fin<CHG_FIN_CHAR2> {
    template <int BLOCK_WORDS, int K>
    static FORCE_INLINE uint64_t apply( const chg_key<BLOCK_WORDS, K> * key, chg_gf P ) {
        return chg_gf_to(chg_finalize<K>::apply(key->c, chg_gf_addint(P, key->t_in)));   // chain(c, P + t_in)
    }
};

template <int BLOCK_WORDS, int K, int S, int FIN, bool bswap>
static void ChainHashG( const void * in, const size_t len, const seed_t seed, void * out ) {''', s)
s = sub('''    // Input twist (integer add of t_in, a fixed bijection), then the degree-K chain.
    const chg_gf v = chg_gf_addint(P, key->t_in);
    const uint64_t     h = chg_gf_to(chg_finalize<K>::apply(key->c, v));
    PUT_U64<bswap>(h, (uint8_t *)out, 0);
}''', '''    PUT_U64<bswap>(chg_fin<FIN>::apply(key, P), (uint8_t *)out, 0);   // the selected finalizer on P_n
}''', s)

head, _ = s.split('REGISTER_FAMILY(', 1)
def reg(name, desc, code, bw, S, fin, be):
    return f'''REGISTER_HASH({name},
   $.desc       = "{desc}",
   $.impl       = CHG_IMPL_STR,
   $.hash_flags =
         FLAG_HASH_CLMUL_BASED,
   $.impl_flags =
         CHG_IMPL_FLAGS,
   $.bits = 64,
   $.verification_LE = {code},
   $.verification_BE = {be},
   $.seedfn          = chg_seed_init<{bw}, 5, {fin}>,
   $.hashfn_native   = ChainHashG<{bw}, 5, {S}, {fin}, false>,
   $.hashfn_bswap    = ChainHashG<{bw}, 5, {S}, {fin}, true>
 );
'''
s = head + '''REGISTER_FAMILY(chainhash_goldi,
   $.src_status = HashFamilyInfo::SRC_ACTIVE
 );

''' + reg('chainhash_g4_256', 'ChainHash EXPERIMENT: carry-less PH + three-key injective chain + Goldilocks-field Motzkin quartic finalizer (2 mults, 4-wise), 256-byte blocks', '0xA3577E75', 32, 1, 'CHG_FIN_G4', '0xAE143AED') + '\n' + \
    reg('chainhash_g5_256', 'ChainHash EXPERIMENT: carry-less PH + three-key injective chain + Goldilocks-field degree-5 finalizer (3 mults, 5-wise), 256-byte blocks', '0xF89E636F', 32, 1, 'CHG_FIN_G5', '0x229C22B5') + '\n' + \
    reg('chainhash_g5_1k', 'ChainHash EXPERIMENT: carry-less PH + three-key injective chain + Goldilocks-field degree-5 finalizer (3 mults, 5-wise), 1024-byte blocks, 2 sub-blocks per block', '0xC8B38421', 128, 2, 'CHG_FIN_G5', '0x6024310F')
(S/'chainhash_goldi_exp.cpp').write_text(s)
assert not re.findall(r'\bchainhash_(?!goldi|g4|g5)', s)
print("chainhash_goldi_exp.cpp:", len(s.splitlines()), "lines")
