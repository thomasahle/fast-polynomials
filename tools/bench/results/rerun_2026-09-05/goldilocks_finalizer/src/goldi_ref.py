"""Python big-int reference of ChainHash<BLOCK_WORDS, 5, S, FIN> as defined in chainhash_goldi.h:
bit-serial carry-less PH, the three-key GF(2^64) recurrence (mirrors chainhash_ref.h), then the
selected finalizer: CHAR2 (integer twist + degree-5 char-2 circuit), G4 (fold + Motzkin quartic over
F_p), G5 (fold + paper's degree-5 scheme over F_p).  Key derivation as in the header."""
MASK = (1 << 64) - 1
P = 2**64 - 2**32 + 1
FIN_CHAR2, FIN_G4, FIN_G5 = 0, 1, 2
FIN_WORDS = {FIN_CHAR2: 0, FIN_G4: 4, FIN_G5: 5}

class SM:
    def __init__(self, state): self.s = state & MASK
    def next(self):
        self.s = (self.s + 0x9E3779B97F4A7C15) & MASK
        z = self.s
        z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK
        z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK
        return z ^ (z >> 31)
    def uniform_p(self):
        while True:
            v = self.next()
            if v < P: return v

def clmul(a, b):
    r = 0
    for i in range(64):
        if (b >> i) & 1: r ^= a << i
    return r
def gf_reduce(r):
    PP = (1 << 64) | 27
    for i in range(127, 63, -1):
        if (r >> i) & 1: r ^= PP << (i - 64)
    return r
def gfmul(a, b): return gf_reduce(clmul(a, b))

def key_from_seed(seed, BW, FIN):
    sm = SM(seed)
    k = [sm.next() for _ in range(BW)]
    u, y, z = sm.next(), sm.next(), sm.next()
    c = [sm.next() for _ in range(5)]
    t_in = sm.next()
    g = [sm.uniform_p() for _ in range(FIN_WORDS[FIN])]
    return dict(k=k, u=u, y=y, z=z, c=c, t_in=t_in, g=g)

def word_at(m, idx):
    return int.from_bytes(m[8*idx:8*idx+8].ljust(8, b'\0'), 'little')

def chain_value(key, m, BW, S):
    """P_{nS}: the recurrence value before the finalizer (independent of FIN)."""
    ln = len(m); BB = 8 * BW; WPS = BW // (2 * S)
    n = 1 if ln == 0 else (ln + BB - 1) // BB
    Pv = key['z']
    for j in range(n):
        r = ln - j * BB if j + 1 == n else BB
        W = (r + 15) // 16
        for i in range(S):
            acc = 0
            for pi in range(i * WPS, min((i + 1) * WPS, W)):
                wa = word_at(m, j * BW + 2 * pi) ^ key['k'][2 * pi]
                wb = word_at(m, j * BW + 2 * pi + 1) ^ key['k'][2 * pi + 1]
                acc ^= clmul(wa, wb)
            a = acc & MASK; b = acc >> 64
            if j + 1 == n and i + 1 == S: a ^= ln
            Pv = a ^ gfmul(b ^ key['y'], Pv ^ key['u'])
    return Pv

def fin_char2(key, Pv):
    c = key['c']; v = (Pv + key['t_in']) & MASK
    y = gfmul(v, v)
    z = gfmul(y ^ c[0], v ^ y ^ c[1])
    t = gfmul(v ^ c[2], z ^ c[3])
    return t ^ c[4]
def fin_g4(key, Pv):
    g = key['g']; x = Pv % P
    y = (x * (x + g[0]) + g[1]) % P
    return (y * (y + x + g[2]) + g[3]) % P
def fin_g5(key, Pv):
    g = key['g']; x = Pv % P
    x2 = x * x
    return ((x + g[2]) * ((x2 + g[4]) * (x2 + x + g[3]) + g[1]) + g[0]) % P
FINS = {FIN_CHAR2: fin_char2, FIN_G4: fin_g4, FIN_G5: fin_g5}

def hash_msg(seed, m, BW, S, FIN):
    key = key_from_seed(seed, BW, FIN)
    return FINS[FIN](key, chain_value(key, m, BW, S))

def test_message(i):
    """Deterministic (seed, message) of test index i, shared with test_goldi.cpp."""
    sm = SM(0xABCDEF + i)
    ln = sm.next() % 2101
    buf = b''.join(sm.next().to_bytes(8, 'little') for _ in range((ln + 7) // 8))
    seed = sm.next()
    return seed, buf[:ln]

if __name__ == '__main__':
    import sys
    # stdin: lines "i len h_char2_256 h_g4_256 h_g5_256 h_char2_1k h_g5_1k" (hex) from test_goldi.cpp
    n = bad = 0
    for line in sys.stdin:
        f = line.split()
        if f[0] != 'M': continue
        i, ln = int(f[1]), int(f[2]); got = [int(t, 16) for t in f[3:8]]
        seed, m = test_message(i)
        assert len(m) == ln, (i, len(m), ln)
        keys = {FIN: key_from_seed(seed, 32, FIN) for FIN in (FIN_CHAR2, FIN_G4, FIN_G5)}
        Pv256 = chain_value(keys[FIN_CHAR2], m, 32, 1)
        exp = [fin_char2(keys[FIN_CHAR2], Pv256), fin_g4(keys[FIN_G4], Pv256), fin_g5(keys[FIN_G5], Pv256)]
        k1k = {FIN: key_from_seed(seed, 128, FIN) for FIN in (FIN_CHAR2, FIN_G5)}
        Pv1k = chain_value(k1k[FIN_CHAR2], m, 128, 2)
        exp += [fin_char2(k1k[FIN_CHAR2], Pv1k), fin_g5(k1k[FIN_G5], Pv1k)]
        n += 1
        if exp != got:
            bad += 1; print("MISMATCH", i, ln, [hex(v) for v in got], [hex(v) for v in exp])
    print(f"python reference: {n} messages x 5 configurations compared, {bad} mismatches")
    sys.exit(1 if bad else 0)
