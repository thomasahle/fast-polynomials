# anf_check.py -- GF(2) algebraic (ANF) degree of the ChainHash finalizer with and
# without the additive input twist, restricted to 10 input bits, over random keys.
#
#   f_c(v)          : the degree-5 circuit over GF(2^64)   (y = v v, z = (y+c0)(v+y+c1),
#                                                            t = (v+c2)(z+c3), f = t+c4)
#   sigma_t(v)      : v (+) t, 64-bit integer addition mod 2^64
#   xor_t(v)        : v XOR t (a GF(2)-affine bijection, for contrast)
#
# For a set of bit positions I = {i_0 < ... < i_{r-1}} and a base vector v* with those
# bits cleared, the restriction h|_{v* + span(2^i : i in I)} is a function on {0,1}^r
# with values in GF(2)^64; its ANF coefficients are the Moebius transform
#   coef(S) = XOR_{T subseteq S} h(v* + sum_{i in T} 2^i),
# and its degree is max{|S| : coef(S) != 0} (0 if constant).  deg(h) >= deg of any
# restriction, so a restriction of degree >= 3 certifies that h is not quadratic.
#
# Also checked numerically (all exhaustive over the relevant small cubes):
#   * the carry ANF  kappa_i = sum_{j<i} v_j t_j prod_{l=j+1}^{i-1} (v_l + t_l)
#     and the explicit bits s_0, s_1, s_2 of v (+) t   (prop:ph:twist-bits);
#   * w_r := XOR_{j<2^r} ((t + 2^{j0} j) mod 2^64) = 2^{j0+r} (m XOR (m+1)) with
#     m = floor(t / 2^{j0+r}) (mod 2^{64-j0-r}), for t with lowest set bit j0 (the slope
#     of e_1 in the top ANF coefficient, prop:ph:twist-degree);
#   * the top coefficient on the cube {bits j0..j0+r-1} is affine in e_1 with slope w_r.
import random, itertools, sys
MASK = (1 << 64) - 1
POLY = (1 << 64) | 0b11011           # x^64 + x^4 + x^3 + x + 1

def gfmul(a, b):
    r = 0
    while b:
        if b & 1: r ^= a
        b >>= 1; a <<= 1
        if a >> 64: a ^= POLY
    return r

def f5(c, v):                         # the degree-5 circuit
    y = gfmul(v, v)
    z = gfmul(y ^ c[0], v ^ y ^ c[1])
    t = gfmul(v ^ c[2], z ^ c[3])
    return t ^ c[4]

def f3(c, v):                         # the degree-3 circuit (CIRCUITS[3]), for contrast
    y = gfmul(v, v)
    z = gfmul(v ^ c[0], v ^ y ^ c[1])
    return z ^ c[2]

def f7(c, v):                         # the former degree-7 circuit, for contrast
    y = gfmul(v, v ^ c[0]); z = gfmul(v ^ c[1], y ^ c[2]); t = gfmul(z, z ^ c[3])
    u = gfmul(v ^ c[4], y ^ t ^ c[5]); return u ^ c[6]

def encode5(c):                       # e_0..e_4 of f_c (eq:ph:chain5-coeffs)
    c0, c1, c2, c3, c4 = c
    b = c0 ^ c1; d = gfmul(c0, c1)
    return [c4 ^ gfmul(c2, d ^ c3), d ^ c3 ^ gfmul(c0, c2), c0 ^ gfmul(c2, b), b ^ c2, 1 ^ c2]

def decode5(e):                       # eq:ph:chain5-decoder
    e0, e1, e2, e3, e4 = e
    q0 = e4 ^ 1; q1 = e3 ^ q0; q2 = e2 ^ gfmul(q0, q1)
    dl = gfmul(q2, q1 ^ q2); q3 = e1 ^ dl ^ gfmul(q0, q2); q4 = e0 ^ gfmul(q0, dl ^ q3)
    return [q2, q1 ^ q2, q0, q3, q4]

def add64(v, t): return (v + t) & MASK

def anf_degree(h, bits, base):
    """ANF degree of v -> h(v) restricted to base + span{2^i : i in bits}; also the per-output-bit max."""
    r = len(bits)
    vals = []
    for m in range(1 << r):
        v = base
        for k in range(r):
            if m >> k & 1: v |= 1 << bits[k]
        vals.append(h(v))
    # Moebius transform, in place, on 64-bit words (all output bits in parallel)
    for k in range(r):
        step = 1 << k
        for m in range(1 << r):
            if m & step: vals[m] ^= vals[m ^ step]
    deg = -1; top = 0
    for m in range(1 << r):
        if vals[m]:
            w = bin(m).count('1')
            if w > deg: deg = w
            if w == r: top = vals[m]
    return deg, top   # top = coefficient of the full monomial prod_{i in bits} v_i

def lowest_set_bit(t):
    return (t & -t).bit_length() - 1

random.seed(20260904)
R = 10
print(f"=== ANF degree on {R}-bit cubes, 20 random keys each (max possible on the cube: {R}) ===")
rows = []
for trial in range(20):
    c5 = [random.getrandbits(64) for _ in range(5)]
    c3 = [random.getrandbits(64) for _ in range(3)]
    c7 = [random.getrandbits(64) for _ in range(7)]
    t  = random.getrandbits(64) | 1          # odd twist word (j0 = 0)
    base = random.getrandbits(64) & ~((1 << R) - 1)
    bits = list(range(R))
    d_f5,    _ = anf_degree(lambda v: f5(c5, v), bits, base)
    d_f7,    _ = anf_degree(lambda v: f7(c7, v), bits, base)
    d_xor,   _ = anf_degree(lambda v: f5(c5, v ^ t), bits, base)
    d_add,   _ = anf_degree(lambda v: f5(c5, add64(v, t)), bits, base)
    d_add3,  _ = anf_degree(lambda v: f3(c3, add64(v, t)), bits, base)
    # cube placed at random higher bits, twist word with a random lowest set bit j0 <= 50
    j0 = random.randrange(0, 51)
    t2 = (random.getrandbits(64) | 1) << j0 & MASK
    bits2 = list(range(j0, j0 + R))
    base2 = random.getrandbits(64) & ~sum(1 << i for i in bits2)
    d_add_j0, _ = anf_degree(lambda v: f5(c5, add64(v, t2)), bits2, base2)
    # cube strictly below j0 (sigma is affine there): expect <= 2
    if j0 >= R:
        d_below, _ = anf_degree(lambda v: f5(c5, add64(v, t2)), list(range(R)), base2 & ~((1 << R) - 1))
    else:
        d_below = None
    rows.append((d_f5, d_f7, d_xor, d_add, d_add3, j0, d_add_j0, d_below))
print("  trial  f5  f7  f5(v^t)  f5(v+t)  f3(v+t) | j0  f5(v+t2) on bits j0..j0+9  | f5(v+t2) on bits 0..9 (j0>=10 only)")
for i, r_ in enumerate(rows):
    print(f"  {i:5d}  {r_[0]:2d}  {r_[1]:2d}  {r_[2]:7d}  {r_[3]:7d}  {r_[4]:7d} | {r_[5]:2d}  {r_[6]:26d}  | {r_[7]}")
print("  summary: deg f5 in", sorted(set(r_[0] for r_ in rows)), " deg f7 in", sorted(set(r_[1] for r_ in rows)),
      " deg f5(v^t) in", sorted(set(r_[2] for r_ in rows)), " deg f5(v+t) in", sorted(set(r_[3] for r_ in rows)),
      " deg f3(v+t) in", sorted(set(r_[4] for r_ in rows)), " deg f5(v+t2)|bits j0.. in", sorted(set(r_[6] for r_ in rows)),
      " below j0 in", sorted(set(r_[7] for r_ in rows if r_[7] is not None)))

print("=== carry/bit ANF (prop:ph:twist-bits), exhaustive over 8-bit v and t ===")
def carry_formula(v, t, i):
    s = 0
    for j in range(i):
        term = (v >> j & 1) & (t >> j & 1)
        for l in range(j + 1, i):
            term &= ((v >> l) ^ (t >> l)) & 1
        s ^= term
    return s
bad = 0
for v in range(256):
    for t in range(256):
        s = v + t
        carry = 0
        for i in range(9):
            # true carry into position i
            ci = ((v & ((1 << i) - 1)) + (t & ((1 << i) - 1))) >> i
            if ci != carry_formula(v, t, i): bad += 1
        v0, v1, v2 = v & 1, v >> 1 & 1, v >> 2 & 1
        t0, t1, t2 = t & 1, t >> 1 & 1, t >> 2 & 1
        s0 = v0 ^ t0
        s1 = v1 ^ t1 ^ (t0 & v0)
        s2 = v2 ^ t2 ^ (t1 & v1) ^ (t0 & t1 & v0) ^ (t0 & v0 & v1)
        if (s & 1, s >> 1 & 1, s >> 2 & 1) != (s0, s1, s2): bad += 1
print("  carry ANF and s_0, s_1, s_2 formulas: mismatches =", bad)
# degree of s_i in v for fixed t: max(1, i - j0) for t != 0 (i <= 7, exhaustive over 8-bit t)
bad = 0
for t in range(1, 256):
    j0 = lowest_set_bit(t)
    for i in range(8):
        d, _ = anf_degree(lambda v: ((v + t) >> i) & 1, list(range(8)), 0)
        if d != max(1, i - j0): bad += 1
print("  deg_v s_i = max(1, i - j0) for all 8-bit t != 0 and i < 8: mismatches =", bad)

print("=== w_r = XOR_{j<2^r} (t + 2^j0 j) = 2^(j0+r) (m XOR (m+1)),  m = floor(t/2^(j0+r)) mod 2^(64-j0-r) ===")
bad = 0; tested = 0
for _ in range(300):
    j0 = random.randrange(0, 61)
    t = ((random.getrandbits(64) | 1) << j0) & MASK
    for r in range(2, 13):
        if j0 + r > 63: continue
        w = 0
        for j in range(1 << r): w ^= add64(t, j << j0)
        N = 64 - j0 - r
        m = (t >> (j0 + r)) & ((1 << N) - 1)
        m1 = (m + 1) & ((1 << N) - 1)
        pred = ((m ^ m1) << (j0 + r)) & MASK
        tested += 1
        if w != pred or w == 0: bad += 1
print(f"  {tested} (t, r) pairs: mismatches/zeros = {bad}")

print("=== top ANF coefficient on bits j0..j0+r-1 is affine in e_1 with slope w_r (prop:ph:twist-degree) ===")
bad = 0; tested = 0
for _ in range(40):
    j0 = random.randrange(0, 50)
    t = ((random.getrandbits(64) | 1) << j0) & MASK
    r = random.randrange(2, 9)
    bits = list(range(j0, j0 + r))
    e = [random.getrandbits(64) for _ in range(5)]
    e2 = list(e); e2[1] = random.getrandbits(64)
    cA, cB = decode5(e), decode5(e2)
    w = 0
    for j in range(1 << r): w ^= add64(t, j << j0)
    # top coefficient at base 0 = sum over the cube = sum_{j<2^r} f_c(t + 2^j0 j)
    _, topA = anf_degree(lambda v: f5(cA, add64(v, t)), bits, 0)
    _, topB = anf_degree(lambda v: f5(cB, add64(v, t)), bits, 0)
    direct = 0
    for j in range(1 << r): direct ^= f5(cA, add64(t, j << j0))
    tested += 1
    if topA != direct: bad += 1
    if (topA ^ topB) != gfmul(e[1] ^ e2[1], w): bad += 1
print(f"  {tested} random (t, r, e, e') : mismatches = {bad}")
