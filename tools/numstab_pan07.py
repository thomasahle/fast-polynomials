#!/usr/bin/env python3
"""Numerical-stability row for Pan's general real scheme (0.7) (Pan 1966 survey, p. 108, Theorem 3.1),
in the model and with the metrics of tools/numstab.mjs.

CORPUS.  Identical to tools/numstab.mjs, regime 'prescribed coefficients': the LCG (MMIX constants,
seed 12345) is replayed for DEGREES = [7, 15, 31] in that order (the stream is shared across degrees,
as in numstab.mjs); per degree 12 monic polynomials with integer coefficients in [-5, 5] and 3 exact
dyadic points x = k/64, k in [-128, 128].  The replay is cross-checked by recomputing the Horner row and
comparing it digit for digit with notes/numstab_coeffs.json.

MODEL (as in numstab.mjs).  rho: rounding depth of the chain (constants count 1, sums max+1, products
add+1).  A: majorant of the chain (|constants|, |x|, every subtraction an addition) evaluated EXACTLY in
rationals, divided by sum_i |a_i| |x|^i, reported as log10.  err: the chain evaluated in IEEE double
(Python floats; each constant is the correctly rounded double of its exact value) minus the correctly
rounded double of the exact rational P(x), in units of u * sum_i |a_i| |x|^i, u = 2^-53.  Median and max
over the 36 samples.  Overflow -> inf.

SCHEME (0.7), monic P, p0 = x^2, p0' = x^2 + x:
    p1 = x + l1;  q^(s) = (p0' + l_{4s-2})(p0 + l_{4s-1}) + l_{4s};  p_{4s+1} = p_{4s-3} q^(s) + l_{4s+1}
    (s = 1..k);  p_{4k+3} = p_{4k+1}(p0 + l_{4k+2}) + l_{4k+3};  P = p_n, or x p_{n-1} + u_0 for even n.
    floor(n/2) + 1 multiplications, n + 1 additions.

DECODER (top-down; the structure of Pan's Lemmas 3.3-3.5, see tools/pan07_check.py for the identities):
  * pair stage (degree 4k+3): p = E(x^2) + x O(x^2); every REAL root y0 of O (monic, odd degree 2k+1,
    so one exists) gives p - E(y0) = (x^2 - y0) r: l_{4k+2} = -y0, l_{4k+3} = E(y0).  y0 is a real
    algebraic number: roots of O by mpmath.polyroots at 60 digits, real ones polished by Newton.
  * quartic stage (degree 4s+1, s >= 2): a REAL t such that p - t = q4 r with q4 = x^4 + x^3 + ...
    real, i.e. a conjugation-closed 4-subset of the roots of p - t with sum -1 (Lemma 3.3 proves one
    exists by an intermediate-value argument; it gives no formula).  Numerically: a scan in t (log-spaced
    grid, both signs, |t| <= max(1e8, 1e3 max|coeff|)) with numpy.roots and the closed 4-subset sums at every probe; grid
    intervals where the count of subset sums below -1 changes, or where the nearest sum changes sign
    continuously, are bisected in double on the nearest subset sum; a candidate is accepted when the
    4-subset is closed and the double-precision division remainder is small; it is then REFINED at 60
    digits by Newton on g(t) = Re(sum of the 4 tracked roots) + 1 (g'(t) = Re(sum 1/p'(x_i))), each root
    polished by Newton on p(x) - t, and accepted only if |g| < 1e-50 and the exact-arithmetic remainder
    of (p - t)/q4 is < 1e-45 relative.  Up to MAXC candidates (smallest |t|) per stage are followed.
    Then l_{4s-1} = b3, l_{4s-2} = b2 - b3, l_{4s} = b4 - l_{4s-2} l_{4s-1}, l_{4s+1} = t (Todd).
  * stage 1 (degree 5): rational: l1 = u4 - 1, l5 = p5(-l1), Todd's quartic.
  Every complete decoding is a chain; among all found, the one with the smallest exact majorant at
  |x| = 2 is kept (the same selection rule as the Knuth (12) row of tools/numstab_pan.mjs; Motzkin-Eve's
  compiler in the website similarly searches its peel order).  The constants are converted from
  60-digit values to doubles once (correctly rounded through an exact Fraction), so, as for the
  Motzkin-Eve row, the error column contains the preprocessing error of the rounded constants; that
  part is measured separately as 'preprocessing residual': the chain with the double constants
  evaluated EXACTLY (rationals) against P at 65 points x = k/16, in units of u * sum |a_i||x|^i.
  This is a numeric real-algebraic preprocessing, not a rational one; the search is heuristic and a
  failure to find t is a limitation of the scan, not a counterexample to Lemma 3.3.

Run:  python3 tools/numstab_pan07.py [degrees=7,15] [out_dir] [maxc=2] [G=3000]
Writes <out_dir>/numstab_pan07_<degrees>.json.
"""
import sys, os, json, time, itertools, math
from fractions import Fraction
import numpy as np
from mpmath import mp, mpf, mpc, polyroots

mp.dps = 60
U = 2.0 ** -53
MASK = (1 << 64) - 1
T_SPAN = 1e8

# ---------------- corpus replay (tools/numstab.mjs) ----------------
class LCG:
    def __init__(self, seed=12345): self.s = seed
    def rnd(self):
        self.s = (self.s * 6364136223846793005 + 1442695040888963407) & MASK
        return self.s
    def rint(self, lo, hi): return lo + self.rnd() % (hi - lo + 1)

def corpus(degrees=(7, 15, 31), trials=12):
    g = LCG(12345); out = {}
    for n in degrees:
        out[n] = []
        for trial in range(trials):
            coeffs = [Fraction(g.rint(-5, 5)) for _ in range(n)] + [Fraction(1)]
            if all(c == 0 for c in coeffs[:n]): continue
            xs = [Fraction(g.rint(-128, 128), 64) for _ in range(3)]
            out[n].append((trial, coeffs, xs))
    return out

# ---------------- exact helpers ----------------
def exact_eval(coeffs, x):
    acc = Fraction(0)
    for c in reversed(coeffs): acc = acc * x + c
    return acc
def sum_abs(coeffs, x):
    ax = abs(x); acc = Fraction(0); xp = Fraction(1)
    for c in coeffs: acc += abs(c) * xp; xp *= ax
    return acc
def err_units(approx, coeffs, x):
    if not math.isfinite(approx): return float('inf')
    return abs(approx - float(exact_eval(coeffs, x))) / (U * float(sum_abs(coeffs, x)))
def log10_frac(f):
    if f == 0: return -float('inf')
    n, d = abs(f.numerator), f.denominator
    return (len(str(n)) - 1 + math.log10(int(str(n)[:15]) / 10 ** (min(len(str(n)), 15) - 1))) - \
           (len(str(d)) - 1 + math.log10(int(str(d)[:15]) / 10 ** (min(len(str(d)), 15) - 1)))

def horner_double(coeffs, xd):
    n = len(coeffs) - 1
    acc = xd + float(coeffs[n - 1])
    for i in range(n - 2, -1, -1): acc = acc * xd + float(coeffs[i])
    return acc

# ---------------- the (0.7) chain ----------------
def stages(n):
    m = n - 1 if n % 2 == 0 else n
    k = (m - 1) // 4 if m % 4 == 1 else (m - 3) // 4
    return m, k
def chain07(n, lam, a_n, x, add, mul, cst):
    """Generic evaluation of scheme (0.7).  lam: dict j -> constant (float); cst maps a constant into the
    arithmetic domain (identity / Fraction / abs Fraction), x already in the domain."""
    m, k = stages(n)
    s = mul(x, x); s1 = add(s, x)
    acc = add(x, cst(lam[1]))
    for st in range(1, k + 1):
        q = add(mul(add(s1, cst(lam[4 * st - 2])), add(s, cst(lam[4 * st - 1]))), cst(lam[4 * st]))
        acc = add(mul(acc, q), cst(lam[4 * st + 1]))
    if m % 4 == 3:
        acc = add(mul(acc, add(s, cst(lam[4 * k + 2]))), cst(lam[4 * k + 3]))
    if n % 2 == 0:
        acc = add(mul(x, acc), cst(a_n))
    return acc
def eval_double(n, lam, a_n, xd):
    return chain07(n, lam, a_n, xd, lambda a, b: a + b, lambda a, b: a * b, lambda c: float(c))
def eval_exact(n, lam, a_n, x):
    return chain07(n, lam, a_n, x, lambda a, b: a + b, lambda a, b: a * b, lambda c: Fraction(c))
def eval_majorant(n, lam, a_n, x):
    return chain07(n, lam, a_n, abs(x), lambda a, b: a + b, lambda a, b: a * b, lambda c: abs(Fraction(c)))
def rho07(n):
    # the rules of numstab.mjs rhoLines: constants 1, x 0, sums max+1, products add+1
    class R:
        def __init__(s, v): s.v = v
    add = lambda a, b: R(max(a.v, b.v) + 1); mul = lambda a, b: R(a.v + b.v + 1)
    m, k = stages(n)
    lam = {j: 1 for j in range(1, n + 1)}
    return chain07(n, lam, 1, R(0), add, mul, lambda c: R(1)).v

# ---------------- mp polynomial helpers (ascending lists) ----------------
def fr_to_mp(f): return mpf(f.numerator) / mpf(f.denominator)
def mp_to_fraction(v):
    sign, man, exp, bc = v._mpf_
    if man == 0: return Fraction(0)
    f = Fraction(man) * (Fraction(2) ** exp)
    return -f if sign else f
def mp_to_double(v):                  # exact Fraction -> correctly rounded double (Python's Fraction.__float__)
    return float(mp_to_fraction(v))
def mp_polyval(p, z):
    acc = p[-1]
    for c in reversed(p[:-1]): acc = acc * z + c
    return acc
def mp_polyder(p): return [i * p[i] for i in range(1, len(p))]
def mp_divmod_monic(p, q):
    """p = quot * q + rem with q monic (ascending mp lists)."""
    p = list(p); dq = len(q) - 1; quot = [mpf(0)] * (len(p) - dq)
    for i in range(len(p) - 1, dq - 1, -1):
        c = p[i]; quot[i - dq] = c
        for j in range(dq + 1): p[i - dq + j] -= c * q[j]
    return quot, p[:dq]
def mp_polymul(a, b):
    out = [mpf(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): out[i + j] += x * y
    return out

def newton_root(p, dp, z, t, real=False, iters=80):
    """Polish a root of p(x) - t from z (mpf or mpc)."""
    for _ in range(iters):
        f = mp_polyval(p, z) - t; g = mp_polyval(dp, z)
        if g == 0: return None
        dz = f / g; z = z - dz
        if abs(dz) < mpf(10) ** (-56) * (1 + abs(z)): return z
    return z if abs(mp_polyval(p, z) - t) < mpf(10) ** (-45) * (1 + abs(t)) else None

# ---------------- pair stage ----------------
def pair_candidates(p):
    """p: ascending mp, monic, degree 4k+3.  Yields (y0, t, r) for every real root y0 of the odd part."""
    m = len(p) - 1
    E = [p[i] for i in range(0, m + 1, 2)]
    O = [p[i] for i in range(1, m + 1, 2)]           # monic, degree (m-1)/2
    try:
        roots = polyroots(O[::-1], maxsteps=400, extraprec=300)
    except Exception:
        roots = polyroots(O[::-1], maxsteps=2000, extraprec=600)
    dO = mp_polyder(O)
    reals = []
    for z in roots:
        if abs(z.imag) < mpf(10) ** (-30) * (1 + abs(z)):
            y = newton_root(O, dO, mpf(z.real), mpf(0), real=True)
            if y is not None and abs(mp_polyval(O, y)) < mpf(10) ** (-50) * (1 + abs(y) ** len(dO)):
                if all(abs(y - w) > mpf(10) ** (-40) * (1 + abs(y)) for w in reals): reals.append(y)
    out = []
    for y0 in reals:
        t = mp_polyval(E, y0)
        q = list(p); q[0] -= t
        r, rem = mp_divmod_monic(q, [-y0, mpf(0), mpf(1)])
        scale = max(abs(c) for c in q)
        if max(abs(c) for c in rem) < mpf(10) ** (-45) * scale:
            out.append((y0, t, r))
    return out

# ---------------- quartic stage ----------------
_COMBOS = {}
def combos4(m):
    if m not in _COMBOS: _COMBOS[m] = np.array(list(itertools.combinations(range(m), 4)))
    return _COMBOS[m]

def probe_double(pf_desc, t, C):
    """Roots of p - t (double), closed 4-subset sums.  Returns (roots, mask_closed, f=sum+1 (nan where not closed))."""
    q = pf_desc.copy(); q[-1] -= t
    r = np.roots(q)
    D = np.abs(r[:, None] - np.conj(r)[None, :])
    partner = np.argmin(D, axis=1)
    pc = partner[C]
    closed = np.all(np.sort(pc, axis=1) == C, axis=1)
    sums = r[C].sum(axis=1).real + 1.0
    f = np.where(closed, sums, np.nan)
    return r, closed, f

def quartic_candidates_double(p, G=3000, maxc=2):
    m = len(p) - 1
    pf = np.array([float(mp_to_double(c)) for c in p])
    pf_desc = pf[::-1].copy()
    C = combos4(m)
    # scan span: the crossing t is on the scale of the coefficients of p (the quotients of the previous stages
    # can have constant terms ~1e9 at n = 31), so the span is at least 1e3 * max |coefficient|
    span = max(T_SPAN, 1e3 * float(np.max(np.abs(pf))))
    us = np.linspace(0.0, math.log10(1 + span), G)
    pos = 10.0 ** us - 1.0
    ts = np.concatenate([-pos[::-1], pos[1:]])
    NB, NEAR, IDX = [], [], []
    for t in ts:
        _, closed, f = probe_double(pf_desc, t, C)
        if not closed.any(): NB.append(-1); NEAR.append(np.nan); IDX.append(-1); continue
        NB.append(int(np.sum(f[closed] < 0)))
        i = int(np.nanargmin(np.abs(f))); NEAR.append(float(f[i])); IDX.append(i)
    cands = []
    for i in range(len(ts) - 1):
        if NB[i] < 0 or NB[i + 1] < 0: continue
        near_a, near_b = NEAR[i], NEAR[i + 1]
        if NB[i] != NB[i + 1] or (near_a * near_b <= 0 and abs(near_a - near_b) < 0.5 + 0.1 * (abs(near_a) + abs(near_b))):
            cands.append((abs(near_a) + abs(near_b), ts[i], ts[i + 1]))
    cands.sort()
    found = []
    def nearest(t):
        r, closed, f = probe_double(pf_desc, t, C)
        if not closed.any(): return None, None, None
        i = int(np.nanargmin(np.abs(f))); return float(f[i]), i, r
    for _, lo, hi in cands[:24]:
        flo, _, _ = nearest(lo); fhi, _, _ = nearest(hi)
        if flo is None or fhi is None or flo * fhi > 0: continue
        for _ in range(120):
            mid = 0.5 * (lo + hi)
            fm, im, rm = nearest(mid)
            if fm is None: break
            if fm * flo <= 0: hi = mid
            else: lo, flo = mid, fm
            if hi - lo < 1e-14 * (1 + abs(mid)): break
        t = 0.5 * (lo + hi)
        fm, im, rm = nearest(t)
        if fm is None or abs(fm) > 1e-6: continue
        sub = rm[C[im]]
        q4 = np.poly(sub)
        if np.max(np.abs(q4.imag)) > 1e-6 * (1 + np.max(np.abs(q4))): continue
        q4 = q4.real
        if abs(q4[1] - 1.0) > 1e-5: continue
        qq = pf_desc.copy(); qq[-1] -= t
        _, rem = np.polydiv(qq, q4)
        if np.max(np.abs(rem)) > 1e-5 * np.max(np.abs(qq)): continue
        if any(abs(t - t2) < 1e-7 * (1 + abs(t)) for t2, _ in found): continue
        found.append((t, sub))
    found.sort(key=lambda e: abs(e[0]))
    return found[:maxc], len(cands)

def refine_quartic(p, t0, sub):
    """60-digit refinement of (t, closed 4-subset) by Newton on g(t) = Re(sum roots) + 1."""
    dp = mp_polyder(p)
    tol = 1e-9 * (1 + max(abs(z) for z in sub))
    units = []; used = set()
    for i, z in enumerate(sub):
        if i in used: continue
        if abs(z.imag) <= tol:
            units.append(['real', mpf(float(z.real))]); used.add(i)
        else:
            j = min((j for j in range(4) if j != i and j not in used), key=lambda j: abs(sub[j] - np.conj(z)), default=None)
            if j is None or abs(sub[j] - np.conj(z)) > 1e-6 * (1 + abs(z)): return None
            units.append(['pair', mpc(float(z.real), float(abs(z.imag)))]); used.add(i); used.add(j)
    t = mpf(t0)
    for it in range(60):
        new = []
        for kind, z in units:
            zz = newton_root(p, dp, z, t, real=(kind == 'real'))
            if zz is None: return None
            if kind == 'pair' and abs(zz.imag) < mpf(10) ** (-50) * (1 + abs(zz)): return None   # pair collapsed onto the real axis
            new.append([kind, zz])
        units = new
        g = mpf(1); gp = mpf(0)
        for kind, z in units:
            d = mp_polyval(dp, z)
            if d == 0: return None
            if kind == 'pair': g += 2 * z.real; gp += 2 * (1 / d).real
            else: g += z; gp += 1 / d
        if abs(g) < mpf(10) ** (-55): break
        if gp == 0: return None
        t = t - g / gp
    if abs(g) > mpf(10) ** (-50): return None
    q4 = [mpf(1)]
    for kind, z in units:
        if kind == 'pair': q4 = mp_polymul(q4, [abs(z) ** 2, -2 * z.real, mpf(1)])
        else: q4 = mp_polymul(q4, [-z, mpf(1)])
    if abs(q4[3] - 1) > mpf(10) ** (-50): return None
    q = list(p); q[0] -= t
    r, rem = mp_divmod_monic(q, q4)
    scale = max(abs(c) for c in q)
    if max(abs(c) for c in rem) > mpf(10) ** (-45) * scale: return None
    return t, q4, r

def quartic_candidates(p, G, maxc):
    dbl, ncand = quartic_candidates_double(p, G, maxc)
    out = []
    for t0, sub in dbl:
        ref = refine_quartic(p, t0, sub)
        if ref is not None: out.append(ref)
    return out, ncand

# ---------------- stage 1 ----------------
def stage1(p):
    """p: ascending mp monic quintic.  Returns dict l1..l5 (mp)."""
    l1 = p[4] - 1
    l5 = mp_polyval(p, -l1)
    q = list(p); q[0] -= l5
    q4, rem = mp_divmod_monic(q, [l1, mpf(1)])
    assert max(abs(c) for c in rem) < mpf(10) ** (-50) * (1 + max(abs(c) for c in q))
    assert abs(q4[4] - 1) < mpf(10) ** (-50) and abs(q4[3] - 1) < mpf(10) ** (-50)
    l3 = q4[1]; l2 = q4[2] - q4[1]; l4 = q4[0] - l2 * l3
    return {1: l1, 2: l2, 3: l3, 4: l4, 5: l5}

# ---------------- full decoder ----------------
def decode_all(coeffs, n, G=3000, maxc=2, max_pair=None, max_sols=64):
    m, k = stages(n)
    a_n = coeffs[0] if n % 2 == 0 else None
    p = [fr_to_mp(c) for c in (coeffs[1:] if n % 2 == 0 else coeffs)]
    sols = []; log = []
    def rec(p, lam, path):
        if len(sols) >= max_sols: return
        mm = len(p) - 1
        if mm % 4 == 3:
            kk = (mm - 3) // 4
            cands = pair_candidates(p)
            cands.sort(key=lambda e: abs(e[1]))
            if max_pair: cands = cands[:max_pair]
            log.append(f'pair stage (degree {mm}): {len(cands)} real roots of O')
            for y0, t, r in cands:
                lam2 = dict(lam); lam2[4 * kk + 2] = -y0; lam2[4 * kk + 3] = t
                rec(r, lam2, path + [f'y0={mp_to_double(y0):.6g}'])
        elif mm == 5:
            lam2 = dict(lam); lam2.update(stage1(p))
            sols.append((lam2, path))
        else:
            s = (mm - 1) // 4
            cands, ncand = quartic_candidates(p, G, maxc)
            log.append(f'quartic stage s={s} (degree {mm}): {ncand} grid candidates, {len(cands)} refined')
            for t, q4, r in cands:
                b2, b3, b4 = q4[2], q4[1], q4[0]
                lam2 = dict(lam)
                lam2[4 * s - 1] = b3; lam2[4 * s - 2] = b2 - b3; lam2[4 * s] = b4 - (b2 - b3) * b3; lam2[4 * s + 1] = t
                rec(r, lam2, path + [f't={mp_to_double(t):.6g}'])
    rec(p, {}, [])
    return sols, a_n, log

def measure_poly(n, coeffs, xs, G, maxc, max_pair):
    t0 = time.time()
    sols, a_n, log = decode_all(coeffs, n, G=G, maxc=maxc, max_pair=max_pair)
    if not sols:                                   # retry once with a finer grid and a wider beam
        log.append(f'retry: G={2 * G}, maxc={max(2, maxc)}, all real roots at the pair stage')
        sols, a_n, log2 = decode_all(coeffs, n, G=2 * G, maxc=max(2, maxc), max_pair=None)
        log += log2
    if not sols:
        return None, log, time.time() - t0
    best = None; majs = []
    for lam_mp, path in sols:
        lam = {j: mp_to_double(v) for j, v in lam_mp.items()}
        maj2 = eval_majorant(n, lam, a_n, Fraction(2))
        cand = {'lam': lam, 'path': path, 'logMaj2': log10_frac(maj2)}
        majs.append(cand['logMaj2'])
        if best is None or cand['logMaj2'] < best['logMaj2']: best = cand
    best['logMaj2_range'] = [min(majs), max(majs)]          # spread of the exact majorant at |x| = 2 over all decodings found
    lam = best['lam']
    # harness metrics at the corpus points
    As, errs = [], []
    for x in xs:
        xd = float(x)
        approx = eval_double(n, lam, a_n, xd)
        maj = eval_majorant(n, lam, a_n, x)
        As.append(log10_frac(maj) - log10_frac(sum_abs(coeffs, x)))
        errs.append(err_units(approx, coeffs, x))
    # preprocessing residual: exact evaluation of the chain with the double constants vs P at 65 points
    resid = 0.0
    for kx in range(-32, 33):
        x = Fraction(kx, 16)
        S = sum_abs(coeffs, x)
        if S == 0: continue                      # x = 0 with a_0 = 0: the unit u*S is 0; point skipped
        v = eval_exact(n, lam, a_n, x)
        resid = max(resid, float(abs(v - exact_eval(coeffs, x)) / S) / U)
    best.update({'A': As, 'err': errs, 'resid_u': resid, 'nsols': len(sols),
                 'maxAbsLam': max(abs(v) for v in lam.values()), 'secs': time.time() - t0})
    return best, log, time.time() - t0

def summarize(a):
    s = sorted(a); return {'median': s[len(s) // 2], 'max': s[-1]}

def main():
    degrees = [int(d) for d in (sys.argv[1] if len(sys.argv) > 1 else '7,15').split(',')]
    out_dir = sys.argv[2] if len(sys.argv) > 2 else '.'
    maxc = 2; G = 3000; max_pair = None
    for a in sys.argv[3:]:
        if a.startswith('maxc='): maxc = int(a[5:])
        elif a.startswith('G='): G = int(a[2:])
        elif a.startswith('maxpair='): max_pair = int(a[8:])
    corp = corpus((7, 15, 31), 12)
    # cross-check of the corpus replay against the published Horner row
    ref = {}
    try:
        here = os.path.dirname(os.path.abspath(__file__))
        ref = json.load(open(os.path.join(here, '..', 'notes', 'numstab_coeffs.json')))
    except Exception: pass
    results = {}
    for n in (7, 15, 31):
        herr = [err_units(horner_double(c, float(x)), c, x) for _, c, xs in corp[n] for x in xs]
        s = summarize(herr)
        rj = ref.get(str(n), {}).get('Horner', {}).get('err', {})
        print(f'[replay check] n={n}: Horner err med={s["median"]!r} max={s["max"]!r}  notes/numstab_coeffs.json: med={rj.get("median")!r} max={rj.get("max")!r}  '
              f'{"MATCH" if rj and rj.get("median") == s["median"] and rj.get("max") == s["max"] else "MISMATCH"}')
        results.setdefault(str(n), {})['Horner'] = {'rho': None, 'err': s, 'samples': len(herr)}
    for n in degrees:
        rows = corp[n]
        As, errs, per = [], [], []
        rho = rho07(n)
        print(f'=== Pan (0.7), n={n}: {len(rows)} corpus polynomials, rho={rho}, {n // 2 + 1} multiplications; G={G}, maxc={maxc}, maxpair={max_pair} ===')
        for trial, coeffs, xs in rows:
            best, log, secs = measure_poly(n, coeffs, xs, G, maxc, max_pair)
            if best is None:
                print(f' trial {trial}: P={[int(c) for c in coeffs]}  FAILED (no complete decoding found by the scan)  [{secs:.1f}s]')
                for l in log: print('    ' + l)
                per.append({'trial': trial, 'coeffs': [str(c) for c in coeffs], 'xs': [str(x) for x in xs], 'failed': True, 'log': log})
                continue
            As += best['A']; errs += best['err']
            print(f' trial {trial}: P={[int(c) for c in coeffs]}  sols={best["nsols"]} chosen={best["path"]}  log10 maj(2)={best["logMaj2"]:.1f}  max|lam|={best["maxAbsLam"]:.3g}  '
                  f'log10A={[round(a, 1) for a in best["A"]]}  err/(uS)={[f"{e:.2e}" for e in best["err"]]}  preproc resid/u={best["resid_u"]:.2e}  [{secs:.1f}s]')
            for l in log: print('    ' + l)
            per.append({'trial': trial, 'coeffs': [str(c) for c in coeffs], 'xs': [str(x) for x in xs], 'lam': {str(j): repr(v) for j, v in sorted(best['lam'].items())},
                        'path': best['path'], 'nsols': best['nsols'], 'logMaj2': best['logMaj2'], 'logMaj2_range': best['logMaj2_range'], 'A': best['A'], 'err': best['err'], 'resid_u': best['resid_u'], 'secs': secs, 'log': log})
        if As:
            r = {'rho': rho, 'logA': summarize(As), 'err': summarize(errs), 'samples': len(errs),
                 'overflow': sum(1 for e in errs if not math.isfinite(e)), 'skipped': sum(1 for p in per if p.get('failed')), 'per': per}
            print(f'n={n} Pan (0.7)        rho={rho:3d}  log10A med={r["logA"]["median"]:.1f} max={r["logA"]["max"]:.1f}  err/(uS) med={r["err"]["median"]:.2e} max={r["err"]["max"]:.2e}  samples={r["samples"]} skipped={r["skipped"]}')
        else:
            r = {'rho': rho, 'samples': 0, 'skipped': len(per), 'per': per}
            print(f'n={n} Pan (0.7): no polynomial decoded')
        results.setdefault(str(n), {})['Pan (0.7)'] = r
        sys.stdout.flush()
    tag = ','.join(map(str, degrees))
    path = os.path.join(out_dir, f'numstab_pan07_{tag}.json')
    json.dump(results, open(path, 'w'), indent=1, default=lambda o: str(o))
    print('wrote', path)

if __name__ == '__main__':
    main()
