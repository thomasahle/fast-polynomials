#!/usr/bin/env python3
"""Prototype decoder for Pan's real everywhere-defined scheme (0.7) (Pan 1966 survey, p. 108 and
Theorem 3.1, pp. 123-125), to settle whether the scheme is implementable for general degree.

SCHEME (0.7), transcribed from the survey (p. 108), monic input, P(x) = sum_l a_l x^{n-l}, a_0 = 1:
    p0  = x * x,     p0' = p0 + x,     p1 = x + lam1,
    p4^(s) = (p0' + lam_{4s-2}) (p0 + lam_{4s-1}) + lam_{4s}            (s = 1, ..., k)
    p_{4s+1} = p_{4s-3} * p4^(s) + lam_{4s+1}                             (s = 1, ..., k)
    p_{4k+3} = p_{4k+1} (p0 + lam_{4k+2}) + lam_{4k+3}
    P = p_n (n = 4k+1, 4k+3);   P = x p_{n-1} + a_n (n = 4k+2, 4k+4).
Multiplications for monic P: 1 + 2k (+1 for n = 4k+3) (+1 for even n) = floor(n/2) + 1 for every n.

WHAT THE DECODER HAS TO SOLVE (this is the whole content of Pan's Theorem 3.1 / Lemmas 3.3-3.5):
  stage s (top down, s = k, ..., 2): given the real monic p = p_{4s+1} of degree 4s+1, find a REAL t
      such that p - t = q4 * r with q4 = x^4 + x^3 + b2 x^2 + b3 x + b4 REAL (x^3-coefficient 1).
      Lemma 3.3 (root-continuity, "pipe and wires") proves that such t exists for every real p:
      among the 4-subsets of roots of p - t that are unions of two "pairs" (a conjugate pair, or two
      real roots), some subset-sum S(t) is continuous in t and runs from -inf to +inf, so S(t) = -1
      has a real solution.  This is an intermediate-value argument: existence is proved by exhibiting
      a continuous branch, not by a formula, and the survey gives no algorithm beyond it.
  stage 1: p_5 - lam5 = (x + lam1) * q4 forces lam1 = u4 - 1 (x^3-coefficient of the quotient must be 1)
      and lam5 = p_5(1 - u4): RATIONAL and everywhere defined.
  every quartic q4 = x^4 + x^3 + b2 x^2 + b3 x + b4 is (x^2 + x + lam)(x^2 + lam') + lam'' with
      lam' = b3, lam = b2 - b3, lam'' = b4 - lam lam' (Lemma 3.5, Todd's scheme): RATIONAL.
  n = 4k+3: first find real t with p - t = (x^2 + lam) * r (two roots summing to 0; Lemma 3.4).

IMPLEMENTATION HERE (numeric, floating point; a demonstration, not a certified decoder):
  * roots of p - t by numpy.roots on a grid of t; for each t enumerate the conjugation-closed
    4-subsets (pair of conjugate pairs / conjugate pair + two reals / four reals) and their real sums;
  * detect a grid interval where some subset-sum crosses -1 (subsets are matched across the interval
    by sorting the roots), then bisect on that subset's sum to 1e-13;
  * verify: q4 = prod (x - r), r in S, has real coefficients and x^3-coefficient 1; the floating-point
    division (p - t) / q4 has a small remainder; the emitted lam's are all real.
  * recurse on the quotient r (degree 4s-3) down to stage 1; then evaluate the (0.7) chain at
    sample points against Horner.
It is NOT rational (t is an algebraic number defined implicitly by a root-sum condition), it needs the
complete root set of p - t at every probe, and the branch bookkeeping near collisions of roots is where
a production implementation would have to work (Sturm-exact isolation cannot be used directly because
the condition couples several roots).  Output states, for each trial, the found t's and the maximum
relative error of the chain at 41 points in [-2, 2].

Run: python3 tools/pan07_proto.py [degrees, default 9,13] [trials, default 8]
"""
import sys, itertools
import numpy as np

rng = np.random.default_rng(20260905)

def roots_desc(p_asc):
    return np.roots(p_asc[::-1])

def closed_subsets(roots, tol=1e-9):
    """Conjugation-closed 4-subsets as index tuples, with their (real) sums."""
    idx = list(range(len(roots)))
    reals = [i for i in idx if abs(roots[i].imag) <= tol * (1 + abs(roots[i]))]
    cplx = [i for i in idx if i not in reals]
    # conjugate pairs among complex roots (greedy nearest conjugate)
    pairs = []
    used = set()
    for i in cplx:
        if i in used: continue
        best, bd = None, np.inf
        for j in cplx:
            if j == i or j in used: continue
            d = abs(roots[j] - np.conj(roots[i]))
            if d < bd: bd, best = d, j
        if best is None: continue
        used.add(i); used.add(best); pairs.append((i, best))
    out = []
    for a, b in itertools.combinations(pairs, 2):
        out.append((a + b, (roots[a[0]] + roots[a[1]] + roots[b[0]] + roots[b[1]]).real))
    for a in pairs:
        for r1, r2 in itertools.combinations(reals, 2):
            out.append((a + (r1, r2), (roots[a[0]] + roots[a[1]] + roots[r1] + roots[r2]).real))
    for q in itertools.combinations(reals, 4):
        out.append((q, sum(roots[i] for i in q).real))
    return out

def find_t_quartic(p, M=-1.0, span=None, grid=4001):
    """Real t with p - t having a real quartic factor whose roots sum to M.  Returns (t, S-roots).
    Candidate intervals: grid points between which the number of closed 4-subsets with sum < M
    changes (a sum crossed M, or subsets were reorganised at a root collision -- the bisection
    below rejects the latter).  Bisection: on the subset sum nearest to M at each probe."""
    if span is None: span = 40.0 * (1 + max(abs(c) for c in p))
    ts = np.linspace(-span, span, grid)
    def probe(t):
        q = p.copy(); q[0] -= t
        r = roots_desc(q)
        return closed_subsets(r), r
    prev = None
    cands = []
    for t in ts:
        subs, r = probe(t)
        below = sum(1 for _, s in subs if s < M)
        near = min(subs, key=lambda e: abs(e[1] - M))[1] if subs else None
        if prev is not None and (below != prev[1]) and near is not None and prev[2] is not None:
            cands.append((prev[0], t, abs(near - M) + abs(prev[2] - M)))
        prev = (t, below, near)
    cands.sort(key=lambda c: c[2])
    def sum_near(t):
        subs, r = probe(t)
        S, s = min(subs, key=lambda e: abs(e[1] - M))
        return s, S, r
    for lo, hi, _ in cands[:12]:
        slo, _, _ = sum_near(lo); shi, _, _ = sum_near(hi)
        if (slo - M) * (shi - M) > 0: continue
        for _ in range(200):
            mid = 0.5 * (lo + hi)
            sm, S, r = sum_near(mid)
            if (sm - M) * (slo - M) <= 0: hi = mid
            else: lo, slo = mid, sm
            if hi - lo < 1e-13 * (1 + abs(mid)): break
        t = 0.5 * (lo + hi)
        sm, S, r = sum_near(t)
        if abs(sm - M) < 1e-7:
            return t, r[list(S)]
    return None, None

def polydiv(p, q):
    """p = quot * q + rem, ascending coefficient lists (floats)."""
    p = list(p); dq = len(q) - 1; quot = [0.0] * (len(p) - dq)
    for i in range(len(p) - 1, dq - 1, -1):
        c = p[i] / q[dq]; quot[i - dq] = c
        for j in range(dq + 1): p[i - dq + j] -= c * q[j]
    return quot, p[:dq]

def decode07(P):
    """P ascending, monic, odd degree n = 4k+1 or 4k+3.  Returns dict of lam's and a log."""
    n = len(P) - 1
    lam = {}
    log = []
    p = [float(c) for c in P]
    if n % 4 == 3:
        # p - t = (x^2 + l) * r : two roots summing to 0
        t, S = find_t_quartic_pair(p)
        if t is None: t, S = find_t_quartic_pair(p, span=400.0 * (1 + max(abs(c) for c in p)), grid=16001)   # retry: wider, finer
        if t is None: raise RuntimeError('4k+3 stage: no real t found (grid search; not a counterexample to Lemma 3.4)')
        k = (n - 3) // 4
        l = (S[0] * S[1]).real
        lam[4 * k + 2] = l; lam[4 * k + 3] = t
        q = p.copy(); q[0] -= t
        r, rem = polydiv(q, [l, 0.0, 1.0])
        log.append(f'  stage 4k+3: t={t:.6g}, x^2+{l:.6g}, |rem|={max(abs(c) for c in rem):.1e}')
        p = r
        n -= 2
    k = (n - 1) // 4
    for s in range(k, 1, -1):
        t, S = find_t_quartic(p)
        if t is None: t, S = find_t_quartic(p, span=400.0 * (1 + max(abs(c) for c in p)), grid=16001)   # retry: wider, finer
        if t is None: raise RuntimeError(f'stage s={s}: no real t found (grid search; not a counterexample to Lemma 3.3)')
        q4 = np.poly(S)[::-1].real          # ascending, monic
        q = p.copy(); q[0] -= t
        r, rem = polydiv(q, list(q4))
        b2, b3, b4 = q4[2], q4[1], q4[0]
        lam[4 * s - 1] = b3; lam[4 * s - 2] = b2 - b3; lam[4 * s] = b4 - (b2 - b3) * b3; lam[4 * s + 1] = t
        log.append(f'  stage s={s}: t={t:.6g}, q4 x^3-coeff={q4[3]:.12f}, |rem|={max(abs(c) for c in rem):.1e}, lam={[round(float(lam[j]), 4) for j in (4*s-2, 4*s-1, 4*s, 4*s+1)]}')
        p = r
    # stage 1 (rational): p5 - lam5 = (x + lam1) q4, lam1 = u4 - 1
    u4 = p[4]; lam1 = u4 - 1.0
    lam5 = np.polyval(p[::-1], -lam1)
    q = p.copy(); q[0] -= lam5
    q4, rem = polydiv(q, [lam1, 1.0])
    b2, b3, b4 = q4[2], q4[1], q4[0]
    lam[1] = lam1; lam[3] = b3; lam[2] = b2 - b3; lam[4] = b4 - (b2 - b3) * b3; lam[5] = lam5
    log.append(f'  stage s=1 (rational): lam1={lam1:.6g}, lam5={lam5:.6g}, |rem|={max(abs(c) for c in rem):.1e}')
    return lam, log

def find_t_quartic_pair(p, span=None, grid=4001):
    """Real t with p - t having two roots summing to 0 (a real quadratic factor x^2 + l)."""
    n = len(p) - 1
    if span is None: span = 40.0 * (1 + max(abs(c) for c in p))
    ts = np.linspace(-span, span, grid)
    prev = None
    for t in ts:
        q = p.copy(); q[0] -= t
        r = roots_desc(q)
        reals = [z for z in r if abs(z.imag) <= 1e-9 * (1 + abs(z))]
        cplx = [z for z in r if abs(z.imag) > 1e-9 * (1 + abs(z))]
        sums = [(2 * z.real, (z, np.conj(z))) for z in cplx if z.imag > 0] + [((a + b).real, (a, b)) for a, b in itertools.combinations(reals, 2)]
        best = min(sums, key=lambda e: abs(e[0]))
        if prev is not None and best[0] * prev[1] <= 0 and abs(best[0] - prev[1]) < 1.0 + abs(best[0]):
            lo, hi, slo = prev[0], t, prev[1]
            for _ in range(200):
                mid = 0.5 * (lo + hi)
                q = p.copy(); q[0] -= mid
                r = roots_desc(q)
                reals = [z for z in r if abs(z.imag) <= 1e-9 * (1 + abs(z))]
                cplx = [z for z in r if abs(z.imag) > 1e-9 * (1 + abs(z))]
                sums = [(2 * z.real, (z, np.conj(z))) for z in cplx if z.imag > 0] + [((a + b).real, (a, b)) for a, b in itertools.combinations(reals, 2)]
                bm = min(sums, key=lambda e: abs(e[0]))
                if bm[0] * slo <= 0: hi = mid
                else: lo, slo = mid, bm[0]
                if hi - lo < 1e-13 * (1 + abs(mid)): break
            if abs(bm[0]) < 1e-7: return 0.5 * (lo + hi), bm[1]
        prev = (t, best[0])
    return None, None

def eval07(lam, n, x):
    p0 = x * x; p0p = p0 + x
    acc = x + lam[1]
    k = (n - 1) // 4 if n % 4 == 1 else (n - 3) // 4
    for s in range(1, k + 1):
        q4 = (p0p + lam[4 * s - 2]) * (p0 + lam[4 * s - 1]) + lam[4 * s]
        acc = acc * q4 + lam[4 * s + 1]
    if n % 4 == 3:
        acc = acc * (p0 + lam[4 * k + 2]) + lam[4 * k + 3]
    return acc

def main():
    degs = [int(d) for d in (sys.argv[1] if len(sys.argv) > 1 else '9,13').split(',')]
    trials = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    for n in degs:
        ok = 0
        print(f'=== degree {n}: {trials} random monic polynomials, integer coefficients in [-5,5] ===')
        for tr in range(trials):
            P = [int(c) for c in rng.integers(-5, 6, size=n)] + [1]
            try:
                lam, log = decode07(P)
            except RuntimeError as e:
                print(f' trial {tr}: P={P}  FAILED ({e})'); continue
            xs = np.linspace(-2, 2, 41)
            errs = []
            for x in xs:
                want = np.polyval(P[::-1], x)
                got = eval07(lam, n, x)
                scale = sum(abs(c) * max(1, abs(x)) ** i for i, c in enumerate(P))
                errs.append(abs(got - want) / max(abs(want), 1e-3 * scale))
            e = max(errs)
            ok += e < 1e-6
            print(f' trial {tr}: P={P}  max rel err of (0.7) chain = {e:.2e}  max|lam| = {max(abs(v) for v in lam.values()):.3g}')
            for l in log: print(l)
        print(f'degree {n}: {ok}/{trials} decoded with chain error < 1e-6')

if __name__ == '__main__':
    main()
