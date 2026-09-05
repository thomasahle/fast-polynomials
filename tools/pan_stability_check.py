#!/usr/bin/env python3
"""Exact checks for theory.md (Pan's sextic: majorant, blow-up near the hypersurface, scheme (0.7)).

Everything below is an exact symbolic identity (sympy over Q(u0..u5)[alpha, d, t]) or an exact
rational evaluation (Fraction / sympy Rational).  No sampling in floating point enters any
verdict; the few floating-point numbers printed (log10 values) are for comparison with
numstab_pan.log only.  Cases verified are listed by name; the final line prints ALL OK or lists
the failures.

Notation: monic sextic P = x^6 + u5 x^5 + ... + u0 (u_i = coefficient, NOT the unit roundoff);
Pan's chain (Knuth (16)): z = (x+a0)x + a1, w = z + x + a2, v = z - x + a3, q = v w + a4,
P = q z + a5.  D = u3 - 2 a0 u4 + 5 a0^3 = Delta/27, Delta = 27u3 - 18u5u4 + 5u5^3,
N = u1 - a0 u2 + a0^2 u3 - a0^3 u4 + 2 a0^5.
"""
import sys, math, itertools
from fractions import Fraction
from sympy import (symbols, Poly, expand, simplify, cancel, Rational, S, series, limit,
                   Abs, sign, oo, nsimplify, cos, pi, N as numeric)

x, t, d = symbols('x t d')
u0, u1, u2, u3, u4, u5 = symbols('u0 u1 u2 u3 u4 u5')
a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')        # Pan's alpha_0..alpha_5
m0_, m1_, m2_, m3_, m4_, m5_ = symbols('m0 m1 m2 m3 m4 m5')  # |alpha_j| (nonnegative) in the majorant
U = [u0, u1, u2, u3, u4, u5]

failures = []
def check(name, cond):
    print(f"  [{'ok' if cond else 'FAIL'}] {name}")
    if not cond: failures.append(name)

def chain(a0, a1, a2, a3, a4, a5, X=x):
    z = (X + a0) * X + a1
    w = z + X + a2
    v = z - X + a3
    q = v * w + a4
    return q * z + a5

def majorant(m0, m1, m2, m3, m4, m5, T=t):
    """Majorant program: constants -> |constants|, subtraction -> addition, evaluated at T=|x|."""
    Z = (T + m0) * T + m1
    W = Z + T + m2
    V = Z + T + m3
    Q = V * W + m4
    return Q * Z + m5

# ------------------------------------------------------------------------------------------
print("C1: hand-derived majorant M(t) = sum_e m_e t^e of Pan's chain")
M = Poly(expand(majorant(m0_, m1_, m2_, m3_, m4_, m5_)), t)
hand = {
    6: S(1),
    5: 3 * m0_ + 2,
    4: 3 * m0_**2 + 4 * m0_ + 3 * m1_ + m2_ + m3_ + 1,
    3: m0_**3 + 2 * m0_**2 + m0_ + 6 * m0_ * m1_ + 2 * m0_ * (m2_ + m3_) + 4 * m1_ + m2_ + m3_,
    2: 3 * m0_**2 * m1_ + m0_**2 * (m2_ + m3_) + m0_ * (4 * m1_ + m2_ + m3_) + 3 * m1_**2 + 2 * m1_ * (m2_ + m3_) + m1_ + m2_ * m3_ + m4_,
    1: m0_ * (3 * m1_**2 + 2 * m1_ * (m2_ + m3_) + m2_ * m3_ + m4_) + m1_ * (2 * m1_ + m2_ + m3_),
    0: m1_ * (m1_ + m2_) * (m1_ + m3_) + m1_ * m4_ + m5_,
}
for e in range(7):
    check(f"m_{e} matches hand formula", simplify(M.coeff_monomial(t**e) - hand[e]) == 0)
check("every m_e is a polynomial with nonnegative integer coefficients in (|alpha_j|)",
      all(c > 0 for e in range(7) for c in Poly(M.coeff_monomial(t**e), m0_, m1_, m2_, m3_, m4_, m5_).coeffs()))
check("M(t) >= |alpha_5| termwise: m_0 - m5 has nonnegative coefficients",
      all(c > 0 for c in Poly(hand[0] - m5_, m1_, m2_, m3_, m4_).coeffs()))

# ------------------------------------------------------------------------------------------
print("C2: decoder as explicit pivots; closed forms of alpha_2..alpha_5 as polynomials in (alpha_0, alpha_1)")
P = Poly(expand(chain(a0, a1, a2, a3, a4, a5)), x)
check("row x^5 = 3 alpha_0", simplify(P.coeff_monomial(x**5) - 3 * a0) == 0)
# synthetic division of P by z = x^2 + a0 x + a1 with GENERAL beta1 (i.e. general alpha_0 relative to u5)
beta1g = u5 - a0
b2g = u4 - a0 * beta1g - a1
b3g = u3 - a0 * b2g - a1 * beta1g
b4g = u2 - a0 * b3g - a1 * b2g
r1g = u1 - a0 * b4g - a1 * b3g
r0g = u0 - a1 * b4g
target = x**6 + sum(U[i] * x**i for i in range(6))
quo = x**4 + beta1g * x**3 + b2g * x**2 + b3g * x + b4g
check("synthetic division: P = (x^2+a0x+a1)*quo + r1 x + r0 identically",
      expand(target - ((x**2 + a0 * x + a1) * quo + r1g * x + r0g)) == 0)
r1poly = Poly(expand(r1g), a1)
check("coefficient of alpha_1^2 in the x^1 remainder is (beta1 - 2 alpha_0) = u5 - 3 alpha_0",
      simplify(r1poly.coeff_monomial(a1**2) - (beta1g - 2 * a0)) == 0)
# now impose alpha_0 = u5/3
A0 = u5 / 3
Dp = u3 - 2 * A0 * u4 + 5 * A0**3
Np = u1 - A0 * u2 + A0**2 * u3 - A0**3 * u4 + 2 * A0**5
r1 = expand(r1g.subs(a0, A0))
check("with alpha_0 = u5/3 the x^1 remainder is N - D alpha_1", simplify(r1 - (Np - Dp * a1)) == 0)
check("27 D = Delta = 27u3 - 18u5u4 + 5u5^3", simplify(27 * Dp - (27 * u3 - 18 * u5 * u4 + 5 * u5**3)) == 0)
# closed forms of the remaining parameters as polynomials in alpha_0, alpha_1 (a0 kept symbolic, beta1 = 2 a0)
c3 = u3 - a0 * u4 + 2 * a0**3
c4 = u2 - a0 * u3 + a0**2 * u4 - 2 * a0**4
e3 = (c3 - (a0 - 1) * (u4 - 2 * a0**2) + (a0 - 1) * (a0**2 - 1)) / 2
e2 = u4 - 3 * a0**2 + 1 - e3
beta2 = u4 - 2 * a0**2 - a1
beta3 = c3 - a0 * a1
beta4 = c4 + (3 * a0**2 - u4) * a1 + a1**2
A3 = e3 - Rational(3, 2) * a1
A2 = e2 - Rational(3, 2) * a1
A4 = Rational(3, 4) * a1**2 + Rational(1, 2) * (3 * a0**2 - u4 + 1) * a1 + (c4 - e2 * e3)
A5 = u0 - c4 * a1 - (3 * a0**2 - u4) * a1**2 - a1**3
# Knuth (19) with beta1 = 2 a0
B1 = 2 * a0
B2 = u4 - a0 * B1 - a1
B3 = u3 - a0 * B2 - a1 * B1
B4 = u2 - a0 * B3 - a1 * B2
K3 = (B3 - (a0 - 1) * B2 + (a0 - 1) * (a0**2 - 1)) / 2 - a1
K2 = B2 - (a0**2 - 1) - K3 - 2 * a1
K4 = B4 - (K2 + a1) * (K3 + a1)
K5 = u0 - a1 * B4
check("beta_2 = u4 - 2a0^2 - a1", simplify(B2 - beta2) == 0)
check("beta_3 = c3 - a0 a1", simplify(B3 - beta3) == 0)
check("beta_4 = c4 + (3a0^2 - u4) a1 + a1^2", simplify(B4 - beta4) == 0)
check("alpha_3 = e3 - (3/2) alpha_1 (Knuth 19)", simplify(K3 - A3) == 0)
check("alpha_2 = e2 - (3/2) alpha_1 (Knuth 19)", simplify(K2 - A2) == 0)
check("alpha_4 = (3/4) alpha_1^2 + ((3a0^2-u4+1)/2) alpha_1 + (c4 - e2 e3) (Knuth 19)", simplify(K4 - A4) == 0)
check("alpha_5 = u0 - c4 alpha_1 - (3a0^2-u4) alpha_1^2 - alpha_1^3 (Knuth 19)", simplify(K5 - A5) == 0)
# the whole decoder reproduces P when alpha_0 = u5/3 and alpha_1 = N/D
full = chain(A0, Np / Dp, A2.subs({a0: A0, a1: Np / Dp}), A3.subs({a0: A0, a1: Np / Dp}),
             A4.subs({a0: A0, a1: Np / Dp}), A5.subs({a0: A0, a1: Np / Dp}))
check("chain(decoder(P)) = P as a rational function of u0..u5", cancel(expand(full) - target) == 0)

# ------------------------------------------------------------------------------------------
print("C3: Laurent orders in d = D along u3 = 2 a0 u4 - 5 a0^3 + d, and the exact leading term of the majorant")
u3d = 2 * A0 * u4 - 5 * A0**3 + d
subsd = {a0: A0, u3: u3d}
N0 = Np.subs(u3, u3d).subs(d, 0)          # N at the limit point (d = 0); N(d) = N0 + a0^2 d
check("N(d) = N0 + alpha_0^2 d", simplify(Np.subs(u3, u3d) - (N0 + A0**2 * d)) == 0)
check("D(d) = d", simplify(Dp.subs(u3, u3d) - d) == 0)
al1 = (N0 + A0**2 * d) / d
pars = {1: al1}
for i, expr in ((2, A2), (3, A3), (4, A4), (5, A5)):
    pars[i] = cancel(expr.subs(subsd).subs(a1, al1))
expected = {1: (-1, N0), 2: (-1, -Rational(3, 2) * N0), 3: (-1, -Rational(3, 2) * N0),
            4: (-2, Rational(3, 4) * N0**2), 5: (-3, -N0**3)}
for i, (order, lead) in expected.items():
    lc = cancel(pars[i] * d**(-order)).subs(d, 0)
    check(f"alpha_{i} = ({lead}) d^({order}) + O(d^({order + 1}))", simplify(lc - lead) == 0)
# leading term of the majorant: for N0 > 0 and 0 < d small, the signs are
#   alpha_1 > 0, alpha_2 < 0, alpha_3 < 0, alpha_4 > 0, alpha_5 < 0  (from the leading terms),
# so |alpha| = (alpha_1, -alpha_2, -alpha_3, alpha_4, -alpha_5) and the majorant is a Laurent series in d.
Msigned = majorant(Abs(A0), pars[1], -pars[2], -pars[3], pars[4], -pars[5])
leadM = cancel(expand(Msigned) * d**3).subs(d, 0)
check("d^3 M(t) -> 8 N0^3 as d -> 0+ (N0 > 0), independently of t",
      simplify(leadM - 8 * N0**3) == 0 and not leadM.has(t))
# and m_0 alone: 8 N0^3 too (so the whole leading term sits in the degree-0 majorant coefficient)
lead0 = cancel(expand(Msigned.subs(t, 0)) * d**3).subs(d, 0)
check("d^3 m_0 -> 8 N0^3 (the degree-0 tree monomials carry the leading term)", simplify(lead0 - 8 * N0**3) == 0)

# ------------------------------------------------------------------------------------------
print("C4: exact rational evaluation on the three families of numstab_pan.log (d = 2^-k), and the inequalities of the proposition")
def decode(u):
    u = [Fraction(c) for c in u]
    A0v = u[5] / 3
    Dv = u[3] - 2 * A0v * u[4] + 5 * A0v**3
    Nv = u[1] - A0v * u[2] + A0v**2 * u[3] - A0v**3 * u[4] + 2 * A0v**5
    if Dv == 0: raise ZeroDivisionError
    A1v = Nv / Dv
    B1 = 2 * A0v; B2 = u[4] - A0v * B1 - A1v; B3 = u[3] - A0v * B2 - A1v * B1; B4 = u[2] - A0v * B3 - A1v * B2
    A3v = (B3 - (A0v - 1) * B2 + (A0v - 1) * (A0v**2 - 1)) / 2 - A1v
    A2v = B2 - (A0v**2 - 1) - A3v - 2 * A1v
    A4v = B4 - (A2v + A1v) * (A3v + A1v)
    A5v = u[0] - A1v * B4
    return [A0v, A1v, A2v, A3v, A4v, A5v], Dv, Nv
def horner(u, xv):
    r = Fraction(1)
    for c in reversed(u): r = r * xv + c
    return r
def log10(q): return (math.log10(q.numerator) - math.log10(q.denominator)) if q else -math.inf

families = [  # (u5, u4, u2, u1, u0) with u3 = 2 a0 u4 - 5 a0^3 + 2^-k   (numstab_pan.mjs, families 0,1,2)
    (0, 1, 5, 1, 2), (3, -4, -3, -1, -2), (-3, 4, 2, 3, -4)]
xs = [Fraction(3, 2), Fraction(-5, 4), Fraction(1, 2)]
# reference values transcribed from numstab_pan.log (log10 A med / max at k = 40; slope at k >= 12 is -3.00)
ref_k40 = {0: (35.8, 36.4), 1: (37.4, 38.4), 2: (37.2, 38.0)}
all_ineq = True; all_slope = True; all_ratio = True; all_ref = True; all_slope8 = True; slope_rows = []
for fi, (v5, v4, v2, v1, v0) in enumerate(families):
    A0v = Fraction(v5, 3)
    prev = None
    for k in range(0, 41, 4):
        dv = Fraction(1, 2**k)
        u = [Fraction(v0), Fraction(v1), Fraction(v2), 2 * A0v * v4 - 5 * A0v**3 + dv, Fraction(v4), Fraction(v5)]
        al, Dv, Nv = decode(u)
        assert Dv == dv
        logs = []
        for xv in xs:
            T = abs(xv)
            Mv = majorant(*[abs(a) for a in al], T=T)
            Sig = sum(abs(c) * T**i for i, c in enumerate(u)) + T**6
            Av = Fraction(Mv) / Sig
            all_ineq &= Av >= abs(al[5]) / Sig                     # (i) of the proposition
            # quantitative form: |alpha_5| >= |alpha_1|^3 - |3a0^2-u4||alpha_1|^2 - |c4||alpha_1| - |u0|
            c4v = u[2] - al[0] * u[3] + al[0]**2 * u[4] - 2 * al[0]**4
            all_ineq &= abs(al[5]) >= abs(al[1])**3 - abs(3 * al[0]**2 - u[4]) * al[1]**2 - abs(c4v) * abs(al[1]) - abs(u[0])
            logs.append(log10(Av))
            if k == 40:
                ratio = Fraction(Mv) / (8 * abs(Nv / Dv)**3)
                all_ratio &= abs(float(ratio) - 1) < 1e-6           # M ~ 8 |N/D|^3 (C3), tested at d = 2^-40
        logs.sort()
        med, mx = logs[1], logs[2]
        if prev is not None:
            slope = (med - prev) / (math.log10(dv) - math.log10(Fraction(1, 2**(k - 4))))   # between k-4 and k
            slope_rows.append((fi, k, slope))
            if k >= 12: all_slope &= abs(slope + 3) < 0.005
            if k >= 8: all_slope8 &= abs(slope + 3) < 0.05
        prev = med
        if k == 40:
            all_ref &= abs(med - ref_k40[fi][0]) < 0.06 and abs(mx - ref_k40[fi][1]) < 0.06
            print(f"   family {fi}: k=40  log10 A med={med:.2f} max={mx:.2f}  log10|alpha_1|={log10(abs(al[1])):.2f}  log10|alpha_5|={log10(abs(al[5])):.2f}  (log: med {ref_k40[fi][0]}, max {ref_k40[fi][1]})")
check("A(P,x) >= |alpha_5| / sum_i |u_i||x|^i at every (family, k, x) sampled (33 x 3 exact evaluations)", all_ineq)
print("   slopes d log10 A / d log10 D between k-4 and k (median over x): " + "; ".join(f"fam {fi} k={k}: {sl:.3f}" for fi, k, sl in slope_rows if k <= 16))
check("d log10 A / d log10 D = -3.00 (within 0.005) for k >= 12 on all three families, median over x", all_slope)
check("d log10 A / d log10 D within 0.05 of -3 for k >= 8 on all three families (at k = 8: -2.95, -3.00, -2.96)", all_slope8)
check("M(|x|) / (8 |N/D|^3) = 1 within 1e-6 at d = 2^-40 on all three families and all three x", all_ratio)
check("log10 A med/max at k = 40 agree with numstab_pan.log within 0.06", all_ref)

# ------------------------------------------------------------------------------------------
print("C5: the hypothesis |N/Delta| -> oo is necessary: paths into H ∩ {N = 0} can keep the parameters bounded")
# (a) P_d = x^6 + d x^3 : Delta = 27 d -> 0, N == 0, so alpha_1 = 0 and every parameter is bounded.
ud = [S(0), S(0), S(0), d, S(0), S(0)]
A0v = ud[5] / 3
Dv = ud[3] - 2 * A0v * ud[4] + 5 * A0v**3
Nv = ud[1] - A0v * ud[2] + A0v**2 * ud[3] - A0v**3 * ud[4] + 2 * A0v**5
check("P_d = x^6 + d x^3 has D = d, N = 0", simplify(Dv - d) == 0 and Nv == 0)
B2 = ud[4] - A0v * 2 * A0v - 0; B3 = ud[3] - A0v * B2; B4 = ud[2] - A0v * B3
K3 = (B3 - (A0v - 1) * B2 + (A0v - 1) * (A0v**2 - 1)) / 2
K2 = B2 - (A0v**2 - 1) - K3
K4 = B4 - K2 * K3
K5 = ud[0]
pars_d = [A0v, S(0), K2, K3, K4, K5]
check("its parameters are (0, 0, (1-d)/2, (1+d)/2, -(1-d^2)/4, 0): polynomial in d, hence bounded as d -> 0",
      [simplify(p - q) == 0 for p, q in zip(pars_d, [0, 0, (1 - d) / 2, (1 + d) / 2, -(1 - d**2) / 4, 0])] == [True] * 6)
check("and the chain with these parameters computes x^6 + d x^3", expand(chain(*pars_d) - (x**6 + d * x**3)) == 0)
# (b) the fibre over x^6 (a point of H ∩ {N = 0}) is one-dimensional: alpha_1 = s free
s = symbols('s')
fib = [S(0), s, Rational(1, 2) - Rational(3, 2) * s, Rational(1, 2) - Rational(3, 2) * s,
       Rational(3, 4) * s**2 + s / 2 - Rational(1, 4), -s**3]
check("x^6 has the one-parameter fibre alpha = (0, s, 1/2 - 3s/2, 1/2 - 3s/2, 3s^2/4 + s/2 - 1/4, -s^3)",
      expand(chain(*fib) - x**6) == 0)
check("at s = 0 the parameters are (0, 0, 1/2, 1/2, -1/4, 0): bounded", [p.subs(s, 0) for p in fib] == [0, 0, Rational(1, 2), Rational(1, 2), -Rational(1, 4), 0])
# (c) a point of H with N != 0 is NOT in the image (x^6 + x): the x^1 row reads N - D alpha_1 = 1 - 0.
check("x^6 + x: D = 0 and N = 1, so no parameters exist (row x^1 reads 1 = 0)",
      Dp.subs({u5: 0, u4: 0, u3: 0}) == 0 and Np.subs({u5: 0, u4: 0, u3: 0, u2: 0, u1: 1}) == 1)

# (d) at a point of H ∩ {N = 0} bounded parameters exist, but sup A over every neighbourhood is still infinite:
#     P_k = x^6 + x^3/k^2 + x/k -> x^6 has D = 1/k^2, N = 1/k, alpha_1 = k, and A(P_k, 1) ~ 8 k^3 (exact Fractions).
e1_ok = True; e1_rows = []
for kk in (10, 100, 1000, 10000):
    uk = [Fraction(0), Fraction(1, kk), Fraction(0), Fraction(1, kk * kk), Fraction(0), Fraction(0)]
    alk, Dk, Nk = decode(uk)
    Mk = majorant(*[abs(a) for a in alk], T=Fraction(1))
    Sk = sum(abs(c) for c in uk) + 1
    Ak = Fraction(Mk) / Sk
    e1_rows.append((kk, alk[1], float(Ak)))
    e1_ok &= alk[1] == kk and abs(float(Ak) / (8 * kk**3) - 1) < 2 / kk
print("   P_k = x^6 + x^3/k^2 + x/k: (k, alpha_1, A(P_k, 1)) =", [(kk, str(a1), f"{Av:.4g}") for kk, a1, Av in e1_rows])
check("P_k -> x^6 in H ∩ {N = 0} with alpha_1 = k and A(P_k, 1) = 8 k^3 (1 + O(1/k)): sup of A near a point of H with bounded fibre is infinite", e1_ok)
# (e) N does not vanish identically on H: substituting u3 = (18 u5 u4 - 5 u5^3)/27 (the graph description of H) into N leaves a
#     nonzero polynomial in (u1, u2, u4, u5) -- so every relatively open subset of H, and every box meeting H, contains points
#     with N != 0 (where the parameters are unbounded); x^6 + x is one, with N = 1.
NonH = expand(Np.subs(u3, (18 * u5 * u4 - 5 * u5**3) / 27))
check("N restricted to H (u3 = (18 u5 u4 - 5 u5^3)/27) is the nonzero polynomial u1 - u5 u2/3 + ... (coefficient of u1 is 1); N(x^6 + x) = 1",
      NonH != 0 and Poly(NonH, u1).coeff_monomial(u1) == 1 and NonH.subs({u1: 1, u2: 0, u4: 0, u5: 0}) == 1)

# ------------------------------------------------------------------------------------------
print("C6: ingredients for Pan's general scheme (0.7)")
# (a) mu_n > 0: no conjugation-closed 4-subset of the n-th roots of unity sums to 0 for odd n
#     (two conjugate pairs {w^±j, w^±k}, j != k in 1..(n-1)/2: sum = 2cos(2πj/n) + 2cos(2πk/n));
#     and no single conjugate pair sums to 0 (2cos(2πj/n) != 0).  Checked numerically to 1e-12 for odd n <= 31,
#     and the parity argument (2(j±k) = n impossible for odd n) covers all n.
mu_ok = True
for n in range(5, 32, 2):
    h = (n - 1) // 2
    m4 = min(abs(2 * math.cos(2 * math.pi * j / n) + 2 * math.cos(2 * math.pi * k / n)) for j in range(1, h + 1) for k in range(j + 1, h + 1))
    m2 = min(abs(2 * math.cos(2 * math.pi * j / n)) for j in range(1, h + 1))
    mu_ok &= m4 > 1e-12 and m2 > 1e-12
    par_ok = all(2 * (j + k) != n and 2 * (j - k) != n for j in range(1, h + 1) for k in range(1, h + 1))
    mu_ok &= par_ok
check("mu_n = min |2cos(2πj/n)+2cos(2πk/n)| > 0 and min |2cos(2πj/n)| > 0 for odd 5 <= n <= 31 (numeric + parity)", mu_ok)
# the values themselves (they decrease like ~ 30/n^2; the lemma needs only mu_n > 0, and T_n(B) grows accordingly)
mus = {}
rou_ok = True
import cmath
for n in range(5, 32, 2):
    h = (n - 1) // 2
    mu = min(min(abs(2 * math.cos(2 * math.pi * j / n) + 2 * math.cos(2 * math.pi * k / n)) for j in range(1, h + 1) for k in range(j + 1, h + 1)),
             min(abs(2 * math.cos(2 * math.pi * j / n)) for j in range(1, h + 1)))
    mus[n] = mu
    eta = min(mu / 8, 0.5 * math.sin(math.pi / n)); lb = eta * math.sin(math.pi / n) ** (n - 1)
    for sgn in (1, -1):                                   # roots of y^n = +1 and of y^n = -1 (n odd: the negatives)
        for j in range(n):
            zc = cmath.exp(2j * math.pi * j / n) * sgn
            for i in range(200):
                y = zc + eta * cmath.exp(2j * math.pi * i / 200)
                rou_ok &= abs(y**n - sgn) >= lb * (1 - 1e-9) and abs(y) <= 1.5
print("   mu_n for odd n = 5..31: " + ", ".join(f"{n}: {mus[n]:.4f}" for n in sorted(mus)))
check("Rouche step of the (0.7) lemma, numerically: |y^n -+ 1| >= eta sin^(n-1)(pi/n) on all n circles |y - zeta| = eta (200 points each), both signs, |y| <= 3/2, odd 5 <= n <= 31", rou_ok)
# (b) the last stage (n = 5) of (0.7) is a polynomial automorphism: p5 = (x + l1) q4 + l5, q4 = (x^2+x+l2)(x^2+l3) + l4
c0, c1, c2, c3_, c4_ = symbols('c0 c1 c2 c3 c4')
l1 = c4_ - 1
q4 = x**4 + x**3 + symbols('b2') * x**2 + symbols('b3') * x + symbols('b4')
quint = x**5 + c4_ * x**4 + c3_ * x**3 + c2 * x**2 + c1 * x + c0
Q4, R = Poly(quint, x).div(Poly(x + l1, x))
b = [Q4.coeff_monomial(x**i) for i in range(5)]
check("(0.7) n = 5: quotient of p5 by (x + c4 - 1) is x^4 + x^3 + ... (x^3-coefficient 1)", b[4] == 1 and simplify(b[3] - 1) == 0)
l5 = R.as_expr()
l3 = b[1]; l2 = b[2] - b[1]; l4 = b[0] - l2 * l3
p5 = (x + l1) * ((x**2 + x + l2) * (x**2 + l3) + l4) + l5
check("(0.7) n = 5: lambda_1..lambda_5 are polynomials in c0..c4 and the chain reproduces the quintic",
      expand(p5 - quint) == 0 and all(e.is_polynomial(c0, c1, c2, c3_, c4_) for e in (l1, l2, l3, l4, l5)))
# (c) illustration only (not part of any proof): for one degree-9 polynomial with |c_i| <= 5, at |t| in {1e9, 1e18, 1e27}
#     every conjugation-closed 4-subset sum of the roots of p - t is at least (mu_9/2)|t|^{1/9} in modulus,
#     and in particular is not -1: the root-asymptotics step of the (0.7) boundedness lemma, numerically.
#     (At |t| = 1e6, where |t|^{1/9} = 4.6 < B = 5, the asymptotic regime is not yet reached: min |sum| = 0.28.)
import numpy as np
mu9 = min(abs(2 * math.cos(2 * math.pi * j / 9) + 2 * math.cos(2 * math.pi * k / 9)) for j in range(1, 5) for k in range(j + 1, 5))
coef = [1, 3, -1, 1, 1, 4, 4, -2, 5, -4]  # x^9 + 3x^8 - x^7 + ... (descending), a [-5,5] example
illus = True
for tv in (1e9, -1e9, 1e18, -1e18, 1e27, -1e27):
    cc = list(coef); cc[-1] -= tv
    rts = np.roots(cc)
    cl = [r for r in rts]
    best = math.inf
    for Ssub in itertools.combinations(range(9), 4):
        sub = [rts[i] for i in Ssub]
        # conjugation-closed: the multiset of conjugates equals the multiset (within tolerance)
        if all(min(abs(np.conj(z) - w) for w in sub) < 1e-6 * abs(tv)**(1 / 9) for z in sub):
            best = min(best, abs(sum(sub)))
    illus &= best >= 0.5 * mu9 * abs(tv)**(1 / 9) and best > 1 + 1e-6
print(f"   (illustration) degree-9 example: min conjugation-closed 4-subset |sum| >= (mu_9/2)|t|^(1/9) at |t| in {{1e9, 1e18, 1e27}}: {illus}")

# ------------------------------------------------------------------------------------------
print("C7: Jacobian of Pan's coefficient map F(alpha) = (u0..u5) and its relation to D and N")
from sympy import Matrix, factor
coefF = [P.coeff_monomial(x**i) for i in range(6)]
JF = Matrix([[coefF[i].diff(a) for a in (a0, a1, a2, a3, a4, a5)] for i in range(6)])
detJ = factor(JF.det())
DF = expand(Dp.subs(dict(zip(U, coefF))))
NF = expand(Np.subs(dict(zip(U, coefF))))
check("det J_F(alpha) = 6 (alpha_0 - alpha_2 + alpha_3)", simplify(detJ - 6 * (a0 - a2 + a3)) == 0)
check("D(F(alpha)) = alpha_0 - alpha_2 + alpha_3  (so det J_F = 6 D∘F: the critical set is F^{-1}(H))", simplify(DF - (a0 - a2 + a3)) == 0)
check("N(F(alpha)) = alpha_1 D(F(alpha))  (so F(alpha) in H forces N = 0: H \\ {N=0} is outside the image)", simplify(NF - a1 * DF) == 0)
wq = (x + a0) * x + a1 + x + a2
vq = (x + a0) * x + a1 - x + a3
check("on the critical set alpha_3 = alpha_2 - alpha_0 the two factors satisfy w(x) = v(x+1)",
      expand(wq - vq.subs(x, x + 1)).subs(a3, a2 - a0) == 0)

print("ALL OK" if not failures else "FAILED: " + "; ".join(failures))
sys.exit(0 if not failures else 1)
