#!/usr/bin/env python3
"""Pan's general real scheme (0.7) -- transcription and decoder identities (sympy, exact over Q).

Source: V. Ya. Pan, "Methods of computing values of polynomials", Russian Math. Surveys 21:1 (1966),
scheme (0.7) p. 108, Lemmas 3.3-3.5 and Theorem 3.1 pp. 123-125.  Monic input P(x) = x^n + u_{n-1} x^{n-1}
+ ... + u_0 (ascending coefficients u_i here; the survey writes a_l x^{n-l}).

Scheme (0.7), with p0 = x^2, p0' = x^2 + x:
    p1 = x + l1
    q^(s) = (p0' + l_{4s-2}) (p0 + l_{4s-1}) + l_{4s}          s = 1..k        (Todd's quartic)
    p_{4s+1} = p_{4s-3} q^(s) + l_{4s+1}                        s = 1..k
    p_{4k+3} = p_{4k+1} (p0 + l_{4k+2}) + l_{4k+3}
    P = p_n (n = 4k+1, 4k+3),   P = x p_{n-1} + u_0 (n even).

WHAT THIS SCRIPT VERIFIES (each item is an exact symbolic identity; nothing is sampled):

  V1  Stage 1 (the last stage of the top-down decoder) is RATIONAL with unit pivots: for a general monic
      quintic p5 = x^5 + u4 x^4 + ... + u0, the x^4 row forces l1 = u4 - 1; l5 = p5(-l1) is the remainder
      of p5 - l5 by x + l1; the quotient is x^4 + x^3 + b2 x^2 + b3 x + b4, and Todd's identity
      (x^2 + x + l2)(x^2 + l3) + l4 = x^4 + x^3 + (l2 + l3) x^2 + l3 x + (l2 l3 + l4)
      gives l3 = b3, l2 = b2 - b3, l4 = b4 - l2 l3 (three unit pivots).  Substituting these closed forms
      into the chain reproduces p5 identically as a polynomial in x with coefficients in Q(u0..u4).
  V2  The even lift: for a general monic sextic, P = x p5 + u0 with p5 = (P - u0)/x decoded by V1
      reproduces P identically (this is the n = 6 row 'Pan (0.7)' of tools/numstab_pan.mjs, and it
      coincides with the paper's own degree-6 chain: P_5 base + even lift; checked there numerically).
  V3  Todd's quartic identity (Lemma 3.5) as a polynomial identity in (b2, b3, b4).
  V4  Quartic stage (s >= 2) bookkeeping: for symbolic t, (b2, b3, b4) and a symbolic monic r of degree
      4s-3 (s = 2, degree 5), p := (x^4 + x^3 + b2 x^2 + b3 x + b4) r + t is reproduced by the stage
      formulas l_{4s-1} = b3, l_{4s-2} = b2 - b3, l_{4s} = b4 - l_{4s-2} l_{4s-1}, l_{4s+1} = t with
      p_{4s-3} := r, i.e. the chain's indexing and the stage's four unit pivots are right.  What the
      stage does NOT make rational is the choice of t: it must be a real number for which p - t has a
      real quartic factor with x^3-coefficient 1 (Lemma 3.3: an intermediate-value argument on the
      root branches of p - t; the resulting t is a real algebraic number).  That step is numeric in
      tools/numstab_pan07.py and is verified there a posteriori (division remainder at 60 digits).
  V5  Pair stage (n = 4k+3, Lemma 3.4): writing p(x) = E(x^2) + x O(x^2), for every root y0 of O the
      remainder of p - E(y0) modulo x^2 - y0 is exactly x O(y0), hence zero: p - t = (x^2 - y0) r with
      t = E(y0), l_{4k+2} = -y0, l_{4k+3} = t.  Verified for a general monic septic (O is a monic cubic,
      so a real y0 always exists) and for a general monic degree-15 polynomial (O monic of degree 7).
  V6  Operation counts of the chain for n = 5..16: floor(n/2) + 1 multiplications and n + 1 additions
      for monic input (survey p. 108: n + 1 additions, floor((n+4)/2) multiplications for general a0).
  V7  Rounding depth rho of the (0.7) chain under the appendix's rules (rho(x) = 0, rho(const) = 1,
      sums max+1, products add+1): rho = 13, 15, 33, 69 for n = 6, 7, 15, 31 (2 + 9k + 4[n = 4k+3]
      + 2[n even]).

Run:  python3 tools/pan07_check.py
"""
import sys
from sympy import symbols, Poly, expand, simplify, cancel, S, div

x = symbols('x')
ok = True
def check(name, cond):
    global ok
    print(f"  [{'ok' if cond else 'FAIL'}] {name}")
    ok = ok and bool(cond)

def chain07(n, lam, u0=None):
    """Evaluate scheme (0.7) symbolically; lam is a dict j -> l_j; u0 the constant term for even n."""
    p0 = x * x; p0p = p0 + x
    m = n - 1 if n % 2 == 0 else n
    k = (m - 1) // 4 if m % 4 == 1 else (m - 3) // 4
    acc = x + lam[1]
    for s in range(1, k + 1):
        q = (p0p + lam[4 * s - 2]) * (p0 + lam[4 * s - 1]) + lam[4 * s]
        acc = acc * q + lam[4 * s + 1]
    if m % 4 == 3:
        acc = acc * (p0 + lam[4 * k + 2]) + lam[4 * k + 3]
    if n % 2 == 0:
        acc = x * acc + u0
    return expand(acc)

def stage1(p5):
    """Rational decoder of a monic quintic (ascending coefficient list, symbolic): returns lam dict."""
    u4 = p5[4]                                   # p5 = the five non-leading coefficients u0..u4 (ascending)
    l1 = u4 - 1
    pexpr = x**5 + sum(c * x**i for i, c in enumerate(p5))
    l5 = expand(pexpr.subs(x, -l1))
    q, r = div(Poly(pexpr - l5, x), Poly(x + l1, x))
    assert r.is_zero
    b = [q.coeff_monomial(x**i) for i in range(5)]
    assert simplify(b[4] - 1) == 0 and simplify(b[3] - 1) == 0
    l3 = b[1]; l2 = b[2] - b[1]; l4 = b[0] - l2 * l3
    return {1: l1, 2: l2, 3: l3, 4: l4, 5: l5}

# ---------------- V1 ----------------
print("V1: stage 1 (monic quintic) is rational with unit pivots")
u = symbols('u0:5')
p5 = list(u)
lam = stage1(p5)
check("l1 = u4 - 1", simplify(lam[1] - (u[4] - 1)) == 0)
target5 = x**5 + sum(u[i] * x**i for i in range(5))
check("chain(decode(p5)) == p5 identically", simplify(chain07(5, lam) - target5) == 0)
check("no denominator other than 1 in any l_j (rational, everywhere defined)",
      all(cancel(v).as_numer_denom()[1] == 1 for v in lam.values()))

# ---------------- V2 ----------------
print("V2: even lift n = 6")
v = symbols('v0:6')
lam = stage1(list(v[1:]))                       # (P - v0)/x has non-leading coefficients v1..v5
target6 = x**6 + sum(v[i] * x**i for i in range(6))
check("x * chain5((P - u0)/x) + u0 == P identically", simplify(chain07(6, lam, v[0]) - target6) == 0)

# ---------------- V3 ----------------
print("V3: Todd's quartic identity")
b2, b3, b4 = symbols('b2 b3 b4')
l3 = b3; l2 = b2 - b3; l4 = b4 - l2 * l3
check("(x^2+x+l2)(x^2+l3)+l4 == x^4+x^3+b2x^2+b3x+b4",
      expand((x**2 + x + l2) * (x**2 + l3) + l4 - (x**4 + x**3 + b2 * x**2 + b3 * x + b4)) == 0)

# ---------------- V4 ----------------
print("V4: quartic stage bookkeeping (s = 2: degree 9 = quartic * quintic + t)")
t = symbols('t')
r = symbols('r0:5')
rpoly = x**5 + sum(r[i] * x**i for i in range(5))
q4 = x**4 + x**3 + b2 * x**2 + b3 * x + b4
p9 = expand(q4 * rpoly + t)
# the stage's formulas, with p_5 := r evaluated by an (arbitrary) inner chain; here we simply substitute r
lam_stage = {7: b3, 6: b2 - b3, 8: b4 - (b2 - b3) * b3, 9: t}
p0 = x * x; p0p = p0 + x
recon = expand(rpoly * ((p0p + lam_stage[6]) * (p0 + lam_stage[7]) + lam_stage[8]) + lam_stage[9])
check("r * q^(2) + l9 == p9 with l7 = b3, l6 = b2 - b3, l8 = b4 - l6 l7, l9 = t", expand(recon - p9) == 0)
check("x^3-coefficient of q^(2) is 1 for every (l6, l7, l8)", Poly(expand((p0p + lam_stage[6]) * (p0 + lam_stage[7]) + lam_stage[8]), x).coeff_monomial(x**3) == 1)

# ---------------- V5 ----------------
print("V5: pair stage (n = 4k+3): p - E(y0) == 0 mod (x^2 - y0) whenever O(y0) = 0")
y0 = symbols('y0')
for n in (7, 15):
    w = symbols(f'w0:{n}')
    p = x**n + sum(w[i] * x**i for i in range(n))
    E = sum(w[i] * y0 ** (i // 2) for i in range(0, n, 2))                 # even part, in y = x^2
    O = y0 ** ((n - 1) // 2) + sum(w[i] * y0 ** (i // 2) for i in range(1, n, 2))   # odd part / x, monic
    q, rem = div(Poly(p - E, x), Poly(x**2 - y0, x))
    check(f"n={n}: remainder of p - E(y0) mod (x^2 - y0) is exactly x * O(y0) (O monic of degree {(n-1)//2})",
          simplify(rem.as_expr() - x * O) == 0 and Poly(O, y0).degree() == (n - 1) // 2 and Poly(O, y0).LC() == 1)
    check(f"n={n}: quotient is monic of degree {n-2} with x^{n-3}-coefficient w_{n-1}",
          q.degree() == n - 2 and q.LC() == 1 and simplify(q.coeff_monomial(x**(n - 3)) - w[n - 1]) == 0)

# ---------------- V6 ----------------
print("V6: operation counts of the chain (monic input)")
def counts(n):
    m = n - 1 if n % 2 == 0 else n
    k = (m - 1) // 4 if m % 4 == 1 else (m - 3) // 4
    mul = 1 + 2 * k + (1 if m % 4 == 3 else 0) + (1 if n % 2 == 0 else 0)     # x*x, 2 per quartic stage, pair stage, even lift
    add = 1 + 1 + 4 * k + (2 if m % 4 == 3 else 0) + (1 if n % 2 == 0 else 0)  # p0'=p0+x, p1=x+l1, 4 per stage (l,l,l,l), pair (l,l), lift (u0)
    return mul, add
allok = True
for n in range(5, 17):
    mul, add = counts(n)
    allok = allok and mul == n // 2 + 1 and add == n + 1
    print(f"   n={n}: {mul} mult, {add} add")
check("floor(n/2)+1 multiplications and n+1 additions for n = 5..16", allok)

# ---------------- V7 ----------------
print("V7: rounding depth")
def rho07(n):
    m = n - 1 if n % 2 == 0 else n
    k = (m - 1) // 4 if m % 4 == 1 else (m - 3) // 4
    RX, RC = 0, 1
    rs = RX + RX + 1; rs1 = max(rs, RX) + 1; acc = max(RX, RC) + 1
    for s in range(k):
        q = (max(rs1, RC) + 1) + (max(rs, RC) + 1) + 1
        q = max(q, RC) + 1
        acc = max(acc + q + 1, RC) + 1
    if m % 4 == 3:
        acc = max(acc + (max(rs, RC) + 1) + 1, RC) + 1
    if n % 2 == 0:
        acc = max(RX + acc + 1, RC) + 1
    return acc
r = {n: rho07(n) for n in (6, 7, 15, 31)}
print("   rho =", r)
check("rho(6,7,15,31) == (13, 15, 33, 69)", r == {6: 13, 7: 15, 15: 33, 31: 69})

print("ALL OK" if ok else "SOME CHECKS FAILED")
sys.exit(0 if ok else 1)
