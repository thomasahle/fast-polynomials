#!/usr/bin/env python3
"""Pan's rational sextic scheme -- transcription and decoder check (sympy, exact over Q).

Source: Knuth, TAOCP vol. 2, 3rd ed., section 4.6.4, eqs. (16)-(19) (pp. 492-493), citing
V. Ya. Pan, Problemy Kibernetiki 5 (1961), 17-29; worked example = Knuth's exercise 22 and its
answer (p. 701-702).

Scheme (16), monic input (alpha6 = u6 = 1):
    z = (x + a0) x + a1,   w = z + x + a2,   u(x) = ((z - x + a3) w + a4) z + a5.

WHAT THIS SCRIPT VERIFIES (each item is an exact symbolic identity or an exact rational
evaluation; nothing is sampled, no Groebner basis or generic solver is used):

  V1  The decoder is a descending pivot sequence.  With u(x) = x^6 + u5 x^5 + ... + u0:
        row x^5:  u5 = 3 a0                                  (constant pivot, slope 3)
        rows x^4..x^2: synthetic division of u - a5 by z = x^2 + a0 x + a1 gives the quotient
                  coefficients beta1..beta4 (Knuth (19)); beta4 is quadratic in a1;
        row x^1:  the x-remainder u1 - a0 beta4 - a1 beta3 is AFFINE in a1 (the a1^2 terms
                  cancel) with slope  D = u3 - 2 a0 u4 + 5 a0^3 = (27 u3 - 18 u5 u4 + 5 u5^3)/27,
                  so a1 = N / D with N = u1 - a0 u2 + a0^2 u3 - a0^3 u4 + 2 a0^5   (Knuth (17),(18));
        rows x^2, x^1 of the quotient: a3 has a constant pivot of slope 2, a2 a unit pivot;
        row x^0 of the quotient: a4 unit pivot;  row x^0 of u: a5 unit pivot.
  V2  Substituting Knuth's closed forms (17) and (19), with alpha3 read as
          a3 = (beta3 - (a0-1) beta2 + (a0-1)(a0^2-1)) / 2 - a1,
      into (16) reproduces x^6 + u5 x^5 + ... + u0 identically as a rational function of u0..u5.
  V3  Knuth's exercise 22: u = x^6 - 3x^5 + x^4 - 2x^3 + x^2 - 3x - 1 decodes to
      a0=-1, a1=1, beta=(-2,-2,-2,1), a3=-4, a2=0, a4=4, a5=-2, i.e. z=(x-1)x+1, w=z+x,
      u=((z-x-4)w+4)z-2 -- exactly the printed answer.
  V4  Image of the coefficient map: on the hypersurface H = {D = 0} the x^1 row reads N = 0,
      so a monic sextic on H is in the image iff N = 0 as well (then a1 is free: a
      one-parameter fibre).  Off H every monic sextic has exactly one preimage.
  V5  Blow-up rates: with u5, u4, u2, u1, u0 fixed and u3 = 2 a0 u4 - 5 a0^3 + d (so that D = d),
      the parameters are Laurent polynomials in d with leading orders
          a1 ~ N/d,  a2 ~ -(3/2) N/d,  a3 ~ -(3/2) N/d,  a4 ~ (3/4) N^2/d^2,  a5 ~ -N^3/d^3,
      (N evaluated on H, i.e. at d = 0),
      and the constant term a5 is a degree-0 tree monomial of the chain, so the majorant at any
      |x| is >= |a5| ~ |N|^3 / |d|^3 while sum_i |u_i| |x|^i stays bounded: the amplification
      A of scheme (16) grows at least like dist(u, H)^{-3} near H (away from {N = 0}).
  V6  Rounding depth of the chain (definition of the paper's appendix: rho(x)=0, rho(const)=1,
      sums max+1, products add+1): rho(P) = 20 for scheme (16) (Horner monic sextic: 11).

Run:  python3 tools/pan_sextic_check.py
"""
import sys
from sympy import symbols, Poly, expand, simplify, cancel, Rational, S, factor, series, Symbol

x = symbols('x')
u0, u1, u2, u3, u4, u5 = symbols('u0 u1 u2 u3 u4 u5')
a0, a1, a2, a3, a4, a5 = symbols('a0 a1 a2 a3 a4 a5')
U = [u0, u1, u2, u3, u4, u5]
A = [a0, a1, a2, a3, a4, a5]

def scheme16(a0, a1, a2, a3, a4, a5):
    z = (x + a0) * x + a1
    w = z + x + a2
    return ((z - x + a3) * w + a4) * z + a5

target = x**6 + sum(U[i] * x**i for i in range(6))
ok = True
def check(name, cond):
    global ok
    print(f"  [{'ok' if cond else 'FAIL'}] {name}")
    ok = ok and bool(cond)

# ---------------- V1: structural decoder (explicit pivots) ----------------
print("V1: decoder as explicit pivots")
P = Poly(expand(scheme16(*A)), x)
rows = [P.coeff_monomial(x**k) for k in range(7)]
check("row x^6 == 1", simplify(rows[6] - 1) == 0)
check("row x^5 == 3 a0 (slope 3)", simplify(rows[5] - 3 * a0) == 0)
# synthetic division of (u(x) - a5) by z = x^2 + a0 x + a1, a1 symbolic: quotient q3..q0, remainder r1 x + r0
# quotient coefficients (Knuth's beta1..beta4) computed by the division recurrence, top down:
A0 = u5 / 3
q3 = u5 - A0
q2 = u4 - A0 * q3 - a1
q1 = u3 - A0 * q2 - a1 * q3
q0 = u2 - A0 * q1 - a1 * q2
r1 = u1 - A0 * q0 - a1 * q1
r0 = u0 - a1 * q0
beta1 = 2 * A0
beta2 = u4 - A0 * beta1 - a1
beta3 = u3 - A0 * beta2 - a1 * beta1
beta4 = u2 - A0 * beta3 - a1 * beta2
check("quotient q3 == beta1 = 2 a0", simplify(q3 - beta1) == 0)
check("quotient q2 == beta2 (Knuth 19)", simplify(q2 - beta2) == 0)
check("quotient q1 == beta3 (Knuth 19)", simplify(q1 - beta3) == 0)
check("quotient q0 == beta4 (Knuth 19), quadratic in a1", simplify(q0 - beta4) == 0 and Poly(beta4, a1).degree() == 2)
r1p = Poly(expand(r1), a1)
check("x^1 remainder is AFFINE in a1 (a1^2 cancels)", r1p.degree() == 1)
D = u3 - 2 * A0 * u4 + 5 * A0**3
N = u1 - A0 * u2 + A0**2 * u3 - A0**3 * u4 + 2 * A0**5
check("slope of a1 pivot == -D, D = u3 - 2a0u4 + 5a0^3", simplify(r1p.coeff_monomial(a1) + D) == 0)
check("intercept == N (Knuth 17 numerator)", simplify(r1p.coeff_monomial(1) - N) == 0)
check("27 D == 27u3 - 18u5u4 + 5u5^3 (Knuth 18)", simplify(27 * D - (27 * u3 - 18 * u5 * u4 + 5 * u5**3)) == 0)
# the quotient q(x) must equal (z - x + a3) w + a4 = x^4 + 2a0 x^3 + [2a1+a2+a3+a0^2-1] x^2 + [(a0-1)(a1+a2)+(a0+1)(a1+a3)] x + (a1+a3)(a1+a2)+a4
# (u - a5) = q(x) z(x); recover q by exact division
qz, rem = Poly(expand(scheme16(*A) - a5), x).div(Poly(x**2 + a0 * x + a1, x))
check("(u - a5) is divisible by z", rem.is_zero)
qc = [qz.coeff_monomial(x**k) for k in range(5)]
check("q2 = 2a1 + a2 + a3 + a0^2 - 1", simplify(qc[2] - (2 * a1 + a2 + a3 + a0**2 - 1)) == 0)
check("q1 = 2a0a1 + (a0-1)a2 + (a0+1)a3", simplify(qc[1] - (2 * a0 * a1 + (a0 - 1) * a2 + (a0 + 1) * a3)) == 0)
check("q0 = (a1+a3)(a1+a2) + a4", simplify(qc[0] - ((a1 + a3) * (a1 + a2) + a4)) == 0)
# a3 pivot: eliminating a2 between the x^2 and x^1 rows of q gives 2 a3 = ... (slope 2)
b2, b3 = symbols('b2 b3')
e2 = qc[2] - b2
e1 = qc[1] - b3
# a2 = b2 - 2a1 - a3 - a0^2 + 1 (unit pivot)
a2_sol = b2 - 2 * a1 - a3 - a0**2 + 1
e1s = Poly(expand(e1.subs(a2, a2_sol)), a3)
check("after the a2 unit pivot, the x^1 row of q is affine in a3 with slope 2", e1s.degree() == 1 and simplify(e1s.coeff_monomial(a3) - 2) == 0)
a3_sol = (b3 - (a0 - 1) * b2 + (a0 - 1) * (a0**2 - 1)) / 2 - a1
check("a3 = (b3 - (a0-1) b2 + (a0-1)(a0^2-1))/2 - a1 solves it (Knuth 19, -a1 OUTSIDE the bracket)",
      simplify(e1s.as_expr().subs(a3, a3_sol)) == 0)

# ---------------- V2: Knuth's closed forms reproduce u(x) identically ----------------
print("V2: closed-form decoder (17)+(19) reproduces the sextic")
def decode_knuth(u):
    u0_, u1_, u2_, u3_, u4_, u5_ = u
    A0 = u5_ / 3
    A1 = (u1_ - A0 * u2_ + A0**2 * u3_ - A0**3 * u4_ + 2 * A0**5) / (u3_ - 2 * A0 * u4_ + 5 * A0**3)
    B1 = 2 * A0
    B2 = u4_ - A0 * B1 - A1
    B3 = u3_ - A0 * B2 - A1 * B1
    B4 = u2_ - A0 * B3 - A1 * B2
    A3 = (B3 - (A0 - 1) * B2 + (A0 - 1) * (A0**2 - 1)) / 2 - A1
    A2 = B2 - (A0**2 - 1) - A3 - 2 * A1
    A4 = B4 - (A2 + A1) * (A3 + A1)
    A5 = u0_ - A1 * B4
    return [A0, A1, A2, A3, A4, A5], [B1, B2, B3, B4]
alphas, betas = decode_knuth(U)
diff = cancel(expand(scheme16(*alphas)) - target)
check("scheme16(decode(u)) - u(x) == 0 as a rational function", diff == 0)
check("a1 denominator is D (up to units)", simplify(cancel(alphas[1] * D) - N) == 0)

# ---------------- V3: Knuth exercise 22 ----------------
print("V3: Knuth exercise 22")
uex = [S(-1), S(-3), S(1), S(-2), S(1), S(-3)]  # x^6 - 3x^5 + x^4 - 2x^3 + x^2 - 3x - 1
al, be = decode_knuth(uex)
print("   alphas =", al, " betas =", be)
check("alphas == (-1, 1, 0, -4, 4, -2)", al == [S(-1), S(1), S(0), S(-4), S(4), S(-2)])
check("betas == (-2, -2, -2, 1)", be == [S(-2), S(-2), S(-2), S(1)])
check("chain evaluates the example polynomial", expand(scheme16(*al) - (x**6 - 3 * x**5 + x**4 - 2 * x**3 + x**2 - 3 * x - 1)) == 0)

# ---------------- V4: image of the coefficient map ----------------
print("V4: image on the hypersurface")
# the x^1 row after all other rows are solved is  D * a1 = N  (from V1); on D = 0 it forces N = 0.
check("row x^1 == N - D a1 identically", simplify(r1 - (N - D * a1)) == 0)
# Example of a point on H with N != 0: u5=0 (a0=0), u3=0 => D=0, N=u1; take u1=1: not in the image.
uH = [S(0), S(1), S(0), S(0), S(0), S(0)]  # x^6 + x
DH = D.subs(dict(zip(U, uH))); NH = N.subs(dict(zip(U, uH)))
check("x^6 + x lies on H (D=0) with N=1 != 0: no parameters exist", DH == 0 and NH == 1)
# and a point on H with N = 0: x^6 (all u = 0): the fibre is one-dimensional (a1 free)
uZ = [S(0)] * 6
fam = [a1]  # a1 free; the rest from the pivots with u = 0, a0 = 0
A0v = S(0); A1v = a1
B1v = 0; B2v = -A1v; B3v = 0; B4v = A1v**2
A3v = (B3v - (A0v - 1) * B2v + (A0v - 1) * (A0v**2 - 1)) / 2 - A1v
A2v = B2v - (A0v**2 - 1) - A3v - 2 * A1v
A4v = B4v - (A2v + A1v) * (A3v + A1v)
A5v = 0 - A1v * B4v
check("x^6 has the one-parameter fibre a1 free: scheme16 == x^6 for all a1", expand(scheme16(A0v, A1v, A2v, A3v, A4v, A5v) - x**6) == 0)

# ---------------- V5: blow-up rates near H ----------------
print("V5: Laurent orders of the parameters in d = D (u3 = 2a0u4 - 5a0^3 + d)")
d = symbols('d')
u3_of_d = 2 * (u5 / 3) * u4 - 5 * (u5 / 3)**3 + d
Ud = [u0, u1, u2, u3_of_d, u4, u5]
al_d, be_d = decode_knuth(Ud)
N0 = N.subs(u3, u3_of_d).subs(d, 0)          # N on the hypersurface point (d = 0)
expected = {1: (-1, N0), 2: (-1, -Rational(3, 2) * N0), 3: (-1, -Rational(3, 2) * N0), 4: (-2, Rational(3, 4) * N0**2), 5: (-3, -N0**3)}
for i, (order, lead) in expected.items():
    e = cancel(al_d[i])
    lc = cancel(e * d**(-order)).subs(d, 0)     # leading Laurent coefficient at order d^order
    print(f"   a{i}: leading coefficient / N0^{-order} =", simplify(lc / N0**(-order)))
    check(f"a{i} ~ ({simplify(lead / N0**(-order))}) * N0^{-order} * d^({order})", simplify(lc - lead) == 0)
check("a0 does not depend on d", al_d[0].has(d) is False)

# ---------------- V6: rounding depth ----------------
print("V6: rounding depth of scheme (16)")
def rho_sum(*terms): return max(terms) + (len(terms) - 1)
def rho_mul(a, b): return a + b + 1
RX, RC = 0, 1
rz = rho_sum(rho_mul(rho_sum(RX, RC), RX), RC)         # (x + a0) * x + a1
rw = rho_sum(rz, RX, RC)                               # z + x + a2
rv = rho_sum(rz, RX, RC)                               # z - x + a3
rq = rho_sum(rho_mul(rv, rw), RC)                      # (..) * w + a4
rP = rho_sum(rho_mul(rq, rz), RC)                      # (..) * z + a5
print(f"   rho(z)={rz} rho(w)={rw} rho(v)={rv} rho(q)={rq} rho(P)={rP}")
check("rho(P) == 20", rP == 20)
horner = rho_sum(RX, 0)                                    # x + u5 (leading multiply skipped, exact coefficients)
for i in range(4, -1, -1): horner = rho_sum(rho_mul(horner, RX), 0)
check("Horner monic sextic rho == 11", horner == 11)

print("ALL OK" if ok else "SOME CHECKS FAILED")
sys.exit(0 if ok else 1)
