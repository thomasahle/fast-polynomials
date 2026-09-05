"""Explicit decoders for the two Goldilocks finalizer coefficient maps (AGENTS.md rule 1:
the inverse is exhibited, not searched for).  Verified cases: (i) symbolic identity
decode(encode(params)) == params in Q[b] resp. Z[c] (sympy expand); (ii) encode(decode(a)) == a
symbolically; (iii) 10^4 random parameter vectors over F_p, p = 2^64 - 2^32 + 1, round-trip."""
import random, sympy as sp
x = sp.symbols('x')
P = 2**64 - 2**32 + 1
half = pow(2, -1, P)

# ---- G4: Motzkin's quartic  y = x(x+b0)+b1, out = y(y+x+b2)+b3 ----
b0, b1, b2, b3 = sp.symbols('b0 b1 b2 b3')
y = x*(x+b0)+b1
G4 = sp.Poly(sp.expand(y*(y+x+b2)+b3), x)
assert G4.degree() == 4 and G4.LC() == 1
a3, a2, a1, a0 = [G4.coeff_monomial(x**i) for i in (3, 2, 1, 0)]
print("G4 coefficients:", {3: a3, 2: a2, 1: a1, 0: a0})
# decoder (needs 1/2): b0 from a3; then (b1, b2) from the 2x2 linear system
#   2 b1 + b2 = a2 - b0^2 - b0,   (2 b0 + 1) b1 + b0 b2 = a1   with determinant 2 b0 - (2 b0 + 1) = -1
def dec4(A3, A2, A1, A0, R=sp):
    B0 = (A3 - 1) * R.Rational(1, 2) if R is sp else (A3 - 1) * half % P
    r2 = A2 - B0**2 - B0
    B1 = A1 - B0 * r2            # from the system: b1 = (a1 - b0 r2)/ (2b0+1 - 2b0) = a1 - b0 r2
    B2 = r2 - 2 * B1
    B3 = A0 - B1**2 - B1 * B2
    if R is not sp: return [v % P for v in (B0, B1, B2, B3)]
    return [sp.expand(v) for v in (B0, B1, B2, B3)]
rt = dec4(a3, a2, a1, a0)
assert rt == [b0, b1, b2, b3], rt
A3, A2, A1, A0 = sp.symbols('A3 A2 A1 A0')
d = dec4(A3, A2, A1, A0)
yy = x*(x+d[0])+d[1]
back = sp.Poly(sp.expand(yy*(yy+x+d[2])+d[3]), x)
assert [sp.expand(back.coeff_monomial(x**i) - v) for i, v in ((3, A3), (2, A2), (1, A1), (0, A0))] == [0]*4
print("G4: decode(encode(b)) == b and encode(decode(a)) == a symbolically over Q (uses 1/2); coefficient map is a bijection whenever 2 is invertible")

# ---- G5: out = (x+c2)((x^2+c4)(x^2+x+c3)+c1)+c0 ----
c0, c1, c2, c3, c4 = sp.symbols('c0 c1 c2 c3 c4')
G5 = sp.Poly(sp.expand((x+c2)*((x**2+c4)*(x**2+x+c3)+c1)+c0), x)
assert G5.degree() == 5 and G5.LC() == 1
e4, e3, e2, e1, e0 = [G5.coeff_monomial(x**i) for i in (4, 3, 2, 1, 0)]
print("G5 coefficients:", {4: e4, 3: e3, 2: e2, 1: e1, 0: e0})
def dec5(E4, E3, E2, E1, E0, modp=False):
    C2 = E4 - 1
    s = E3 - C2                  # = c3 + c4
    C4 = E2 - C2 * s
    C3 = s - C4
    C1 = E1 - C3 * C4 - C2 * C4
    C0 = E0 - C2 * (C1 + C3 * C4)
    out = (C0, C1, C2, C3, C4)
    return [v % P for v in out] if modp else [sp.expand(v) for v in out]
assert dec5(e4, e3, e2, e1, e0) == [c0, c1, c2, c3, c4]
E4, E3, E2, E1, E0 = sp.symbols('E4 E3 E2 E1 E0')
d = dec5(E4, E3, E2, E1, E0)
back = sp.Poly(sp.expand((x+d[2])*((x**2+d[4])*(x**2+x+d[3])+d[1])+d[0]), x)
assert [sp.expand(back.coeff_monomial(x**i) - v) for i, v in ((4, E4), (3, E3), (2, E2), (1, E1), (0, E0))] == [0]*5
print("G5: decoder uses only ring operations (unit pivots): bijection over Z, hence over every commutative ring incl. F_p and GF(2^64)")

# ---- numeric round trips over F_p ----
rng = random.Random(1)
f4 = sp.lambdify((b0, b1, b2, b3), [a3, a2, a1, a0])
f5 = sp.lambdify((c0, c1, c2, c3, c4), [e4, e3, e2, e1, e0])
for _ in range(10000):
    bb = [rng.randrange(P) for _ in range(4)]
    A = [v % P for v in f4(*bb)]
    assert dec4(*A, R=None) == bb
    cc = [rng.randrange(P) for _ in range(5)]
    E = [v % P for v in f5(*cc)]
    assert dec5(*E, modp=True) == cc
print("10^4 random round trips over F_p (Goldilocks) for both maps: OK")
