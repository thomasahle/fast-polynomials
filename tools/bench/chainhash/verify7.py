# Verify eq:ph:chain7-coeffs, eq:ph:chain7-q/cq, eq:ph:chain7-rows, eq:ph:chain7-decoder
# over GF(2)[c0..c6][X] with sympy.
from sympy import symbols, Poly, expand, GF
X = symbols('X')
c = symbols('c0:7')
c0,c1,c2,c3,c4,c5,c6 = c
q = symbols('q0:7')
q0,q1,q2,q3,q4,q5,q6 = q
gens_c = (X,)+c
def P2(expr, gens):  # reduce to polynomial over GF(2)
    return Poly(expand(expr), *gens, modulus=2)
def eq2(a, b, gens):
    return P2(a-b, gens).is_zero

# --- circuit (eq:ph:chain7)
g1 = X*(X+c0)
g2 = (X+c1)*(g1+c2)
g3 = g2*(g2+c3)
f  = (X+c4)*(g1+g3+c5)+c6
Pf = P2(f, gens_c)
# coefficient of X^i as polynomial in c
def coeffX(P, i, gens):
    # P is Poly in gens (X first); extract coefficient of X^i
    d = P.as_dict()
    out = 0
    for mon, co in d.items():
        if mon[0] == i:
            term = co
            for g, e in zip(gens[1:], mon[1:]):
                term *= g**e
            out += term
    return out
ecirc = [coeffX(Pf, i, gens_c) for i in range(8)]
print("degree of f:", Pf.degree(X), " e7 =", ecirc[7])

# --- claimed table (eq:ph:chain7-coeffs)
b = c0+c1; e = c2+c0*c1; d = c1*c2
claim = {
 7: 1,
 6: c4,
 5: b**2,
 4: c3 + c4*b**2,
 3: e**2 + c3*b + 1 + c3*c4,
 2: c3*e + c0 + c4*(e**2 + c3*b + 1),
 1: d**2 + c3*d + c5 + c4*(c3*e + c0),
 0: c6 + c4*(d**2 + c3*d + c5),
}
ok = True
for i in range(8):
    good = eq2(ecirc[i], claim[i], c)
    ok &= good
    print(f"  e{i}: {'OK' if good else 'MISMATCH'}   circuit={P2(ecirc[i], c).as_expr()}")
print("coefficient table:", "ALL OK" if ok else "FAIL")

# intermediate claims in the Expansion paragraph
print("g2 = X^3+bX^2+eX+d:", eq2(g2, X**3+b*X**2+e*X+d, gens_c))
print("g3 = X^6+b^2X^4+c3X^3+(e^2+c3b)X^2+c3eX+(d^2+c3d):",
      eq2(g3, X**6+b**2*X**4+c3*X**3+(e**2+c3*b)*X**2+c3*e*X+(d**2+c3*d), gens_c))
print("g1+g3+c5 sextic:", eq2(g1+g3+c5, X**6+b**2*X**4+c3*X**3+(e**2+c3*b+1)*X**2+(c3*e+c0)*X+(d**2+c3*d+c5), gens_c))

# --- coordinate change (eq:ph:chain7-q) and inverse (eq:ph:chain7-cq)
qc = [c4, c0+c1, c3, c2+c0*c1, c1, c5, c6]                    # q(c)
cq = [q1+q4, q4, q3+q1*q4+q4**2, q2, q0, q5, q6]              # c(q)
# A(q(c)) = c
comp1 = [expr.subs(dict(zip(q, qc)), simultaneous=True) for expr in cq]
print("c(q(c)) = c:", all(eq2(comp1[i], c[i], c) for i in range(7)))
comp2 = [expr.subs(dict(zip(c, cq)), simultaneous=True) for expr in qc]
print("q(c(q)) = q:", all(eq2(comp2[i], q[i], q) for i in range(7)))

# --- rows (eq:ph:chain7-rows): substitute c(q) into the circuit coefficients
subs_cq = dict(zip(c, cq))
e_q = [P2(ecirc[i].subs(subs_cq, simultaneous=True), q).as_expr() for i in range(8)]
delta = q4*(q3+q1*q4+q4**2)
rows = {
 6: q0,
 5: q1**2,
 4: q2 + q0*q1**2,
 3: q3**2 + q2*q1 + q2*q0 + 1,
 2: q4 + q2*q3 + q1 + q0*(q3**2 + q2*q1 + 1),
 1: q5 + delta**2 + q2*delta + q0*(q2*q3 + q1 + q4),
 0: q6 + q0*(delta**2 + q2*delta + q5),
}
ok = True
for i in range(7):
    good = eq2(e_q[i], rows[i], q)
    ok &= good
    print(f"  row e{i} in q: {'OK' if good else 'MISMATCH'}   actual={e_q[i]}")
print("row table:", "ALL OK" if ok else "FAIL")
# delta = d(c(q))
print("delta = c1 c2 under c(q):", eq2(delta, (c1*c2).subs(subs_cq, simultaneous=True), q))
# unitriangularity: row i depends only on q_0..q_i, with pivot in q_i
for i in range(7):
    Pi = P2(rows[6-i], q)
    used = [q[j] for j in range(7) if Pi.degree(q[j]) > 0]
    print(f"  row {i} (e{6-i}) uses {used}, degree in q{i} = {Pi.degree(q[i])}")

# --- decoder (eq:ph:chain7-decoder): decode(encode(q)) = q, with sqrt formal
E = {i: e_q[i] for i in range(7)}
d0 = E[6]
# q1 = sqrt(e5): check e5 == q1^2 (then sqrt gives q1 on a perfect field)
print("e5 == q1^2:", eq2(E[5], q1**2, q))
d1 = q1
d2 = E[4] + d0*d1**2
print("q2 decoded:", eq2(d2, q2, q))
print("e3 + q2 q1 + q2 q0 + 1 == q3^2:", eq2(E[3] + d2*d1 + d2*d0 + 1, q3**2, q))
d3 = q3
d4 = E[2] + d2*d3 + d1 + d0*(d3**2 + d2*d1 + 1)
print("q4 decoded:", eq2(d4, q4, q))
dd = d4*(d3 + d1*d4 + d4**2)
d5 = E[1] + dd**2 + d2*dd + d0*(d2*d3 + d1 + d4)
print("q5 decoded:", eq2(d5, q5, q))
d6 = E[0] + d0*(dd**2 + d2*dd + d5)
print("q6 decoded:", eq2(d6, q6, q))

# --- numeric round trip over GF(2^64) with Pi = X^64+X^4+X^3+X+1, and exhaustive GF(4), GF(8)
import random
def mkfield(k, poly):
    mask = (1<<k)-1
    def mul(a,b):
        r=0
        while b:
            if b&1: r^=a
            b>>=1; a<<=1
            if a>>k: a^=poly
        return r
    def sqrt(a):
        # a^(2^(k-1))
        r=a
        for _ in range(k-1): r=mul(r,r)
        return r
    return mul, sqrt, mask
def encode(cv, mul):
    c0,c1,c2,c3,c4,c5,c6 = cv
    b=c0^c1; e=c2^mul(c0,c1); d=mul(c1,c2)
    b2=mul(b,b); e2=mul(e,e); d2=mul(d,d)
    return [c6^mul(c4, d2^mul(c3,d)^c5),
            d2^mul(c3,d)^c5^mul(c4, mul(c3,e)^c0),
            mul(c3,e)^c0^mul(c4, e2^mul(c3,b)^1),
            e2^mul(c3,b)^1^mul(c3,c4),
            c3^mul(c4,b2),
            b2,
            c4]
def eval_circuit(cv, v, mul):
    c0,c1,c2,c3,c4,c5,c6 = cv
    y=mul(v, v^c0); z=mul(v^c1, y^c2); t=mul(z, z^c3); u=mul(v^c4, y^t^c5); return u^c6
def decode(ev, mul, sqrt):
    e0,e1,e2,e3,e4,e5,e6 = ev
    q0=e6; q1=sqrt(e5); q2=e4^mul(q0,mul(q1,q1))
    q3=sqrt(e3^mul(q2,q1)^mul(q2,q0)^1)
    q4=e2^mul(q2,q3)^q1^mul(q0, mul(q3,q3)^mul(q2,q1)^1)
    dl=mul(q4, q3^mul(q1,q4)^mul(q4,q4))
    q5=e1^mul(dl,dl)^mul(q2,dl)^mul(q0, mul(q2,q3)^q1^q4)
    q6=e0^mul(q0, mul(dl,dl)^mul(q2,dl)^q5)
    return [q1^q4, q4, q3^mul(q1,q4)^mul(q4,q4), q2, q0, q5, q6]
mul64, sqrt64, m64 = mkfield(64, (1<<64)|0b11011)
random.seed(1)
bad=0
for _ in range(2000):
    cv=[random.getrandbits(64) for _ in range(7)]
    ev=encode(cv, mul64)
    if decode(ev, mul64, sqrt64)!=cv: bad+=1
    ev=[random.getrandbits(64) for _ in range(7)]
    if encode(decode(ev, mul64, sqrt64), mul64)!=ev: bad+=1
    # circuit evaluation equals polynomial evaluation
    v=random.getrandbits(64); cv=[random.getrandbits(64) for _ in range(7)]; ev=encode(cv,mul64)
    acc=1
    for i in range(6,-1,-1): acc=mul64(acc,v)^ev[i]
    if acc!=eval_circuit(cv,v,mul64): bad+=1
print("GF(2^64) random round trips (2000x3): failures =", bad)
import itertools
for k,poly in [(1,0b11),(2,0b111),(3,0b1011)]:
    mul,sqrt,mask=mkfield(k,poly)
    seen=set(); bad=0
    for cv in itertools.product(range(1<<k), repeat=7):
        ev=tuple(encode(list(cv), mul))
        if ev in seen: bad+=1
        seen.add(ev)
        if decode(list(ev), mul, sqrt)!=list(cv): bad+=1
    print(f"GF(2^{k}) exhaustive: {len(seen)} distinct images of {(1<<k)**7}, failures = {bad}")
