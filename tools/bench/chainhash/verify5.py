# Verify eq:ph:chain5-coeffs, eq:ph:chain5-q/cq, eq:ph:chain5-rows, eq:ph:chain5-decoder
# over GF(2)[c0..c4][X] with sympy.  Companion of verify7.py (the former degree-7 chain).
#
# Circuit (CIRCUITS[5] of website/js/char2.js, = chx_finalize<5> of chainhash_exp.cpp):
#     y = X X
#     z = (y + c0)(X + y + c1)
#     t = (X + c2)(z + c3)
#   f_c = t + c4
from sympy import symbols, Poly, expand
X = symbols('X')
c = symbols('c0:5')
c0,c1,c2,c3,c4 = c
q = symbols('q0:5')
q0,q1,q2,q3,q4 = q
gens_c = (X,)+c
def P2(expr, gens):  # reduce to polynomial over GF(2)
    return Poly(expand(expr), *gens, modulus=2)
def eq2(a, b, gens):
    return P2(a-b, gens).is_zero

# --- circuit (eq:ph:chain5)
g1 = X*X
g2 = (g1+c0)*(X+g1+c1)
f  = (X+c2)*(g2+c3)+c4
Pf = P2(f, gens_c)
def coeffX(P, i, gens):
    d = P.as_dict()
    out = 0
    for mon, co in d.items():
        if mon[0] == i:
            term = co
            for g, e in zip(gens[1:], mon[1:]):
                term *= g**e
            out += term
    return out
ecirc = [coeffX(Pf, i, gens_c) for i in range(6)]
print("degree of f:", Pf.degree(X), " e5 =", ecirc[5])

# --- claimed table (eq:ph:chain5-coeffs)
b = c0+c1; d = c0*c1
claim = {
 5: 1,
 4: 1 + c2,
 3: b + c2,
 2: c0 + c2*b,
 1: d + c3 + c0*c2,
 0: c4 + c2*(d + c3),
}
ok = True
for i in range(6):
    good = eq2(ecirc[i], claim[i], c)
    ok &= good
    print(f"  e{i}: {'OK' if good else 'MISMATCH'}   circuit={P2(ecirc[i], c).as_expr()}")
print("coefficient table:", "ALL OK" if ok else "FAIL")

# intermediate claims in the Expansion paragraph
print("g2 = X^4+X^3+bX^2+c0X+d:", eq2(g2, X**4+X**3+b*X**2+c0*X+d, gens_c))
print("g2+c3 quartic:", eq2(g2+c3, X**4+X**3+b*X**2+c0*X+(d+c3), gens_c))

# --- coordinate change (eq:ph:chain5-q) and inverse (eq:ph:chain5-cq)
qc = [c2, c0+c1, c0, c3, c4]                 # q(c)
cq = [q2, q1+q2, q0, q3, q4]                 # c(q)
comp1 = [expr.subs(dict(zip(q, qc)), simultaneous=True) for expr in cq]
print("c(q(c)) = c:", all(eq2(comp1[i], c[i], c) for i in range(5)))
comp2 = [expr.subs(dict(zip(c, cq)), simultaneous=True) for expr in qc]
print("q(c(q)) = q:", all(eq2(comp2[i], q[i], q) for i in range(5)))

# --- rows (eq:ph:chain5-rows): substitute c(q) into the circuit coefficients
subs_cq = dict(zip(c, cq))
e_q = [P2(ecirc[i].subs(subs_cq, simultaneous=True), q).as_expr() for i in range(6)]
delta = q2*(q1+q2)           # = c0 c1 under c(q)
rows = {
 4: q0 + 1,
 3: q1 + q0,
 2: q2 + q0*q1,
 1: q3 + delta + q0*q2,
 0: q4 + q0*(delta + q3),
}
ok = True
for i in range(5):
    good = eq2(e_q[i], rows[i], q)
    ok &= good
    print(f"  row e{i} in q: {'OK' if good else 'MISMATCH'}   actual={e_q[i]}")
print("row table:", "ALL OK" if ok else "FAIL")
print("delta = c0 c1 under c(q):", eq2(delta, (c0*c1).subs(subs_cq, simultaneous=True), q))
# unitriangularity: row i (= e_{4-i}) depends only on q_0..q_i, with pivot q_i of degree 1 (identity)
allunit = True
for i in range(5):
    Pi = P2(rows[4-i], q)
    used = [q[j] for j in range(5) if Pi.degree(q[j]) > 0]
    later = [q[j] for j in range(i+1, 5) if Pi.degree(q[j]) > 0]
    piv = Pi.degree(q[i])
    # pivot must be exactly q_i + K_i(q_0..q_{i-1}): row - q_i is free of q_i and of later coordinates
    Ki = P2(rows[4-i] - q[i], q)
    unit = (piv == 1) and (Ki.degree(q[i]) <= 0) and not later
    allunit &= unit
    print(f"  row {i} (e{4-i}) uses {used}, degree in q{i} = {piv}, K_{i} = {Ki.as_expr()}, later coords used = {later} -> {'unit pivot' if unit else 'NOT unit'}")
print("all pivots are the identity (no Frobenius root needed):", allunit)

# --- decoder (eq:ph:chain5-decoder): decode(encode(q)) = q, symbolically (no sqrt anywhere)
E = {i: e_q[i] for i in range(5)}
d0 = E[4] + 1
print("q0 decoded:", eq2(d0, q0, q))
d1 = E[3] + d0
print("q1 decoded:", eq2(d1, q1, q))
d2 = E[2] + d0*d1
print("q2 decoded:", eq2(d2, q2, q))
dd = d2*(d1 + d2)
d3 = E[1] + dd + d0*d2
print("q3 decoded:", eq2(d3, q3, q))
d4 = E[0] + d0*(dd + d3)
print("q4 decoded:", eq2(d4, q4, q))
# and encode(decode(e)) = e symbolically, with e0..e4 free symbols
es = symbols('e0:5')
e0,e1,e2,e3,e4 = es
D0 = e4 + 1; D1 = e3 + D0; D2 = e2 + D0*D1; DD = D2*(D1+D2); D3 = e1 + DD + D0*D2; D4 = e0 + D0*(DD + D3)
cdec = [D2, D1+D2, D0, D3, D4]      # c(q) with q = decoded
re = [claim[i].subs(dict(zip(c, cdec)), simultaneous=True) for i in range(5)]
print("encode(decode(e)) = e (symbolic, free e):", all(eq2(re[i], es[i], es) for i in range(5)))

# --- numeric round trip over GF(2^64) with Pi = X^64+X^4+X^3+X+1, and exhaustive GF(2), GF(4), GF(8)
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
    return mul, mask
def encode(cv, mul):
    c0,c1,c2,c3,c4 = cv
    b=c0^c1; d=mul(c0,c1)
    return [c4^mul(c2, d^c3),
            d^c3^mul(c0,c2),
            c0^mul(c2,b),
            b^c2,
            1^c2]
def eval_circuit(cv, v, mul):
    c0,c1,c2,c3,c4 = cv
    y=mul(v,v); z=mul(y^c0, v^y^c1); t=mul(v^c2, z^c3); return t^c4
def decode(ev, mul):
    e0,e1,e2,e3,e4 = ev
    q0=e4^1; q1=e3^q0; q2=e2^mul(q0,q1)
    dl=mul(q2, q1^q2)
    q3=e1^dl^mul(q0,q2)
    q4=e0^mul(q0, dl^q3)
    return [q2, q1^q2, q0, q3, q4]
mul64, m64 = mkfield(64, (1<<64)|0b11011)
random.seed(1)
bad=0
for _ in range(2000):
    cv=[random.getrandbits(64) for _ in range(5)]
    ev=encode(cv, mul64)
    if decode(ev, mul64)!=cv: bad+=1
    ev=[random.getrandbits(64) for _ in range(5)]
    if encode(decode(ev, mul64), mul64)!=ev: bad+=1
    # circuit evaluation equals polynomial evaluation (monic degree 5)
    v=random.getrandbits(64); cv=[random.getrandbits(64) for _ in range(5)]; ev=encode(cv,mul64)
    acc=1
    for i in range(4,-1,-1): acc=mul64(acc,v)^ev[i]
    if acc!=eval_circuit(cv,v,mul64): bad+=1
print("GF(2^64) random round trips (2000x3): failures =", bad)
import itertools
for k,poly in [(1,0b11),(2,0b111),(3,0b1011)]:
    mul,mask=mkfield(k,poly)
    seen=set(); bad=0
    for cv in itertools.product(range(1<<k), repeat=5):
        ev=tuple(encode(list(cv), mul))
        if ev in seen: bad+=1
        seen.add(ev)
        if decode(list(ev), mul)!=list(cv): bad+=1
    print(f"GF(2^{k}) exhaustive: {len(seen)} distinct images of {(1<<k)**5}, failures = {bad}")
