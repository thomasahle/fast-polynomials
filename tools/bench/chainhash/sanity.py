import sympy as sp
from sympy import symbols, expand, Poly, GF

# (a) irreducibility of x^64+x^4+x^3+x+1 over GF(2) via Rabin's test
def gf2_mulmod(a,b,m,deg):
    r=0
    while b:
        if b&1: r^=a
        b>>=1; a<<=1
        if a>>deg&1: a^=m
    return r
def gf2_powmod(a,e,m,deg):
    r=1
    while e:
        if e&1: r=gf2_mulmod(r,a,m,deg)
        a=gf2_mulmod(a,a,m,deg); e>>=1
    return r
def gf2_gcd(a,b):
    while b:
        while a.bit_length()>=b.bit_length() and a:
            a^=b<<(a.bit_length()-b.bit_length())
        a,b=b,a
    return a
m=(1<<64)|27; deg=64
x=2
ok = gf2_powmod(x,1<<64,m,deg)==x
xp=gf2_powmod(x,1<<32,m,deg)      # x^(2^(64/2)); prime factor of 64 is only 2
ok = ok and gf2_gcd(m, xp^x)==1
print("x^64+x^4+x^3+x+1 irreducible over GF(2):", ok)

# (b) chain parametrizations are bijections onto monic polys in char 2
X=symbols('X')
c0,c1,c2,c3,c4=symbols('c0:5')
e0,e1,e2,e3,e4=symbols('e0:5')
def coeffs_mod2(expr,K):
    P=Poly(expand(expr),X)
    cs=[0]*(K+1)
    for (i,),v in P.terms():
        cs[i]=sp.Poly(v, c0,c1,c2,c3,c4, modulus=2).as_expr()
    return cs
# K=3: (X+c0)(X^2+c1)+c2
f3=(X+c0)*(X**2+c1)+c2
cs=coeffs_mod2(f3,3); print("K=3 coeffs (x^0..x^3) mod 2:",cs)
# inverse: c0=e2, c1=e1, c2=e0+e1e2 ; check round trip mod 2
sub={c0:e2,c1:e1,c2:e0+e1*e2}
rt=[sp.Poly(sp.expand(cc.subs(sub)),e0,e1,e2,e3,e4,modulus=2).as_expr() for cc in cs]
print("K=3 roundtrip (expect e0,e1,e2,1):",rt)
# K=5: (X+c2)((X^2+c0)(X^2+X+c1)+c3)+c4
f5=(X+c2)*((X**2+c0)*(X**2+X+c1)+c3)+c4
cs=coeffs_mod2(f5,5); print("K=5 coeffs (x^0..x^5) mod 2:",cs)
# inverse (derived by hand):
C2=e4+1
S =e3+C2               # c0+c1
C0=e2+C2*S
C1=S+C0
C3=e1+C0*C1+C0*C2
C4=e0+C2*(C0*C1+C3)
sub={c0:C0,c1:C1,c2:C2,c3:C3,c4:C4}
rt=[sp.Poly(sp.expand(cc.subs(sub)),e0,e1,e2,e3,e4,modulus=2).as_expr() for cc in cs]
print("K=5 roundtrip (expect e0..e4,1):",rt)
# and the other direction: decode(encode(c)) = c  (mod 2)
enc=coeffs_mod2(f5,5)
dec_sub={e0:enc[0],e1:enc[1],e2:enc[2],e3:enc[3],e4:enc[4]}
back=[sp.Poly(sp.expand(v.subs(dec_sub)),c0,c1,c2,c3,c4,modulus=2).as_expr() for v in (C0,C1,C2,C3,C4)]
print("K=5 decode(encode(c)) (expect c0..c4):",back)

# (c) injective recurrence: mod-3 exponent classes, degrees, f3 expansion, n=2 check
y,z,u=symbols('y z u')
for n in range(1,5):
    a=symbols('a1:%d'%(n+1)); b=symbols('b1:%d'%(n+1))
    P=z
    for i in range(n):
        P=a[i]+(b[i]+y)*(P+u)
    P=expand(P)
    Pp=Poly(P,z,u)
    d=dict(Pp.terms())
    f1=d.get((0,0),0); f2=d.get((1,0),0); f3=d.get((0,1),0)
    others={k:v for k,v in d.items() if k not in [(0,0),(1,0),(0,1)]}
    assert not others, others
    g=lambda i: sp.prod([(y+b[j]) for j in range(i,n)])
    F1=expand(sum(a[i]*g(i+1) for i in range(n)))
    F2=expand(g(0))
    F3=expand(sum(g(i) for i in range(n)))
    print("n=%d facts 1-4 hold:"%n, expand(f1-F1)==0, expand(f2-F2)==0, expand(f3-F3)==0,
          "deg_y f1,f2,f3 =", Poly(f1,y).degree() if f1!=0 else -1, Poly(f2,y).degree(), Poly(f3,y).degree())
    # specialization degree
    Ps=expand(P.subs({y:X**3,z:X,u:X**2}))
    print("   deg_x P_n after specialization =", Poly(Ps,X).degree(), "(3n+2 =",3*n+2,")",
          "monic:", Poly(Ps,X).LC()==1)
    if n>=2:
        e1=sum(b); e2=sum(b[i]*b[j] for i in range(n) for j in range(i+1,n))
        c_nm1=Poly(f3,y).coeff_monomial(y**(n-1)); c_nm2=Poly(f3,y).coeff_monomial(y**(n-2))
        print("   [y^{n-1}]f3 - (1+sum b) =", expand(c_nm1-(1+e1)),
              "; [y^{n-2}]f3 - (1+sum_{i>=2}b_i+e2) =", expand(c_nm2-(1+sum(b[1:])+e2)))
