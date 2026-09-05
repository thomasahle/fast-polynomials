#!/usr/bin/env python3
"""
balanced_gadgets.py — prototype of depth-balanced decodable known-powers gadgets.

Question (2026-08-28): the paper's fill / known-powers gadgets are Horner-shaped,
which makes the full construction's multiplicative height Theta((log n)^2).  Can
they be restructured to O(log)-depth while KEEPING rational (unitriangular-style)
decodability — and what does that cost in multiplications and additions?

This file implements a square-difference *shell* family, over any field of
characteristic != 2, given the power tower H_2, H_4, ..., H_{2^L} as inputs
(arbitrary monic degree-2^i polynomials, exactly like the paper's "known powers"):

  FB(2^j)   "free block":  ALL polynomials of degree < 2^j      (2^j keys)
  MB(2^j)   "monic block": monic degree 2^j, lower coeffs free  (2^j keys)
  QB(2^t-1) "odd monic":   monic degree 2^t-1, all lower free   (2^t-1 keys)

Shapes (S, D, F recurse in PARALLEL — that is the depth win):

  FB(2^j)   = (H_{2^{j-1}} + S + D)(H_{2^{j-1}} + S - D) - H_{2^j} + F
  MB(2^j)   = (H_{2^{j-1}} + S + D)(H_{2^{j-1}} + S - D) + F
                with S = FB(2^{j-1}),  D = MB(2^{j-2}),  F = FB(2^{j-2})
  QB(2^t-1) = H_{2^{t-1}} * QB(2^{t-1}-1) + FB(2^{t-1})

  bases: FB(1) = c;  FB(2) = (x+a)^2 - H_2 + b;  MB(1) = x + a;
         MB(2) = (x+a)^2 + b;  QB(1) = x + a;  QB(3) = (H_2+a)(x+b) + c.

Every decoder is EXPLICIT and rational: descending window reads with pivot 2
(the S window against 2*H*S, the D window against -D^2 — an inline windowed
monic square root, cf. `lem:monic-from-power`), subtraction of known
polynomials, and division by known monic polynomials (for QB).  No solving.

Degree staggering is forced: a balanced product of two *free* half-degree
blocks is NOT rationally decodable (each coefficient row mixes one fresh key
from each factor — recovering them is a factoring problem).  The shell's
symmetric (E+O)(E-O) form with deg O <= 2^{j-2} (O monic) is what keeps the
read triangular.  This forces the (d/2, d/4, d/4) size split and hence the
multiplication overhead measured here (~4/3 of the paper's count).

HEADLINE (the "peeled" family QP): the recursion

  QP(2^t-1) = (H_{2^{t-1}} + gamma) * QP(2^{t-1}-1) + QP'(2^{t-1}-1),
  base QP(3) = (H_2+a)(x+b)+c

closes the exact-budget gap: it matches the paper's ledger EXACTLY
(2^{t-1}-1 multiplications, 5*2^{t-2}-2 additions) at height exactly t.
The key-carrying glue factor (H+gamma) and the one-degree offset
deg H = deg W + 1 are what make it work: the top window is pure H*W (peel W
against the known monic H), the residual gamma*W + B reveals gamma at its
top row because both children are monic, and B follows by subtraction.
The selftest asserts the exact ledger equality for every t.  QP's decoder
never divides by 2 (pivots are the monic leading 1's), so unlike the shells
it is characteristic-independent: the selftest includes GF(2).

QO extends the peel to EVERY odd degree d at exactly (d-1)/2 multiplications
(asserted per d): QO(d) = (H_h + U)*W + B with h = 2^floor(log2 d),
U = QO(2h-d) riding inside the factor, W = B = QO(d-h).  Measured against
the paper's odd-degree family Q_{2^{l+1}k+2^l-1}: identical multiplications,
strictly fewer additions at every point, and about half the depth — at the
known-powers interface (tower given up to 2^floor(log2 d)).

CLI:
  python3 tools/balanced_gadgets.py selftest
  python3 tools/balanced_gadgets.py table
"""

from __future__ import annotations

import argparse
import random
import sys
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional, Tuple

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

MERSENNE61 = (1 << 61) - 1


# =============================================================================
# Field + polynomial helpers (little-endian coefficient lists)
# =============================================================================


class F:
    """GF(p) for odd p, or exact rationals (p=None)."""

    def __init__(self, p: Optional[int]):
        # The square-difference shells (FB/MB/QB) need characteristic != 2
        # (they halve window reads); the peeled family QP is char-independent
        # and works over GF(2) as well.
        self.p = p

    def c(self, v):  # coerce
        return Fraction(v) if self.p is None else v % self.p

    def add(self, a, b):
        return a + b if self.p is None else (a + b) % self.p

    def sub(self, a, b):
        return a - b if self.p is None else (a - b) % self.p

    def mul(self, a, b):
        return a * b if self.p is None else (a * b) % self.p

    def inv(self, a):
        return 1 / a if self.p is None else pow(a, -1, self.p)

    def half(self, a):
        return self.mul(a, self.inv(self.c(2)))

    def zero(self):
        return self.c(0)

    def one(self):
        return self.c(1)

    def rand(self, rng: random.Random):
        if self.p is None:
            return Fraction(rng.randrange(-99, 100), rng.randrange(1, 20))
        return rng.randrange(self.p)


def ptrim(p: List, f: F) -> List:
    while p and p[-1] == f.zero():
        p.pop()
    return p


def padd(a: List, b: List, f: F) -> List:
    n = max(len(a), len(b))
    out = [f.zero()] * n
    for i, v in enumerate(a):
        out[i] = f.add(out[i], v)
    for i, v in enumerate(b):
        out[i] = f.add(out[i], v)
    return ptrim(out, f)


def psub(a: List, b: List, f: F) -> List:
    n = max(len(a), len(b))
    out = [f.zero()] * n
    for i, v in enumerate(a):
        out[i] = f.add(out[i], v)
    for i, v in enumerate(b):
        out[i] = f.sub(out[i], v)
    return ptrim(out, f)


def pmul(a: List, b: List, f: F) -> List:
    if not a or not b:
        return []
    out = [f.zero()] * (len(a) + len(b) - 1)
    for i, u in enumerate(a):
        if u == f.zero():
            continue
        for j, v in enumerate(b):
            out[i + j] = f.add(out[i + j], f.mul(u, v))
    return ptrim(out, f)


def pscal(a: List, s, f: F) -> List:
    return ptrim([f.mul(s, v) for v in a], f)


def pcoeff(a: List, i: int, f: F):
    return a[i] if 0 <= i < len(a) else f.zero()


def pdivmod_monic(num: List, den: List, f: F) -> Tuple[List, List]:
    """Divide by a monic polynomial: (quotient, remainder). Rational."""

    assert den and den[-1] == f.one(), "divisor must be monic"
    num = list(num)
    dd = len(den) - 1
    q = [f.zero()] * max(0, len(num) - dd)
    for i in range(len(num) - 1, dd - 1, -1):
        c = num[i]
        if c == f.zero():
            continue
        q[i - dd] = c
        for j, v in enumerate(den):
            num[i - dd + j] = f.sub(num[i - dd + j], f.mul(c, v))
    return ptrim(q, f), ptrim(num, f)


# =============================================================================
# Value DAG (shared): inputs, affine combinations, products
# =============================================================================


class Node:
    __slots__ = ("kind", "terms", "const", "left", "right", "poly", "dep", "label")

    def __init__(self, kind, terms=None, const=None, left=None, right=None, label=""):
        self.kind = kind  # 'inp' | 'lin' | 'mul'
        self.terms = terms or []  # [(int coefficient, Node)] for 'lin'
        self.const = const  # field element or None, for 'lin'
        self.left = left
        self.right = right
        self.label = label


def inp(label: str) -> Node:
    return Node("inp", label=label)


def lin(terms, const=None) -> Node:
    return Node("lin", terms=list(terms), const=const)


def mul(a: Node, b: Node) -> Node:
    return Node("mul", left=a, right=b)


def dag_walk(root: Node):
    seen: Dict[int, Node] = {}
    stack = [root]
    while stack:
        n = stack.pop()
        if id(n) in seen:
            continue
        seen[id(n)] = n
        if n.kind == "lin":
            stack.extend(node for _, node in n.terms)
        elif n.kind == "mul":
            stack.append(n.left)
            stack.append(n.right)
    return list(seen.values())


def count_mults(root: Node) -> int:
    return sum(1 for n in dag_walk(root) if n.kind == "mul")


def count_adds(root: Node, f: F) -> int:
    """Share-aware: each distinct lin node pays (#terms-1) + (1 if key const)."""

    total = 0
    for n in dag_walk(root):
        if n.kind == "lin":
            total += max(0, len(n.terms) - 1)
            if n.const is not None and n.const != f.zero():
                total += 1
    return total


def dag_depth(root: Node, input_depth: Dict[str, int]) -> int:
    memo: Dict[int, int] = {}

    def go(n: Node) -> int:
        if id(n) in memo:
            return memo[id(n)]
        if n.kind == "inp":
            d = input_depth[n.label]
        elif n.kind == "lin":
            d = max((go(node) for _, node in n.terms), default=0)
        else:
            d = 1 + max(go(n.left), go(n.right))
        memo[id(n)] = d
        return d

    return go(root)


def dag_eval(root: Node, input_poly: Dict[str, List], f: F) -> List:
    memo: Dict[int, List] = {}

    def go(n: Node) -> List:
        if id(n) in memo:
            return memo[id(n)]
        if n.kind == "inp":
            p = list(input_poly[n.label])
        elif n.kind == "lin":
            p = []
            for c, node in n.terms:
                p = padd(p, pscal(go(node), f.c(c), f), f)
            if n.const is not None:
                p = padd(p, [n.const], f)
        else:
            p = pmul(go(n.left), go(n.right), f)
        memo[id(n)] = p
        return p

    return go(root)


# =============================================================================
# Towers (as gadget inputs)
# =============================================================================


def random_tower(L: int, f: F, rng: random.Random) -> List[List]:
    """Hs[i] = arbitrary monic degree-2^i polynomial; Hs[0] = x."""

    Hs = [[f.zero(), f.one()]]
    for i in range(1, L + 1):
        d = 1 << i
        Hs.append([f.rand(rng) for _ in range(d)] + [f.one()])
    return Hs


def tower_nodes(L: int) -> List[Node]:
    return [inp(f"H{i}") for i in range(L + 1)]  # H0 = x


def tower_env(Hs: List[List]) -> Dict[str, List]:
    return {f"H{i}": Hs[i] for i in range(len(Hs))}


def ideal_depths(L: int) -> Dict[str, int]:
    """Model: the tower itself at depth i per level (H0 = x at 0)."""

    return {f"H{i}": i for i in range(L + 1)}


# =============================================================================
# Builders (encode side). Keys are consumed from a list in canonical order.
# =============================================================================


class KeyFeed:
    def __init__(self, keys: List):
        self.keys = keys
        self.i = 0

    def take(self):
        v = self.keys[self.i]
        self.i += 1
        return v


def build_FB(j: int, ks: KeyFeed, H: List[Node], f: F) -> Node:
    """Free block: all polynomials of degree < 2^j; consumes 2^j keys."""

    if j == 0:
        return lin([], const=ks.take())
    if j == 1:
        a, b = ks.take(), ks.take()
        xa = lin([(1, H[0])], const=a)
        return lin([(1, mul(xa, xa)), (-1, H[1])], const=b)
    S = build_FB(j - 1, ks, H, f)
    D = build_MB(j - 2, ks, H, f)
    Fb = build_FB(j - 2, ks, H, f)
    E = lin([(1, H[j - 1]), (1, S)])
    return lin([(1, mul(lin([(1, E), (1, D)]), lin([(1, E), (-1, D)]))),
                (-1, H[j]), (1, Fb)])


def build_MB(j: int, ks: KeyFeed, H: List[Node], f: F) -> Node:
    """Monic block of degree 2^j, all lower coefficients free; 2^j keys."""

    if j == 0:
        return lin([(1, H[0])], const=ks.take())
    if j == 1:
        a, b = ks.take(), ks.take()
        xa = lin([(1, H[0])], const=a)
        return lin([(1, mul(xa, xa))], const=b)
    S = build_FB(j - 1, ks, H, f)
    D = build_MB(j - 2, ks, H, f)
    Fb = build_FB(j - 2, ks, H, f)
    E = lin([(1, H[j - 1]), (1, S)])
    return lin([(1, mul(lin([(1, E), (1, D)]), lin([(1, E), (-1, D)]))), (1, Fb)])


def build_QB(t: int, ks: KeyFeed, H: List[Node], f: F) -> Node:
    """Monic degree 2^t-1, all lower coefficients free; 2^t-1 keys."""

    if t == 1:
        return lin([(1, H[0])], const=ks.take())
    if t == 2:
        a, b, c = ks.take(), ks.take(), ks.take()
        return lin([(1, mul(lin([(1, H[1])], const=a), lin([(1, H[0])], const=b)))],
                   const=c)
    W = build_QB(t - 1, ks, H, f)
    V = build_FB(t - 1, ks, H, f)
    return lin([(1, mul(H[t - 1], W)), (1, V)])


def build_QP(t: int, ks: KeyFeed, H: List[Node], f: F) -> Node:
    """Peeled balanced QB: monic degree 2^t-1, EXACT paper budget.

    QP(2^t-1) = (H_{2^{t-1}} + gamma) * QP(2^{t-1}-1) + QP'(2^{t-1}-1),
    base QP(3) = (H_2+a)(x+b)+c.  Both children recurse in parallel; the
    one-degree offset (deg H = m+1 vs deg W = deg B = m) keeps every window
    clean.  Key order: [gamma, W-keys..., B-keys...].
    """

    if t == 1:
        return lin([(1, H[0])], const=ks.take())
    if t == 2:
        a, b, c = ks.take(), ks.take(), ks.take()
        return lin([(1, mul(lin([(1, H[1])], const=a), lin([(1, H[0])], const=b)))],
                   const=c)
    g = ks.take()
    W = build_QP(t - 1, ks, H, f)
    B = build_QP(t - 1, ks, H, f)
    return lin([(1, mul(lin([(1, H[t - 1])], const=g), W)), (1, B)])


def build_QO(d: int, ks: KeyFeed, H: List[Node], f: F) -> Node:
    """Peeled monic family for EVERY odd degree d, exact budget (d-1)/2 mults.

    QO(d) = (H_h + U) * W + B,  h = 2^floor(log2 d),  w = d - h,
    with U = QO(2h-d) inside the factor and W = B = QO(w) — all three
    children odd-degree monic, recursing in parallel.  Mersenne d delegates
    to QP.  Key order: [U-keys..., W-keys..., B-keys...].
    """

    if d == 1:
        return lin([(1, H[0])], const=ks.take())
    t = d.bit_length()
    if d == (1 << t) - 1:
        return build_QP(t, ks, H, f)
    h = 1 << (t - 1)
    U = build_QO(2 * h - d, ks, H, f)
    W = build_QO(d - h, ks, H, f)
    B = build_QO(d - h, ks, H, f)
    return lin([(1, mul(lin([(1, H[t - 1]), (1, U)]), W)), (1, B)])


# =============================================================================
# Decoders (explicit rational schedules)
# =============================================================================


def _read_S_window(R: List, Hc: List, m2: int, dsq_leading_row: Optional[int], f: F) -> List:
    """
    Recover S (deg < m2) from R = 2*H*S + S^2 - D^2 + F, reading rows
    2^j-1 .. m2 descending.  H = Hc is known monic of degree m2.  D^2 is monic
    of degree exactly `dsq_leading_row` (or None); F lives strictly below m2.
    Pivot at row m2+i is 2*S_i.
    """

    S = [f.zero()] * m2
    for i in range(m2 - 1, -1, -1):
        r = m2 + i
        acc = pcoeff(R, r, f)
        # known part of 2*H*S at this row: indices a<m2 with S-index r-a>i
        for a in range(max(0, r - (m2 - 1)), m2):
            si = r - a
            if si > i:
                acc = f.sub(acc, f.mul(f.c(2), f.mul(pcoeff(Hc, a, f), S[si])))
        # S^2 at this row: pairs (p,q) with p+q=r, both > i (known descending)
        for p_ in range(i + 1, m2):
            q_ = r - p_
            if i < q_ < m2:
                acc = f.sub(acc, f.mul(S[p_], S[q_]))
        # -D^2 leading term (known -1) lands exactly at row m2 when i == 0
        if dsq_leading_row is not None and r == dsq_leading_row:
            acc = f.add(acc, f.one())
        S[i] = f.half(acc)
    return S


def _read_sqrt_window(R2: List, m4: int, f: F) -> List:
    """
    Recover the lower coefficients of monic D (deg m4) from R2 = -D^2 + F
    with deg F < m4: rows m4+i for i = m4-1..0, pivot -2*D_i (inline windowed
    monic square root).
    """

    D = [f.zero()] * m4  # lower coefficients; leading 1 implicit
    for i in range(m4 - 1, -1, -1):
        r = m4 + i
        acc = pcoeff(R2, r, f)
        # -D^2 known part at row r: cross pairs below leading, both > i
        for p_ in range(i + 1, m4):
            q_ = r - p_
            if i < q_ < m4:
                acc = f.add(acc, f.mul(D[p_], D[q_]))
        D[i] = f.half(f.sub(f.zero(), acc))
    return D


def _full_D(Dlow: List, f: F) -> List:
    return ptrim(list(Dlow) + [f.one()], f)


def decode_FB(c: List, j: int, Hs: List[List], f: F) -> List:
    """Inverse of build_FB: coefficients (deg < 2^j) -> keys, same order."""

    if j == 0:
        return [pcoeff(c, 0, f)]
    if j == 1:
        # (x+a)^2 - H_2 + b:  R := c + H_2 = x^2 + 2a x + (a^2 + b)
        R = padd(c, Hs[1], f)
        assert pcoeff(R, 2, f) == f.one(), "FB(2): bad leading"
        a = f.half(pcoeff(R, 1, f))
        b = f.sub(pcoeff(R, 0, f), f.mul(a, a))
        return [a, b]
    m2, m4 = 1 << (j - 1), 1 << (j - 2)
    Hc = Hs[j - 1]
    # R = 2*H*S + S^2 - D^2 + F
    R = padd(psub(c, pmul(Hc, Hc, f), f), Hs[j], f)
    S = _read_S_window(R, Hc, m2, dsq_leading_row=m2, f=f)
    Sp = ptrim(list(S), f)
    R2 = psub(psub(R, pscal(pmul(Hc, Sp, f), f.c(2), f), f), pmul(Sp, Sp, f), f)
    Dlow = _read_sqrt_window(R2, m4, f)
    Dfull = _full_D(Dlow, f)
    Fp = padd(R2, pmul(Dfull, Dfull, f), f)
    assert len(Fp) <= m4, "FB: residual too large"
    return (decode_FB(Sp, j - 1, Hs, f)
            + decode_MB(Dlow, j - 2, Hs, f)
            + decode_FB(Fp, j - 2, Hs, f))


def decode_MB(clow: List, j: int, Hs: List[List], f: F) -> List:
    """Inverse of build_MB: LOWER coefficients of the monic value -> keys."""

    if j == 0:
        # x + a
        return [pcoeff(clow, 0, f)]
    if j == 1:
        # (x+a)^2 + b
        a = f.half(pcoeff(clow, 1, f))
        b = f.sub(pcoeff(clow, 0, f), f.mul(a, a))
        return [a, b]
    m2, m4 = 1 << (j - 1), 1 << (j - 2)
    Hc = Hs[j - 1]
    cfull = ptrim(list(clow) + [f.zero()] * ((1 << j) - len(clow)) + [f.one()], f)
    R = psub(cfull, pmul(Hc, Hc, f), f)  # = 2HS + S^2 - D^2 + F  (+ x^{2^j} cancelled)
    S = _read_S_window(R, Hc, m2, dsq_leading_row=m2, f=f)
    Sp = ptrim(list(S), f)
    R2 = psub(psub(R, pscal(pmul(Hc, Sp, f), f.c(2), f), f), pmul(Sp, Sp, f), f)
    Dlow = _read_sqrt_window(R2, m4, f)
    Dfull = _full_D(Dlow, f)
    Fp = padd(R2, pmul(Dfull, Dfull, f), f)
    assert len(Fp) <= m4, "MB: residual too large"
    return (decode_FB(Sp, j - 1, Hs, f)
            + decode_MB(Dlow, j - 2, Hs, f)
            + decode_FB(Fp, j - 2, Hs, f))


def decode_QB(clow: List, t: int, Hs: List[List], f: F) -> List:
    """Inverse of build_QB: LOWER coefficients of the monic value -> keys."""

    if t == 1:
        return [pcoeff(clow, 0, f)]
    if t == 2:
        # (H_2 + a)(x + b) + c, H_2 = x^2 + h1 x + h0
        h0, h1 = pcoeff(Hs[1], 0, f), pcoeff(Hs[1], 1, f)
        b = f.sub(pcoeff(clow, 2, f), h1)
        a = f.sub(f.sub(pcoeff(clow, 1, f), h0), f.mul(h1, b))
        c0 = f.sub(pcoeff(clow, 0, f), f.mul(f.add(h0, a), b))
        return [a, b, c0]
    deg = (1 << t) - 1
    cfull = ptrim(list(clow) + [f.zero()] * (deg - len(clow)) + [f.one()], f)
    W, V = pdivmod_monic(cfull, Hs[t - 1], f)
    assert W and W[-1] == f.one() and len(W) - 1 == (1 << (t - 1)) - 1
    return decode_QB(W[:-1], t - 1, Hs, f) + decode_FB(V, t - 1, Hs, f)


def decode_QP(clow: List, t: int, Hs: List[List], f: F) -> List:
    """Inverse of build_QP: LOWER coefficients of the monic value -> keys.

    Schedule: (1) read W's lower coefficients from rows [2^{t-1}, 2^t-2]
    against the known monic H_{2^{t-1}} (gamma*W + B live strictly below);
    (2) gamma = (residual row 2^{t-1}-1) - 1, since W and B are monic;
    (3) B = residual - gamma*W.  Always rational.
    """

    if t == 1:
        return [pcoeff(clow, 0, f)]
    if t == 2:
        h0, h1 = pcoeff(Hs[1], 0, f), pcoeff(Hs[1], 1, f)
        b = f.sub(pcoeff(clow, 2, f), h1)
        a = f.sub(f.sub(pcoeff(clow, 1, f), h0), f.mul(h1, b))
        c0 = f.sub(pcoeff(clow, 0, f), f.mul(f.add(h0, a), b))
        return [a, b, c0]
    m = (1 << (t - 1)) - 1
    deg = (1 << t) - 1
    cfull = ptrim(list(clow) + [f.zero()] * (deg - len(clow)) + [f.one()], f)
    H = Hs[t - 1]  # known monic, degree m+1
    W = [f.zero()] * m + [f.one()]  # monic, lower coeffs unknown
    for i in range(m - 1, -1, -1):
        r = (m + 1) + i
        acc = pcoeff(cfull, r, f)
        for a_ in range(0, m + 1):  # H indices below leading
            wi = r - a_
            if i < wi <= m:
                acc = f.sub(acc, f.mul(pcoeff(H, a_, f), W[wi]))
        W[i] = acc  # pivot 1: H leading * W_i
    R = psub(cfull, pmul(H, W, f), f)  # = gamma*W + B, degree m
    g = f.sub(pcoeff(R, m, f), f.one())
    B = psub(R, pscal(W, g, f), f)
    assert pcoeff(B, m, f) == f.one(), "QP: B not monic"
    return [g] + decode_QP(W[:-1], t - 1, Hs, f) + decode_QP(B[:-1], t - 1, Hs, f)


def decode_QO(clow: List, d: int, Hs: List[List], f: F) -> List:
    """Inverse of build_QO: LOWER coefficients of the monic value -> keys.

    Schedule: (1) W's window rows [h, d-1] is H*W plus the single known
    leading 1 of U*W at row h — peel W against the known monic H;
    (2) residual R = U*W + B: peel U against W's monic leading descending,
    with U_0 read at row w where B contributes its pinned leading 1;
    (3) B = R - U*W.  Always rational, characteristic-independent.
    """

    if d == 1:
        return [pcoeff(clow, 0, f)]
    t = d.bit_length()
    if d == (1 << t) - 1:
        return decode_QP(clow, t, Hs, f)
    h = 1 << (t - 1)
    w = d - h
    ud = 2 * h - d
    cfull = ptrim(list(clow) + [f.zero()] * (d - len(clow)) + [f.one()], f)
    Hc = Hs[t - 1]
    W = [f.zero()] * w + [f.one()]
    for i in range(w - 1, -1, -1):
        r = h + i
        acc = pcoeff(cfull, r, f)
        for a_ in range(0, h):
            wi = r - a_
            if i < wi <= w:
                acc = f.sub(acc, f.mul(pcoeff(Hc, a_, f), W[wi]))
        if i == 0:
            acc = f.sub(acc, f.one())  # leading 1 of U*W at row h
        W[i] = acc
    R = psub(cfull, pmul(Hc, W, f), f)  # = U*W + B, degree h
    U = [f.zero()] * ud + [f.one()]
    for j in range(ud - 1, -1, -1):
        r = w + j
        acc = pcoeff(R, r, f)
        for a_ in range(j + 1, ud + 1):
            wi = r - a_
            if 0 <= wi < w:
                acc = f.sub(acc, f.mul(U[a_], W[wi]))
        if j == 0:
            acc = f.sub(acc, f.one())  # pinned leading of monic B at row w
        U[j] = acc
    B = psub(R, pmul(U, W, f), f)
    assert pcoeff(B, w, f) == f.one(), "QO: B not monic"
    return (decode_QO(U[:-1], ud, Hs, f) + decode_QO(W[:-1], w, Hs, f)
            + decode_QO(B[:-1], w, Hs, f))


# =============================================================================
# Paper baseline (measured through poly_schedule's actual builders)
# =============================================================================


def paper_Q_counts(t: int, prime: int = MERSENNE61) -> Tuple[int, int, int]:
    """(mults, adds, depth) of the paper's Q_{2^t-1} given an ideal tower.

    Multiplications are exact gate counts.  Additions are counted with the
    same affine convention as `count_adds` (terms-1 per gate factor plus one
    per key constant), on the gates the Q call creates.  Depth pins the tower
    wires at depth i (H_{2^i} at i) to isolate the gadget's own ledger.
    """

    import tools.poly_schedule as ps

    field = ps.Field(modulus=prime)
    rng = random.Random(7)
    b = ps.ChainBuilder(field)
    x = b.x
    # tower up to H_{2^{t-1}}, built the paper's way (square differences)
    Hs = [x, ps._paper_H2(b, rng.randrange(prime), rng.randrange(prime))]
    for i in range(2, t):
        shift = x.add_const(field.coerce(rng.randrange(prime)), field)
        Hs.append(ps._paper_square_diff(b, Hs[-1], shift)
                  .add_const(field.coerce(rng.randrange(prime)), field))
    tower_gates = len(b.gates)
    tower_wires = {g.out_wire for g in b.gates}

    alpha = [rng.randrange(prime) for _ in range((1 << t) - 1)]
    q = ps._paper_Q_known_powers(b, t, alpha, Hs[:t])

    gates = b.gates[tower_gates:]
    mults = len(gates)

    def aff_adds(a) -> int:
        n = max(0, len(a.terms) - 1)
        if not field.is_zero(a.const):
            n += 1 + (1 if a.terms else 0) - 1 if a.terms else 1
        return n

    # (terms-1) + 1-if-const, matching count_adds
    def aff_adds2(a) -> int:
        n = max(0, len(a.terms) - 1)
        if not field.is_zero(a.const):
            n += 1
        return n

    adds = sum(aff_adds2(g.left) + aff_adds2(g.right) for g in gates) + aff_adds2(q)

    # depth with the tower pinned at ideal levels
    pin = {}
    for i, hform in enumerate(Hs):
        for w in hform.terms:
            if w in tower_wires:
                pin[w] = i
    depth: Dict[int, int] = dict(pin)
    for g in b.gates:
        if g.out_wire in pin:
            continue
        d = 0
        for a in (g.left, g.right):
            for w in a.terms:
                d = max(d, depth.get(w, 0))
        depth[g.out_wire] = d + 1
    qdepth = max((depth.get(w, 0) for w in q.terms), default=0)
    return mults, adds, qdepth


def paper_Qodd_counts(k: int, l: int, prime: int = MERSENNE61) -> Tuple[int, int, int, int]:
    """(deg, mults, adds, depth) of the paper's Q_{2^{l+1}k + 2^l - 1}.

    Tower H_2..H_{2^l} is prebuilt (paper square-difference steps) and not
    charged; everything the gadget itself builds — including the higher
    keyed tower levels inside its internal T call — is charged, since those
    carry the gadget's own parameters.  Depth pins the prebuilt tower at
    ideal levels.
    """

    import tools.poly_schedule as ps

    field = ps.Field(modulus=prime)
    rng = random.Random(11)
    b = ps.ChainBuilder(field)
    x = b.x
    Hs = [x, ps._paper_H2(b, rng.randrange(prime), rng.randrange(prime))]
    for i in range(2, l + 1):
        shift = x.add_const(field.coerce(rng.randrange(prime)), field)
        Hs.append(ps._paper_square_diff(b, Hs[-1], shift)
                  .add_const(field.coerce(rng.randrange(prime)), field))
    tower_gates = len(b.gates)
    tower_wires = {g.out_wire for g in b.gates}

    deg = (1 << (l + 1)) * k + ((1 << l) - 1)
    alpha = [rng.randrange(prime) for _ in range(deg)]
    q = ps._paper_Q_2lp1k_minus_1(b, k, l, alpha, Hs[: l + 1])

    gates = b.gates[tower_gates:]
    mults = len(gates)

    def aff_adds(a) -> int:
        n = max(0, len(a.terms) - 1)
        if not field.is_zero(a.const):
            n += 1
        return n

    adds = sum(aff_adds(g.left) + aff_adds(g.right) for g in gates) + aff_adds(q)

    pin = {}
    for i, hform in enumerate(Hs):
        for wv in hform.terms:
            if wv in tower_wires:
                pin[wv] = i
    depth: Dict[int, int] = dict(pin)
    for g in b.gates:
        if g.out_wire in pin:
            continue
        dd = 0
        for a in (g.left, g.right):
            for wv in a.terms:
                dd = max(dd, depth.get(wv, 0))
        depth[g.out_wire] = dd + 1
    qdepth = max((depth.get(wv, 0) for wv in q.terms), default=0)
    return deg, mults, adds, qdepth


# =============================================================================
# Measurements and verification
# =============================================================================


def gadget_counts(kind: str, size_log: int, f: F) -> Tuple[int, int, int, int]:
    """(keys, mults, adds, depth) for FB/MB(2^j) or QB(2^t-1) at ideal tower."""

    L = size_log + 1
    H = tower_nodes(L)
    nkeys = ((1 << size_log) - 1) if kind in ("QB", "QP") else (1 << size_log)
    ks = KeyFeed([f.c(1)] * nkeys)
    node = {"FB": build_FB, "MB": build_MB, "QB": build_QB,
            "QP": build_QP}[kind](size_log, ks, H, f)
    assert ks.i == nkeys
    return nkeys, count_mults(node), count_adds(node, f), dag_depth(node, ideal_depths(L))


def roundtrip(kind: str, size_log: int, f: F, rng: random.Random) -> None:
    L = size_log + 1
    Hn = tower_nodes(L)
    Hs = random_tower(L, f, rng)
    env = tower_env(Hs)
    nkeys = ((1 << size_log) - 1) if kind in ("QB", "QP") else (1 << size_log)

    build = {"FB": build_FB, "MB": build_MB, "QB": build_QB, "QP": build_QP}[kind]
    decode = {"FB": decode_FB, "MB": decode_MB, "QB": decode_QB,
              "QP": decode_QP}[kind]

    # keys -> coefficients -> keys
    keys = [f.rand(rng) for _ in range(nkeys)]
    val = dag_eval(build(size_log, KeyFeed(keys), Hn, f), env, f)
    if kind == "FB":
        assert len(val) <= (1 << size_log), f"{kind}({size_log}): degree too big"
        got = decode(val, size_log, Hs, f)
    else:
        deg = ((1 << size_log) - 1) if kind in ("QB", "QP") else (1 << size_log)
        assert len(val) - 1 == deg and val[-1] == f.one(), f"{kind}: not monic deg {deg}"
        got = decode(val[:-1], size_log, Hs, f)
    assert got == [f.c(k) for k in keys], f"{kind}(2^{size_log}) key round-trip failed"

    # coefficients -> keys -> coefficients  (surjectivity / bijection)
    ncoef = nkeys
    coeffs = [f.rand(rng) for _ in range(ncoef)]
    keys2 = decode(list(coeffs), size_log, Hs, f)
    val2 = dag_eval(build(size_log, KeyFeed(keys2), Hn, f), env, f)
    if kind == "FB":
        re = [pcoeff(val2, i, f) for i in range(ncoef)]
    else:
        assert val2[-1] == f.one()
        re = [pcoeff(val2, i, f) for i in range(ncoef)]
    assert re == [f.c(c) for c in coeffs], f"{kind}(2^{size_log}) coeff round-trip failed"


def counts_QO(d: int, f: F) -> Tuple[int, int, int]:
    """(mults, adds, depth) of QO(d) at the ideal tower."""

    L = d.bit_length()
    H = tower_nodes(L)
    ks = KeyFeed([f.c(1)] * d)
    node = build_QO(d, ks, H, f)
    assert ks.i == d
    return count_mults(node), count_adds(node, f), dag_depth(node, ideal_depths(L))


def roundtrip_QO(d: int, f: F, rng: random.Random) -> None:
    L = d.bit_length()
    Hn = tower_nodes(L)
    Hs = random_tower(L, f, rng)
    env = tower_env(Hs)
    keys = [f.rand(rng) for _ in range(d)]
    val = dag_eval(build_QO(d, KeyFeed(keys), Hn, f), env, f)
    assert len(val) - 1 == d and val[-1] == f.one(), f"QO({d}): not monic degree {d}"
    got = decode_QO(val[:-1], d, Hs, f)
    assert got == [f.c(k) for k in keys], f"QO({d}) key round-trip failed"
    coeffs = [f.rand(rng) for _ in range(d)]
    keys2 = decode_QO(list(coeffs), d, Hs, f)
    val2 = dag_eval(build_QO(d, KeyFeed(keys2), Hn, f), env, f)
    re = [pcoeff(val2, i, f) for i in range(d)]
    assert re == [f.c(c) for c in coeffs], f"QO({d}) coeff round-trip failed"


def selftest(max_log: int = 7, verbose: bool = True) -> None:
    fields = [("GF(2^61-1)", F(MERSENNE61)), ("GF(1009)", F(1009))]
    f2 = F(2)
    rng2 = random.Random(99)
    for t in range(1, max_log + 1):
        for _ in range(5):
            roundtrip("QP", t, f2, rng2)
    if verbose:
        print(f"  GF(2): peeled QP up to 2^{max_log}-1: ok (char-independent)")
    for name, f in fields:
        rng = random.Random(12345)
        for j in range(0, max_log + 1):
            for kind in ("FB", "MB"):
                for _ in range(3):
                    roundtrip(kind, j, f, rng)
        for t in range(1, max_log + 1):
            for _ in range(3):
                roundtrip("QB", t, f, rng)
                roundtrip("QP", t, f, rng)
        for t in range(2, max_log + 1):
            nk, m, a, d = gadget_counts("QP", t, f)
            assert m == (1 << (t - 1)) - 1, f"QP({t}): mults {m} != paper"
            assert a == (1 if t == 1 else 5 * (1 << (t - 2)) - 2), \
                f"QP({t}): adds {a} != paper ledger"
            assert d == t, f"QP({t}): depth {d} != {t}"
        if verbose:
            print(f"  {name}: FB/MB up to 2^{max_log}, QB up to 2^{max_log}-1: ok")
    for name, f in [("GF(2^61-1)", F(MERSENNE61)), ("GF(2)", F(2))]:
        rng = random.Random(777)
        for d in list(range(1, 132, 2)) + [161, 195, 201, 231, 255, 257]:
            m, a, dep = counts_QO(d, F(MERSENNE61))
            assert m == (d - 1) // 2, f"QO({d}): mults {m} != {(d - 1) // 2}"
            roundtrip_QO(d, f, rng)
        if verbose:
            print(f"  {name}: QO all odd d <= 131 (+ spot to 257): ok, "
                  f"mults == (d-1)/2 asserted")
    fq = F(None)
    rngq = random.Random(5)
    for j in range(0, 5):
        roundtrip("FB", j, fq, rngq)
        roundtrip("MB", j, fq, rngq)
    for t in range(1, 5):
        roundtrip("QB", t, fq, rngq)
        roundtrip("QP", t, fq, rngq)
    for d in (5, 11, 13, 21, 27):
        roundtrip_QO(d, fq, rngq)
    if verbose:
        print("  exact rationals: sizes up to 31: ok")
        print("selftest OK (explicit rational decoders, both directions)")


def table(max_log: int = 8) -> None:
    f = F(MERSENNE61)
    print("Q_{2^t-1} given the tower: paper (sequential fill) vs shell vs peeled")
    print(f"{'t':>2} {'deg':>5} | {'m: paper':>8} {'shell':>6} {'peel':>5} | "
          f"{'a: paper':>8} {'shell':>6} {'peel':>5} | {'d: paper':>8} {'shell':>6} {'peel':>5}")
    for t in range(2, max_log + 1):
        pm, pa, pd = paper_Q_counts(t)
        _, bm, ba, bd = gadget_counts("QB", t, f)
        _, qm, qa, qd = gadget_counts("QP", t, f)
        print(f"{t:>2} {(1 << t) - 1:>5} | {pm:>8} {bm:>6} {qm:>5} | "
              f"{pa:>8} {ba:>6} {qa:>5} | {pd:>8} {bd:>6} {qd:>5}")
    print("  (peel = (H+gamma)*W + B, both children monic; m and a match the paper EXACTLY)")
    print()
    print("odd-degree family Q_{2^{l+1}k+2^l-1}: paper (T + seam fill) vs peeled QO")
    print(f"{'(k,l)':>7} {'deg':>4} | {'m: paper':>8} {'QO':>4} | {'a: paper':>8} {'QO':>4} | "
          f"{'d: paper':>8} {'QO':>4}")
    for l in (1, 2, 3):
        for k in (1, 2, 4, 8, 16):
            deg, pm, pa, pd = paper_Qodd_counts(k, l)
            if deg > 300:
                continue
            m, a, dd = counts_QO(deg, f)
            print(f"({k},{l})".rjust(7) + f" {deg:>4} | {pm:>8} {m:>4} | {pa:>8} {a:>4} | "
                  f"{pd:>8} {dd:>4}")
    print("  (QO needs the tower up to 2^floor(log2 deg) given; the paper's version")
    print("   self-builds its upper levels with its own keys and returns them as")
    print("   byproducts — integration accounting differs, see the report)")
    print()
    print("free / monic blocks (no direct paper twin; role of the fill A):")
    print(f"{'kind':>4} {'j':>2} {'keys':>5} {'mults':>6} {'m/key':>6} {'adds':>6} {'depth':>6}")
    for kind in ("FB", "MB"):
        for j in range(1, max_log + 1):
            nk, m, a, d = gadget_counts(kind, j, f)
            print(f"{kind:>4} {j:>2} {nk:>5} {m:>6} {m / nk:>6.3f} {a:>6} {d:>6}")


def hybrid(max_log: int = 12, cutoffs=(3, 5, 7)) -> None:
    """Shells above a cutoff size, paper-style sequential gadgets below.

    Below the cutoff the stubs use the paper's exact Q ledger
    (m = 2^{t-1}-1, a = 5*2^{t-2}-2, measured depth) and a fill-model stub for
    FB/MB (m = keys/2, a = 1.25*keys, depth 2j-2), so the FB column below the
    cutoff is a model, not a measurement; everything above the cutoff is the
    exact shell recurrence.
    """

    # measured (chain sweep) through t=9; the ledger bound floor((t+1)^2/4)
    # beyond that — the paper depth is genuinely quadratic in t
    paper_d = {1: 1, 2: 2, 3: 4, 4: 6, 5: 8, 6: 11, 7: 14, 8: 18, 9: 22}

    def run(c: int, L: int):
        FBm, FBa, FBd = {}, {}, {}
        MBm, MBa, MBd = {}, {}, {}
        QBm, QBa, QBd = {}, {}, {}
        for j in range(0, L + 1):
            if j <= c:
                keys = 1 << j
                FBm[j] = MBm[j] = max(0, keys // 2) if j >= 1 else 0
                FBa[j] = MBa[j] = (5 * keys) // 4
                FBd[j] = MBd[j] = max(j, 2 * j - 2)
            else:
                FBm[j] = 1 + FBm[j - 1] + MBm[j - 2] + FBm[j - 2]
                FBa[j] = 5 + FBa[j - 1] + MBa[j - 2] + FBa[j - 2]
                FBd[j] = max(1 + max(j - 1, FBd[j - 1], MBd[j - 2]), j, FBd[j - 2])
                MBm[j] = FBm[j]
                MBa[j] = FBa[j] - 1
                MBd[j] = max(1 + max(j - 1, FBd[j - 1], MBd[j - 2]), FBd[j - 2])
        for t in range(1, L + 1):
            if t <= c:
                QBm[t] = (1 << (t - 1)) - 1
                QBa[t] = 1 if t == 1 else 5 * (1 << (t - 2)) - 2
                QBd[t] = paper_d.get(t, ((t + 1) * (t + 1)) // 4)
            else:
                QBm[t] = 1 + QBm[t - 1] + FBm[t - 1]
                QBa[t] = 1 + QBa[t - 1] + FBa[t - 1]
                QBd[t] = max(1 + max(t - 1, QBd[t - 1]), FBd[t - 1])
        return QBm, QBa, QBd

    print("hybrid QB(2^t-1): shells above cutoff c, paper gadgets below")
    hdr = f"{'t':>2} {'deg':>5} {'paper m':>8} {'paper d':>7}"
    for c in cutoffs:
        hdr += f" | c={c}: {'m':>6} {'ovh%':>6} {'d':>3}"
    print(hdr)
    for t in range(2, max_log + 1):
        pm = (1 << (t - 1)) - 1
        pd = paper_d.get(t)
        if pd is None:
            pd = ((t + 1) * (t + 1)) // 4  # ledger bound
        row = f"{t:>2} {(1 << t) - 1:>5} {pm:>8} {pd:>7}"
        for c in cutoffs:
            QBm, QBa, QBd = run(c, max_log)
            ov = 100.0 * (QBm[t] - pm) / pm
            row += f" |     {QBm[t]:>6} {ov:>6.1f} {QBd[t]:>3}"
        print(row)


def project(ns=(17, 63, 127, 253, 511, 1021, 2045, 4093)) -> None:
    """Projected full-construction heights, two levels of caution.

    "QP-only" substitutes ONLY the verified peeled known-powers gadget
    (depth t) and leaves every spine, seam fill and good-polynomial gadget
    byte-for-byte as the paper builds them — no assumptions at all.  This
    alone removes the quadratic term: the tower recurrence's q_t driver was
    the sole source.  "full peel" additionally prices the odd-degree family
    at ceil(log2 deg) (verified at its interface) and the good-polynomial
    gadgets at ceil(log2 deg)+1 (same spine recipe, unbuilt).  In both
    columns the keyed spines carry the towers, so the multiplication count
    stays exactly floor(n/2)+1 (no Rabin--Winograd drift) and additions only
    improve.
    """

    import math
    import tools.poly_schedule as ps
    from tools import polychain as pc

    pins: Dict[int, int] = {}
    mode = {"level": 0}  # 0 = off, 1 = QP-only, 2 = full

    def getarg(args, kw, name, pos):
        return kw[name] if name in kw else args[pos]

    def pin_form(form, d):
        for w in form.terms:
            if w not in pins or pins[w] > d:
                pins[w] = d

    def wrap(name, min_level, pin_of):
        orig = getattr(ps, name)

        def wrapped(*args, _orig=orig, _pin=pin_of, _lvl=min_level, **kw):
            out = _orig(*args, **kw)
            if mode["level"] >= _lvl:
                form = out[0] if isinstance(out, tuple) else out
                d = _pin(args, kw)
                if d is not None:
                    pin_form(form, d)
            return out

        setattr(ps, name, wrapped)
        return orig

    def pin_Q2(args, kw):
        k, l = getarg(args, kw, "k", 1), getarg(args, kw, "l", 2)
        deg = (1 << (l + 1)) * k + ((1 << l) - 1)
        return max(2, math.ceil(math.log2(deg))) if deg >= 3 else None

    saved = [
        ("_paper_Q_known_powers",
         wrap("_paper_Q_known_powers", 1,
              lambda a, kw: max(2, getarg(a, kw, "k", 1)))),
        ("_paper_Q_2lp1k_minus_1_with_powers",
         wrap("_paper_Q_2lp1k_minus_1_with_powers", 2, pin_Q2)),
        ("_paper_barQ_odd_with_H2_H4_with_powers",
         wrap("_paper_barQ_odd_with_H2_H4_with_powers", 2,
              lambda a, kw: max(2, math.ceil(math.log2(getarg(a, kw, "deg", 1)))) + 1)),
        ("_paper_barQ_odd_with_H2_H4",
         wrap("_paper_barQ_odd_with_H2_H4", 2,
              lambda a, kw: max(2, math.ceil(math.log2(getarg(a, kw, "deg", 1)))) + 1)),
    ]

    def height(prog):
        ch = prog.chain
        d: Dict[int, int] = {}
        for g in ch.gates:
            m = 0
            for a in (g.left, g.right):
                for w in a.terms:
                    m = max(m, d.get(w, 0))
            dep = m + 1
            if g.out_wire in pins:
                dep = min(dep, pins[g.out_wire])
            d[g.out_wire] = dep
        return max((d.get(w, 0) for w in ch.output.terms), default=0)

    try:
        print(f"{'n':>5} {'current':>8} {'QP-only':>8} {'full peel':>10} {'ceil(log2 n)':>12}")
        for n in ns:
            row = []
            for lvl in (0, 1, 2):
                mode["level"] = lvl
                pins.clear()
                row.append(height(pc.chain(n)))
            print(f"{n:>5} {row[0]:>8} {row[1]:>8} {row[2]:>10} "
                  f"{math.ceil(math.log2(n)):>12}")
    finally:
        for name, orig in saved:
            setattr(ps, name, orig)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    ap.add_argument("cmd", choices=["selftest", "table", "hybrid", "project"])
    ap.add_argument("--max-log", type=int, default=7)
    args = ap.parse_args()
    if args.cmd == "selftest":
        selftest(args.max_log)
    elif args.cmd == "hybrid":
        hybrid(args.max_log)
    elif args.cmd == "project":
        project()
    else:
        table(args.max_log)


if __name__ == "__main__":
    main()
