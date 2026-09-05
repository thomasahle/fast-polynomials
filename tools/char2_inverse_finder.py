#!/usr/bin/env python3
"""Explicit-inverse finder over F_2 for keyed state transitions (char-2 circuits).

The finder answers: given a circuit whose gates are products of affine forms in
wires/state polynomials plus fresh scalars, can the unknowns (fresh scalars and
the unknown coefficients of the state polynomials) be recovered from the visible
coefficient rows of the output polynomials by a *causal table of unit pivots*?
Every step it takes is an explicit decoding expression, never a rank test:

  * unit pivot   -- a visible row that, after substituting everything already
                    decoded, reads  k + (expression without k) ; over F_2 a
                    nonzero ground pivot is 1, so k = that expression.
  * Frobenius    -- optional (``frobenius=True``): a row of the form
                    k^2 + (expression without k); on a perfect field k is the
                    unique square root.  Tables using it are marked 'Frob'.

Solutions are *parametric* (k may be expressed through unknowns decoded later)
and are closed at the end by back-substitution; the closed forms are written in
the observed coefficient symbols ``P[i]`` (row i of output P), so the answer IS
the decoder.  Monic division by a known factor appears as the sequence of unit
pivots it is (cf. Section 68 of better_bounds/char2_static_patterns.md).

On failure the exact obstruction is printed: the remaining unknowns and, for
every remaining row, the residual's shape in the unknowns (e.g. 'a*b + [P[3]]*c').
A *diagnostic only* translation-gauge report follows: the kernel of the
Jacobian of the coefficient map at random points over F_2 and over GF(2^8),
which names unknowns that shift together.  It is labelled as a diagnostic and
is never used as evidence of decodability (AGENTS.md rule 1).

Python API (see the docstrings of ``InverseFinder``)::

    fd = InverseFinder()
    x = fd.x
    s2, s1, a, c, d, e = fd.scalar('s2', 's1', 'a', 'c', 'd', 'e')
    C = fd.state_poly('C', 8, fixed={7: 0, 6: 0, 5: 1})   # unknown C_4..C_0
    S = fd.wire('S', (x + s2) * (x**2 + s1))
    fd.output('P', (S + a) * C + (x + c) * (x**2 + d) + e)
    res = fd.solve()
    print(res.report())

JSON/dict spec (``InverseFinder.from_spec``; expressions are Python syntax over
the declared names, ``^`` is accepted for ``**``)::

    {"state":   [{"name": "C", "degree": 8, "monic": true,
                  "fixed": {"7": 0, "6": 0, "5": 1}}],
     "scalars": ["s2", "s1", "a", "c", "d", "e"],
     "constraints": {"T_2": "H_2 + 1"},              # symbol -> expression
     "wires":   [["S", "(x+s2)*(x^2+s1)"]],
     "outputs": [{"name": "P", "expr": "(S+a)*C+(x+c)*(x^2+d)+e",
                  "visible": [10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]}],
     "options": {"frobenius": false, "prefer": "fewest"}}

Run:  python3 tools/char2_inverse_finder.py spec.json [--frobenius] [--prefer high]
"""
from __future__ import annotations

import argparse
import json
import os
import random
import sys
from dataclasses import dataclass, field
from typing import Dict, Iterable, List, Optional, Sequence, Tuple, Union

# ----------------------------------------------------------------------------
# GF(2^k) arithmetic (char2/gf2k.py; inline fallback keeps the tool standalone)
# ----------------------------------------------------------------------------
_REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
try:  # pragma: no cover - import path depends on checkout layout
    sys.path.insert(0, _REPO)
    from char2.gf2k import GF2k  # type: ignore
except Exception:  # pragma: no cover
    from dataclasses import dataclass as _dc

    @_dc(frozen=True)
    class GF2k:  # type: ignore
        k: int
        mod: int

        @property
        def mask(self) -> int:
            return (1 << self.k) - 1

        def mul(self, a: int, b: int) -> int:
            a &= self.mask
            b &= self.mask
            res = 0
            top = 1 << self.k
            while b:
                if b & 1:
                    res ^= a
                b >>= 1
                a <<= 1
                if a & top:
                    a ^= self.mod
            return res & self.mask

        def pow(self, a: int, e: int) -> int:
            r, base = 1, a & self.mask
            while e:
                if e & 1:
                    r = self.mul(r, base)
                e >>= 1
                if e:
                    base = self.mul(base, base)
            return r

        def inv(self, a: int) -> int:
            if a & self.mask == 0:
                raise ZeroDivisionError
            return self.pow(a, (1 << self.k) - 2)


GF2 = GF2k(1, 0b11)
GF256 = GF2k(8, 0x11B)

# ----------------------------------------------------------------------------
# Sparse multivariate polynomials over F_2 (exponents are NOT reduced: a^2 != a)
# ----------------------------------------------------------------------------
_NAMES: List[str] = []
_INDEX: Dict[str, int] = {}


def _vid(name: str) -> int:
    i = _INDEX.get(name)
    if i is None:
        i = len(_NAMES)
        _NAMES.append(name)
        _INDEX[name] = i
    return i


Mono = Tuple[Tuple[int, int], ...]  # sorted ((var_index, exponent), ...)


def _mmul(m1: Mono, m2: Mono) -> Mono:
    if not m1:
        return m2
    if not m2:
        return m1
    i = j = 0
    out: List[Tuple[int, int]] = []
    n1, n2 = len(m1), len(m2)
    while i < n1 and j < n2:
        a, ea = m1[i]
        b, eb = m2[j]
        if a == b:
            out.append((a, ea + eb))
            i += 1
            j += 1
        elif a < b:
            out.append(m1[i])
            i += 1
        else:
            out.append(m2[j])
            j += 1
    out.extend(m1[i:])
    out.extend(m2[j:])
    return tuple(out)


class F2Poly:
    """Element of F_2[symbols], stored as a frozenset of monomials (XOR-sum)."""

    __slots__ = ("t",)

    def __init__(self, terms: Iterable[Mono] = ()):
        self.t: frozenset = terms if isinstance(terms, frozenset) else frozenset(terms)

    # -- constructors ---------------------------------------------------
    @staticmethod
    def var(name: str) -> "F2Poly":
        return F2Poly(frozenset({((_vid(name), 1),)}))

    @staticmethod
    def const(c: int) -> "F2Poly":
        return ONE if c & 1 else ZERO

    @staticmethod
    def _coerce(o):
        if isinstance(o, F2Poly):
            return o
        if isinstance(o, int) and not isinstance(o, bool):
            return F2Poly.const(o)
        return NotImplemented

    # -- ring operations ------------------------------------------------
    def __add__(self, o):
        o = F2Poly._coerce(o)
        if o is NotImplemented:
            return NotImplemented
        return F2Poly(self.t ^ o.t)

    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__
    __xor__ = __add__

    def __neg__(self):
        return self

    def __mul__(self, o):
        o = F2Poly._coerce(o)
        if o is NotImplemented:
            return NotImplemented
        if not self.t or not o.t:
            return ZERO
        if o.t == _ONE_T:
            return self
        if self.t == _ONE_T:
            return o
        out: set = set()
        for m1 in self.t:
            for m2 in o.t:
                m = _mmul(m1, m2)
                if m in out:
                    out.discard(m)
                else:
                    out.add(m)
        return F2Poly(frozenset(out))

    __rmul__ = __mul__

    def square(self) -> "F2Poly":  # Frobenius: (sum m)^2 = sum m^2
        return F2Poly(frozenset(tuple((v, 2 * e) for v, e in m) for m in self.t))

    def __pow__(self, n: int) -> "F2Poly":
        if n < 0:
            raise ValueError("negative power")
        r, b = ONE, self
        while n:
            if n & 1:
                r = r * b
            n >>= 1
            if n:
                b = b.square()
        return r

    def __eq__(self, o):
        o = F2Poly._coerce(o)
        if o is NotImplemented:
            return NotImplemented
        return self.t == o.t

    def __hash__(self):
        return hash(self.t)

    def __bool__(self):
        return bool(self.t)

    # -- structure ------------------------------------------------------
    def is_zero(self) -> bool:
        return not self.t

    def is_ground(self) -> bool:
        return all(not m for m in self.t)

    def variables(self) -> set:
        return {_NAMES[v] for m in self.t for v, _ in m}

    def degree(self, name: str) -> int:
        """Degree in ``name`` (0 if absent; -1 for the zero polynomial)."""
        if not self.t:
            return -1
        vi = _INDEX.get(name)
        if vi is None:
            return 0
        d = 0
        for m in self.t:
            for v, e in m:
                if v == vi and e > d:
                    d = e
        return d

    def coeff_wrt(self, name: str, j: int) -> "F2Poly":
        """Coefficient of name^j (a polynomial in the other symbols)."""
        vi = _INDEX.get(name)
        out = []
        for m in self.t:
            e = 0
            rest = m
            for idx, (v, ee) in enumerate(m):
                if v == vi:
                    e = ee
                    rest = m[:idx] + m[idx + 1:]
                    break
            if e == j:
                out.append(rest)
        return F2Poly(frozenset(out))

    def subs(self, name: str, val: "F2Poly") -> "F2Poly":
        vi = _INDEX.get(name)
        if vi is None:
            return self
        keep = []
        by_exp: Dict[int, set] = {}
        for m in self.t:
            for idx, (v, e) in enumerate(m):
                if v == vi:
                    rest = m[:idx] + m[idx + 1:]
                    s = by_exp.setdefault(e, set())
                    if rest in s:
                        s.discard(rest)
                    else:
                        s.add(rest)
                    break
            else:
                keep.append(m)
        acc = F2Poly(frozenset(keep))
        for e, rest in by_exp.items():
            acc = acc + F2Poly(frozenset(rest)) * (val ** e)
        return acc

    def subs_many(self, mapping: Dict[str, "F2Poly"]) -> "F2Poly":
        r = self
        for name, val in mapping.items():
            if name in r.variables():
                r = r.subs(name, val)
        return r

    def reduce_square(self, name: str, rest: "F2Poly") -> "F2Poly":
        """Rewrite using name^2 = rest (name known through a Frobenius pivot)."""
        return self.reduce_power(name, 2, rest)

    def reduce_power(self, name: str, order: int, rest: "F2Poly") -> "F2Poly":
        """Rewrite using name^order = rest, order a power of two (name known
        through an order-2^s Frobenius pivot, cf. static_patterns sec 76)."""
        if self.degree(name) < order:
            return self
        vi = _INDEX[name]
        acc = ZERO
        for m in self.t:
            e = 0
            base = m
            for idx, (v, ee) in enumerate(m):
                if v == vi:
                    e = ee
                    base = m[:idx] + m[idx + 1:]
                    break
            term = F2Poly(frozenset({base})) * (rest ** (e // order))
            if e % order:
                term = term * F2Poly(frozenset({((vi, e % order),)}))
            acc = acc + term
        return acc

    def diff(self, name: str) -> "F2Poly":
        vi = _INDEX.get(name)
        if vi is None:
            return ZERO
        out: set = set()
        for m in self.t:
            for idx, (v, e) in enumerate(m):
                if v == vi:
                    if e % 2 == 1:  # e * name^(e-1), e odd -> 1
                        nm = m[:idx] + (((v, e - 1),) if e > 1 else ()) + m[idx + 1:]
                        if nm in out:
                            out.discard(nm)
                        else:
                            out.add(nm)
                    break
        return F2Poly(frozenset(out))

    def evaluate(self, env: Dict[str, int], F: GF2k = GF2) -> int:
        acc = 0
        for m in self.t:
            term = 1
            for v, e in m:
                term = F.mul(term, F.pow(env[_NAMES[v]], e))
                if term == 0:
                    break
            acc ^= term
        return acc

    # -- printing -------------------------------------------------------
    @staticmethod
    def _mono_str(m: Mono) -> str:
        if not m:
            return "1"
        return "*".join(f"{_NAMES[v]}^{e}" if e > 1 else _NAMES[v] for v, e in m)

    def __str__(self) -> str:
        if not self.t:
            return "0"
        ms = sorted(self.t, key=lambda m: (-sum(e for _, e in m), [(_NAMES[v], e) for v, e in m]))
        return " + ".join(self._mono_str(m) for m in ms)

    __repr__ = __str__


ZERO = F2Poly(frozenset())
ONE = F2Poly(frozenset({()}))
_ONE_T = ONE.t


# ----------------------------------------------------------------------------
# Polynomials in x with F2Poly coefficients (wires)
# ----------------------------------------------------------------------------
class XPoly:
    """Polynomial in the circuit variable x, ascending coefficient list."""

    __slots__ = ("c",)

    def __init__(self, coeffs: Sequence[Union[F2Poly, int]]):
        cs = [F2Poly._coerce(v) if not isinstance(v, F2Poly) else v for v in coeffs]
        while cs and cs[-1].is_zero():
            cs.pop()
        self.c: List[F2Poly] = cs

    @staticmethod
    def coerce(o) -> "XPoly":
        if isinstance(o, XPoly):
            return o
        if isinstance(o, F2Poly):
            return XPoly([o])
        if isinstance(o, int) and not isinstance(o, bool):
            return XPoly([F2Poly.const(o)])
        return NotImplemented

    @property
    def degree(self) -> int:
        return len(self.c) - 1

    def coeff(self, i: int) -> F2Poly:
        return self.c[i] if 0 <= i < len(self.c) else ZERO

    def __getitem__(self, i: int) -> F2Poly:
        return self.coeff(i)

    def __add__(self, o):
        o = XPoly.coerce(o)
        if o is NotImplemented:
            return NotImplemented
        n = max(len(self.c), len(o.c))
        return XPoly([self.coeff(i) + o.coeff(i) for i in range(n)])

    __radd__ = __add__
    __sub__ = __add__
    __rsub__ = __add__

    def __neg__(self):
        return self

    def __mul__(self, o):
        o = XPoly.coerce(o)
        if o is NotImplemented:
            return NotImplemented
        if not self.c or not o.c:
            return XPoly([])
        out = [ZERO] * (len(self.c) + len(o.c) - 1)
        for i, a in enumerate(self.c):
            if a.is_zero():
                continue
            for j, b in enumerate(o.c):
                if b.is_zero():
                    continue
                out[i + j] = out[i + j] + a * b
        return XPoly(out)

    __rmul__ = __mul__

    def __pow__(self, n: int) -> "XPoly":
        r = XPoly([ONE])
        for _ in range(n):
            r = r * self
        return r

    def shift(self, k: int) -> "XPoly":
        return XPoly([ZERO] * k + self.c)

    def subs_many(self, mapping: Dict[str, F2Poly]) -> "XPoly":
        return XPoly([v.subs_many(mapping) for v in self.c])

    def is_monic(self) -> bool:
        return bool(self.c) and self.c[-1] == ONE

    def __eq__(self, o):
        o = XPoly.coerce(o)
        if o is NotImplemented:
            return NotImplemented
        return self.c == o.c

    def __hash__(self):
        return hash(tuple(self.c))

    def __str__(self) -> str:
        if not self.c:
            return "0"
        parts = []
        for i in range(len(self.c) - 1, -1, -1):
            v = self.c[i]
            if v.is_zero():
                continue
            mon = "" if i == 0 else ("x" if i == 1 else f"x^{i}")
            if v == ONE and mon:
                parts.append(mon)
            elif mon:
                parts.append(f"({v})*{mon}")
            else:
                parts.append(f"({v})")
        return " + ".join(parts)

    __repr__ = __str__


X = XPoly([ZERO, ONE])


def divmod_monic(N: XPoly, D: XPoly) -> Tuple[XPoly, XPoly]:
    """Long division of N by the monic polynomial D (explicit, coefficientwise)."""
    assert D.is_monic(), "divisor must be monic"
    rem = list(N.c)
    dd = D.degree
    q = [ZERO] * max(0, len(rem) - dd)
    for i in range(len(rem) - 1, dd - 1, -1):
        lead = rem[i]
        if lead.is_zero():
            continue
        q[i - dd] = lead
        for j in range(dd + 1):
            rem[i - dd + j] = rem[i - dd + j] + lead * D.c[j]
    return XPoly(q), XPoly(rem[:dd])


# ----------------------------------------------------------------------------
# Result types
# ----------------------------------------------------------------------------
RowKey = Tuple[str, int]  # (output surface, coefficient index)


@dataclass
class Step:
    surface: str
    row: int
    unknown: str
    kind: str  # 'unit' | 'Frob'
    parametric: F2Poly  # value at pivot time (may still involve later unknowns)

    def text(self, width: int = 400) -> str:
        v = _trunc(self.parametric, width)
        rhs = (v if self.kind == "unit" else f"sqrt({v})" if self.kind == "Frob"
               else f"({v})^(1/{self.kind[4:]})")
        return f"row {self.row:>3} of {self.surface}: {self.unknown} = {rhs}   [{self.kind}]"

    def __str__(self) -> str:
        return self.text()


def _trunc(v: F2Poly, width: int) -> str:
    s = str(v)
    if width and len(s) > width:
        s = s[:width] + f" ... ({len(v.t)} monomials)"
    return s


@dataclass
class Result:
    status: str  # 'ok' | 'fail' | 'budget'
    order: List[Step]
    solution: Dict[str, Tuple[str, F2Poly]]  # unknown -> (kind, closed form in observations)
    unknowns: List[str]
    rows_used: List[RowKey]
    leftover: Dict[RowKey, F2Poly]  # consistency relations among observations
    fixed_rows: Dict[RowKey, F2Poly]  # ground rows (no observation symbol)
    remaining_unknowns: List[str]
    obstruction: List[str]
    gauge: List[str]
    verified: Optional[bool]
    frob_used: bool
    nodes: int
    info: Dict[str, object] = field(default_factory=dict)

    @property
    def ok(self) -> bool:
        return self.status == "ok"

    def order_tuples(self) -> List[Tuple[str, int, str, str]]:
        return [(s.surface, s.row, s.unknown, s.kind) for s in self.order]

    def report(self, width: int = 400) -> str:
        """Human-readable report; expressions longer than ``width`` chars are elided."""
        L: List[str] = []
        tag = "Frob" if self.frob_used else "unit"
        L.append(f"status: {self.status}   table kind: {tag}   search nodes: {self.nodes}")
        L.append(f"unknowns ({len(self.unknowns)}): {', '.join(self.unknowns)}")
        for k, v in self.info.items():
            L.append(f"{k}: {v}")
        if self.fixed_rows:
            L.append("fixed rows (ground, carry no information): " + ", ".join(
                f"{s}[{i}]={v}" for (s, i), v in self.fixed_rows.items()))
        L.append("pivot order:")
        for st in self.order:
            L.append("  " + st.text(width))
        if self.solution:
            L.append("decoder" + (" (partial, parametric)" if self.status != "ok" else "")
                     + f" [{self.info.get('solution forms', '')}]:")
            for u in self.unknowns:
                if u in self.solution:
                    kind, val = self.solution[u]
                    sv = _trunc(val, width)
                    L.append(f"  {u} = {sv}" if kind == "unit"
                             else f"  {u} = sqrt({sv})" if kind == "Frob"
                             else f"  {u} = ({sv})^(1/{kind[4:]})")
        if self.leftover:
            L.append("leftover rows (consistency relations, not used):")
            for (s, i), v in self.leftover.items():
                L.append(f"  {s}[{i}]: {_trunc(v, width)} = 0")
        if self.verified is not None:
            L.append(f"decoder verification (causal check; plus encoder(decoder(obs)) == obs when closed): "
                     f"{'PASS' if self.verified else 'FAIL'}")
        if self.status != "ok":
            L.append(f"remaining unknowns ({len(self.remaining_unknowns)}): {', '.join(self.remaining_unknowns)}")
            L.append("obstruction (remaining rows, residual shape in the unknowns; [..] = known part):")
            for line in self.obstruction:
                L.append("  " + line)
            L.append("DIAGNOSTIC ONLY (not a decodability argument): Jacobian-kernel / gauge report")
            for line in self.gauge:
                L.append("  " + line)
        return "\n".join(L)

    __str__ = report


class SpecError(ValueError):
    pass


# ----------------------------------------------------------------------------
# The finder
# ----------------------------------------------------------------------------
class InverseFinder:
    """Declare unknowns/state, build wires and outputs, then ``solve()``.

    * ``scalar(*names, known=False)`` -- fresh scalar unknowns (F2Poly symbols).
    * ``state_poly(name, degree, monic=True, fixed=None, known=False)`` -- a
      polynomial in x whose coefficients are unknown symbols ``name_i``;
      ``fixed`` maps coefficient index -> 0/1/F2Poly/expression string, which is
      substituted in place of the symbol (so ``[x^{D-1}]C = 0`` etc.).
    * ``constrain(symbol, value)`` -- substitute an unknown by an expression in
      other unknowns before solving (e.g. ``T_2 = H_2 + 1``).
    * ``wire(name, xpoly)`` / ``gate(L, R, name=None)`` -- name intermediate
      polynomials (``gate`` also counts the product).
    * ``output(name, xpoly, visible=None)`` -- an output surface; rows are its
      coefficients (default: all indices 0..deg).
    """

    def __init__(self, x_name: str = "x"):
        self.x = X
        self.x_name = x_name
        self._unknowns: List[str] = []
        self._known: List[str] = []
        self._subs: Dict[str, F2Poly] = {}
        self._state: Dict[str, dict] = {}
        self._outputs: List[Tuple[str, XPoly, Optional[List[int]]]] = []
        self._wires: Dict[str, XPoly] = {}
        self._products: List[Tuple[str, int]] = []
        self.namespace: Dict[str, object] = {x_name: X}

    # -- declarations ---------------------------------------------------
    def _new_symbol(self, name: str, known: bool) -> F2Poly:
        if name in self.namespace:
            raise SpecError(f"name {name!r} already declared")
        sym = F2Poly.var(name)
        (self._known if known else self._unknowns).append(name)
        self.namespace[name] = sym
        return sym

    def scalar(self, *names: str, known: bool = False):
        syms = tuple(self._new_symbol(n, known) for n in names)
        return syms[0] if len(syms) == 1 else syms

    def coeff_name(self, poly: str, i: int) -> str:
        return f"{poly}_{i}"

    def state_poly(self, name: str, degree: int, monic: bool = True, fixed=None,
                   known: bool = False, coeff_names: Optional[Dict[int, str]] = None) -> XPoly:
        if name in self.namespace:
            raise SpecError(f"name {name!r} already declared")
        fixed = {int(k): v for k, v in (fixed or {}).items()}
        coeffs: List[F2Poly] = []
        syms: Dict[int, str] = {}
        for i in range(degree + 1):
            if i == degree and monic:
                coeffs.append(ONE)
            elif i in fixed:
                coeffs.append(self._as_scalar(fixed[i]))
            else:
                cname = (coeff_names or {}).get(i, self.coeff_name(name, i))
                coeffs.append(self._new_symbol(cname, known))
                syms[i] = cname
        p = XPoly(coeffs)
        self._state[name] = {"degree": degree, "monic": monic, "fixed": fixed, "symbols": syms}
        self.namespace[name] = p
        return p

    def coeff_symbol(self, poly: str, i: int) -> F2Poly:
        return self.namespace[self._state[poly]["symbols"][i]]  # type: ignore

    def constrain(self, sym: Union[str, F2Poly], value) -> None:
        name = self._sym_name(sym)
        if name not in self._unknowns and name not in self._known:
            raise SpecError(f"{name!r} is not a declared symbol")
        val = self._as_scalar(value)
        if name in val.variables():
            raise SpecError(f"constraint for {name!r} refers to itself")
        self._subs[name] = val

    def wire(self, name: str, p) -> XPoly:
        p = XPoly.coerce(p)
        if name in self.namespace:
            raise SpecError(f"name {name!r} already declared")
        self._wires[name] = p
        self.namespace[name] = p
        return p

    def gate(self, L, R, name: Optional[str] = None) -> XPoly:
        g = XPoly.coerce(L) * XPoly.coerce(R)
        self._products.append((name or f"g{len(self._products)}", g.degree))
        if name:
            self.wire(name, g)
        return g

    def output(self, name: str, p, visible: Optional[Iterable[int]] = None) -> XPoly:
        p = XPoly.coerce(p)
        if name in self.namespace:
            raise SpecError(f"name {name!r} already declared")
        self.namespace[name] = p
        self._outputs.append((name, p, None if visible is None else sorted(set(int(i) for i in visible))))
        return p

    # -- helpers --------------------------------------------------------
    def _sym_name(self, sym) -> str:
        if isinstance(sym, str):
            return sym
        if isinstance(sym, F2Poly) and len(sym.t) == 1:
            (m,) = sym.t
            if len(m) == 1 and m[0][1] == 1:
                return _NAMES[m[0][0]]
        raise SpecError(f"{sym} is not a symbol")

    def parse(self, expr):
        if isinstance(expr, (int, F2Poly, XPoly)):
            return expr
        code = str(expr).replace("^", "**")
        try:
            return eval(code, {"__builtins__": {}}, dict(self.namespace))
        except NameError as e:
            raise SpecError(f"unknown name in {expr!r}: {e}") from None

    def _as_scalar(self, v) -> F2Poly:
        v = self.parse(v)
        if isinstance(v, XPoly):
            if v.degree > 0:
                raise SpecError("expected a scalar (x-free) expression")
            return v.coeff(0)
        return F2Poly._coerce(v)

    @property
    def unknowns(self) -> List[str]:
        return [u for u in self._unknowns if u not in self._subs]

    @property
    def products(self) -> List[Tuple[str, int]]:
        return list(self._products)

    # -- spec -----------------------------------------------------------
    @classmethod
    def from_spec(cls, spec: dict) -> "InverseFinder":
        fd = cls(spec.get("x", "x"))
        for s in spec.get("state", []):
            fd.state_poly(s["name"], int(s["degree"]), bool(s.get("monic", True)),
                          s.get("fixed"), bool(s.get("known", False)))
        for s in spec.get("scalars", []):
            if isinstance(s, dict):
                fd.scalar(s["name"], known=bool(s.get("known", False)))
            else:
                fd.scalar(s)
        for k, v in (spec.get("constraints") or {}).items():
            fd.constrain(k, v)
        wires = spec.get("wires", [])
        items = wires.items() if isinstance(wires, dict) else (
            (w["name"], w["expr"]) if isinstance(w, dict) else tuple(w) for w in wires)
        for name, expr in items:
            fd.wire(name, fd.parse(expr))
        outs = spec.get("outputs", [])
        if isinstance(outs, dict):
            outs = [{"name": k, "expr": v} for k, v in outs.items()]
        for o in outs:
            if not isinstance(o, dict):
                o = {"name": o[0], "expr": o[1]}
            fd.output(o["name"], fd.parse(o["expr"]), o.get("visible"))
        return fd

    # -- solving --------------------------------------------------------
    def _apply_constraints(self) -> Tuple[List[Tuple[str, XPoly, Optional[List[int]]]], List[str]]:
        subs = dict(self._subs)
        for _ in range(len(subs) + 1):  # close chained constraints
            new = {k: v.subs_many(subs) for k, v in subs.items()}
            if new == subs:
                break
            subs = new
        outs = [(n, p.subs_many(subs), vis) for n, p, vis in self._outputs]
        return outs, [u for u in self._unknowns if u not in subs]

    def build_rows(self):
        """Return (rows, fixed_rows, unknowns, meta). rows: RowKey -> residual
        ``coeff + name[i]`` where ``name[i]`` is the observed-coefficient symbol."""
        outs, unknowns = self._apply_constraints()
        rows: Dict[RowKey, F2Poly] = {}
        fixed: Dict[RowKey, F2Poly] = {}
        meta: Dict[str, object] = {}
        for name, p, vis in outs:
            idxs = vis if vis is not None else list(range(p.degree + 1))
            meta[f"output {name}"] = f"degree {p.degree}, leading coefficient {p.coeff(p.degree)}"
            for i in sorted(idxs, reverse=True):
                cval = p.coeff(i)
                if cval.is_ground():
                    fixed[(name, i)] = cval
                else:
                    rows[(name, i)] = cval + F2Poly.var(f"{name}[{i}]")
        if self._products:
            meta["products"] = ", ".join(f"{n}:deg{d}" for n, d in self._products)
        return rows, fixed, unknowns, meta

    def solve(self, frobenius: bool = False, prefer: str = "fewest", max_nodes: int = 4000,
              gauge_diag: bool = True, seed: int = 1, verbose: bool = False,
              substitute: str = "parametric", closed_form_budget: int = 5000) -> Result:
        """Run the causal unit-pivot table search.

        frobenius   -- accept k^2 + (k-free) rows as Frobenius pivots ('Frob' table).
        prefer      -- 'fewest' (fewest unknowns in the row, then highest row),
                       'causal' (ground pivots first, unit or Frobenius, then highest row) or
                       'high' (highest row first).
        substitute  -- 'parametric' (default; decoded unknowns stay symbols unless
                       their value still contains unknowns) or 'all' (substitute every
                       decoded value everywhere; slower, catches accidental cancellations).
        closed_form_budget -- max monomials per closed-form decoder expression; above
                       it ``solution`` keeps the causal (table) forms.
        """
        rows, fixed, unknowns, meta = self.build_rows()
        solver = _TableSearch(rows, unknowns, frobenius, prefer, max_nodes, verbose, substitute)
        final = solver.run()
        st = final if final is not None else solver.deepest
        status = "ok" if final is not None else ("budget" if solver.budget_hit else "fail")
        used = [(s.surface, s.row) for s in st.order]
        obs = {f"{k[0]}[{k[1]}]" for k in rows} | set(self._known)  # known side symbols are allowed
        causal = _causal(st.known, st.frob, st.order)
        frob_used = bool(st.frob)
        closed = _close(causal, st.order, closed_form_budget) if status == "ok" else None
        solution = closed if closed is not None else causal
        meta["solution forms"] = ("closed (observations only)" if closed is not None else
                                  "causal table (observations + earlier-decoded symbols)")
        # leftover rows: consistency relations; express them through the decoded values
        lin = {u: v for u, (kind, v) in solution.items() if kind == "unit"}
        leftover = {}
        for k, v in st.rows.items():
            if v.variables() & set(st.unknown):
                continue
            for _ in range(len(lin) + 1):
                nv = v.subs_many({u: lin[u] for u in v.variables() & set(lin)})
                for f, (m, rest) in st.frob.items():
                    nv = nv.reduce_power(f, m, rest)
                if nv == v:
                    break
                v = nv
            leftover[k] = v
        verified = None
        if status == "ok":
            verified = _causal_check(st.order, causal, obs)
            meta["causal (unitriangular) check"] = "PASS" if verified else "FAIL"
            if closed is not None and verified:
                verified = _verify(rows, used, closed)
        obstruction: List[str] = []
        gauge: List[str] = []
        remaining = list(st.unknown)
        if status != "ok":
            touched: set = set()
            for e in st.rows.values():
                touched |= e.variables()
            absent = [u for u in st.unknown if u not in touched]
            if absent:
                obstruction.append("unknowns absent from every remaining row: " + ", ".join(absent))
            for key, e in sorted(st.rows.items(), key=lambda kv: (kv[0][0], -kv[0][1])):
                uv = e.variables() & set(st.unknown)
                if not uv:
                    continue
                obstruction.append(f"row {key[1]} of {key[0]}: {_shape(e, st.unknown)}   "
                                   f"({_classify(e, sorted(uv, key=st.unknown.index))})")
            if gauge_diag:
                gauge = gauge_report(rows, unknowns, seed=seed)
                if len(st.known) or len(st.frob):
                    gauge.append("(restricted to the remaining unknowns and rows after the partial table:)")
                    gauge += gauge_report({k: v for k, v in st.rows.items()}, remaining, seed=seed + 1)
        meta["rows"] = f"{len(rows)} informative visible rows, {len(unknowns)} unknowns"
        return Result(status, list(st.order), solution, unknowns, used, leftover, fixed, remaining,
                      obstruction, gauge, verified, frob_used, solver.nodes, meta)


# ----------------------------------------------------------------------------
# Search
# ----------------------------------------------------------------------------
@dataclass
class _State:
    rows: Dict[RowKey, F2Poly]
    unknown: List[str]
    known: Dict[str, F2Poly]
    frob: Dict[str, F2Poly]
    order: List[Step]


class _TableSearch:
    def __init__(self, rows, unknowns, frobenius, prefer, max_nodes, verbose, substitute="parametric"):
        self.frobenius = frobenius
        self.substitute = substitute
        self.prefer = prefer
        self.max_nodes = max_nodes
        self.verbose = verbose
        self.nodes = 0
        self.budget_hit = False
        self.surfaces = list(dict.fromkeys(k[0] for k in rows))
        self.uindex = {u: i for i, u in enumerate(unknowns)}
        self.start = _State(dict(rows), list(unknowns), {}, {}, [])
        self.deepest = self.start

    def run(self) -> Optional[_State]:
        return self._dfs(self.start)

    def _candidates(self, st: _State):
        cands = []
        uset = set(st.unknown)
        for key, e in st.rows.items():
            uv = e.variables() & uset
            if not uv:
                continue
            for u in uv:
                d = e.degree(u)
                if d == 1 and e.coeff_wrt(u, 1) == ONE:
                    cands.append((key, u, "unit", len(uv)))
                elif (self.frobenius and d in (2, 4, 8) and e.coeff_wrt(u, d) == ONE
                      and all(e.coeff_wrt(u, j).is_zero() for j in range(1, d))):
                    # order-2^s Frobenius pivot: u^(2^s) + (u-free), sec 76
                    cands.append((key, u, "Frob" if d == 2 else f"Frob{d}", len(uv)))
        sidx = {s: i for i, s in enumerate(self.surfaces)}
        if self.prefer == "high":
            keyf = lambda c: (c[2] != "unit", -c[0][1], sidx[c[0][0]], c[3], self.uindex[c[1]])
        elif self.prefer == "causal":
            # ground pivots first (value free of remaining unknowns, unit or Frobenius alike),
            # then highest row: this follows hand decoders that open with a square root
            # (e.g. row 13 = A^2 + known) before the unit rows that depend on it
            keyf = lambda c: (c[3] != 1, c[2] != "unit", -c[0][1], sidx[c[0][0]], self.uindex[c[1]])
        else:
            keyf = lambda c: (c[2] != "unit", c[3], -c[0][1], sidx[c[0][0]], self.uindex[c[1]])
        cands.sort(key=keyf)
        return cands

    def _apply(self, st: _State, cand) -> _State:
        key, u, kind, _ = cand
        e = st.rows[key]
        known, frob = dict(st.known), dict(st.frob)
        unknown = [v for v in st.unknown if v != u]
        if kind == "unit":
            val = e + F2Poly.var(u)  # e = u + val  (char 2)
            known[u] = val
            # Certificate semantics: a decoded unknown whose value is causal
            # (observations + earlier-decoded symbols only) stays a *symbol*;
            # only parametric values (still containing unknowns) are substituted.
            substitute = self.substitute == "all" or bool(val.variables() & set(unknown))
        else:
            order = 2 if kind == "Frob" else int(kind[4:])
            val = e.coeff_wrt(u, 0)  # e = u^order + val
            frob[u] = (order, val)
            substitute = False
        rows = {}
        for k, r in st.rows.items():
            if k == key:
                continue
            if substitute and u in r.variables():
                r = r.subs(u, val)
            for f, (m, rest) in frob.items():
                r = r.reduce_power(f, m, rest)
            rows[k] = r
        step = Step(key[0], key[1], u, kind, val)
        return _State(rows, unknown, known, frob, st.order + [step])

    def _dfs(self, st: _State) -> Optional[_State]:
        if not st.unknown:
            return st
        if len(st.known) + len(st.frob) > len(self.deepest.known) + len(self.deepest.frob):
            self.deepest = st
        self.nodes += 1
        if self.nodes > self.max_nodes:
            self.budget_hit = True
            return None
        cands = self._candidates(st)
        if not cands:
            return None
        for c in cands:
            if self.verbose:
                print(f"  try row {c[0][1]} of {c[0][0]} -> {c[1]} [{c[2]}]", file=sys.stderr)
            nxt = self._apply(st, c)
            res = self._dfs(nxt)
            if res is not None:
                return res
            if self.budget_hit:
                return None
        return None


def _causal(known: Dict[str, F2Poly], frob: Dict[str, Tuple[int, F2Poly]], order: List[Step]):
    """Causal table forms: each unknown through observations and earlier-decoded
    symbols (parametric values are closed by substituting later-decoded ones)."""
    sol: Dict[str, F2Poly] = dict(known)
    fsol: Dict[str, Tuple[int, F2Poly]] = dict(frob)
    decoded = {st.unknown for st in order}
    for _ in range(len(order) + 2):
        changed = False
        for u in list(sol):
            v = sol[u]
            later = {k: sol[k] for k in v.variables() & decoded if k in sol and k not in _earlier(order, u)}
            later = {k: val for k, val in later.items() if k != u}
            if later:
                nv = v.subs_many(later)
                for f, (m, rest) in fsol.items():
                    nv = nv.reduce_power(f, m, rest)
                if nv != v:
                    sol[u] = nv
                    changed = True
        if not changed:
            break
    out: Dict[str, Tuple[str, F2Poly]] = {}
    for st in order:
        out[st.unknown] = (("unit", sol[st.unknown]) if st.kind == "unit"
                           else (st.kind, fsol[st.unknown][1]))
    return out


def _earlier(order: List[Step], u: str) -> set:
    out = set()
    for st in order:
        if st.unknown == u:
            break
        out.add(st.unknown)
    return out


def _close(causal: Dict[str, Tuple[str, F2Poly]], order: List[Step], budget: int):
    """Back-substitute the causal forms into closed forms in the observations only.
    Returns None if any expression would exceed ``budget`` monomials."""
    sol: Dict[str, F2Poly] = {}
    fsol: Dict[str, Tuple[int, F2Poly]] = {}
    for st in order:
        kind, nv = causal[st.unknown]
        for k in sorted(nv.variables() & set(sol)):  # sol values are already closed
            if len(nv.t) * len(sol[k].t) ** nv.degree(k) > 8 * budget:
                return None
            nv = nv.subs(k, sol[k])
            if len(nv.t) > budget:
                return None
        for f, (m, rest) in fsol.items():
            nv = nv.reduce_power(f, m, rest)
        if len(nv.t) > budget:
            return None
        if kind == "unit":
            sol[st.unknown] = nv
        else:
            fsol[st.unknown] = (2 if kind == "Frob" else int(kind[4:]), nv)
    return {st.unknown: (("unit", sol[st.unknown]) if st.kind == "unit"
                         else (st.kind, fsol[st.unknown][1]))
            for st in order}


def _causal_check(order: List[Step], causal, obs: set) -> bool:
    """Unitriangular check: each decoded unknown depends only on observations
    and earlier-decoded symbols (this is the certificate's own criterion)."""
    seen: set = set()
    for st in order:
        _, v = causal[st.unknown]
        if not (v.variables() <= obs | seen):
            return False
        seen.add(st.unknown)
    return True


def _verify(rows: Dict[RowKey, F2Poly], used: List[RowKey], solution) -> Optional[bool]:
    """Check encoder(decoder(obs)) == obs on the used rows as a polynomial identity."""
    lin = {u: v for u, (k, v) in solution.items() if k == "unit"}
    frob = {u: (2 if k == "Frob" else int(k[4:]), v)
            for u, (k, v) in solution.items() if k != "unit"}
    ok = True
    for key in used:
        r = rows[key].subs_many(lin)
        for f, (m, rest) in frob.items():
            r = r.reduce_power(f, m, rest)
        if not r.is_zero():
            if frob and (r.variables() & set(frob)):
                return None  # cannot decide symbolically through a square root
            ok = False
    return ok


def _shape(e: F2Poly, unknowns: List[str]) -> str:
    """Residual grouped by its monomials in the unknowns; known parts in [..]."""
    uids = {_INDEX[u] for u in unknowns if u in _INDEX}
    groups: Dict[Mono, set] = {}
    for m in e.t:
        um = tuple((v, x) for v, x in m if v in uids)
        km = tuple((v, x) for v, x in m if v not in uids)
        s = groups.setdefault(um, set())
        if km in s:
            s.discard(km)
        else:
            s.add(km)
    parts = []
    for um in sorted(groups, key=lambda m: (-sum(x for _, x in m), [(_NAMES[v], x) for v, x in m])):
        kp = F2Poly(frozenset(groups[um]))
        if kp.is_zero():
            continue
        us = F2Poly._mono_str(um)
        if kp == ONE:
            parts.append(us)
        elif not um:
            parts.append(f"[{kp}]")
        else:
            parts.append(f"[{kp}]*{us}")
    return " + ".join(parts) if parts else "0"


def _classify(e: F2Poly, uv: List[str]) -> str:
    out = []
    for u in uv:
        d = e.degree(u)
        if d == 1:
            piv = e.coeff_wrt(u, 1)
            out.append(f"{u}: linear, pivot {piv}" + ("" if piv == ONE else " (not a unit)"))
        elif d == 2 and e.coeff_wrt(u, 1).is_zero() and e.coeff_wrt(u, 2) == ONE:
            out.append(f"{u}: pure square {u}^2 (Frobenius pivot; enable frobenius=True)")
        else:
            out.append(f"{u}: degree {d}")
    return "; ".join(out)


# ----------------------------------------------------------------------------
# Diagnostic: Jacobian kernel at random points (gauge / translation directions)
# ----------------------------------------------------------------------------
def nullspace(M: List[List[int]], ncols: int, F: GF2k) -> List[List[int]]:
    M = [row[:] for row in M]
    pivots: List[int] = []
    r = 0
    for c in range(ncols):
        if r >= len(M):
            break
        p = next((i for i in range(r, len(M)) if M[i][c]), None)
        if p is None:
            continue
        M[r], M[p] = M[p], M[r]
        inv = F.inv(M[r][c])
        M[r] = [F.mul(inv, v) for v in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]
                M[i] = [a ^ F.mul(f, b) for a, b in zip(M[i], M[r])]
        pivots.append(c)
        r += 1
    basis = []
    for fcol in [c for c in range(ncols) if c not in pivots]:
        v = [0] * ncols
        v[fcol] = 1
        for i, pc in enumerate(pivots):
            v[pc] = M[i][fcol]  # char 2: x_pc = M[i][fcol] * x_fcol
        basis.append(v)
    return basis


def gauge_report(rows: Dict[RowKey, F2Poly], unknowns: List[str], seed: int = 1, trials: int = 2) -> List[str]:
    """Kernel of the Jacobian d(rows)/d(unknowns) at random points over F_2 and GF(2^8).
    Diagnostic only: names unknowns that shift together (translation gauges)."""
    lines = [f"Jacobian: {len(rows)} rows x {len(unknowns)} unknowns"]
    if not unknowns or not rows:
        return lines
    keys = list(rows)
    jac = [[rows[k].diff(u) for u in unknowns] for k in keys]
    allvars = set()
    for k in keys:
        allvars |= rows[k].variables()
    rng = random.Random(seed)
    for F, fname in ((GF2, "F_2"), (GF256, "GF(2^8)")):
        for t in range(trials):
            env = {v: rng.randrange(F.mask + 1) for v in allvars}
            M = [[d.evaluate(env, F) for d in row] for row in jac]
            ker = nullspace(M, len(unknowns), F)
            rank = len(unknowns) - len(ker)
            desc = []
            for v in ker:
                names = [f"{u}" + ("" if val == 1 else f":{val:#x}") for u, val in zip(unknowns, v) if val]
                desc.append("{" + ", ".join(names) + "}")
            lines.append(f"{fname} random point #{t + 1}: rank {rank}, kernel dim {len(ker)}"
                         + (":  shift together " + "; ".join(desc) if ker else ""))
    return lines


# ----------------------------------------------------------------------------
# CLI
# ----------------------------------------------------------------------------
def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("spec", help="JSON spec file")
    ap.add_argument("--frobenius", action="store_true", help="accept k^2 + (k-free) rows as Frobenius pivots")
    ap.add_argument("--prefer", choices=["fewest", "high", "causal"], default="fewest")
    ap.add_argument("--max-nodes", type=int, default=4000)
    ap.add_argument("--no-gauge", action="store_true")
    ap.add_argument("--verbose", action="store_true")
    ap.add_argument("--substitute", choices=["parametric", "all"], default="parametric")
    ap.add_argument("--width", type=int, default=400, help="elide printed expressions beyond this length")
    ap.add_argument("--json", default=None, help="also dump the result as JSON to this path")
    args = ap.parse_args(argv)
    with open(args.spec) as fh:
        spec = json.load(fh)
    opts = spec.get("options", {})
    fd = InverseFinder.from_spec(spec)
    res = fd.solve(frobenius=args.frobenius or bool(opts.get("frobenius", False)),
                   prefer=opts.get("prefer", args.prefer), max_nodes=args.max_nodes,
                   gauge_diag=not args.no_gauge, verbose=args.verbose, substitute=args.substitute)
    print(res.report(args.width))
    if args.json:
        with open(args.json, "w") as fh:
            json.dump({"status": res.status, "order": res.order_tuples(),
                       "solution": {u: [k, str(v)] for u, (k, v) in res.solution.items()},
                       "leftover": {f"{s}[{i}]": str(v) for (s, i), v in res.leftover.items()},
                       "verified": res.verified, "remaining": res.remaining_unknowns,
                       "obstruction": res.obstruction, "gauge": res.gauge}, fh, indent=1)
    return 0 if res.ok else 1


if __name__ == "__main__":
    sys.exit(main())
