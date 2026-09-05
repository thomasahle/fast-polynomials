"""Sparse GF(2)[q][x] algebra for explicit Lean certificate generation.

Extracted from the local inverse-finder's algebra layer; no search, finite-field
sampling, Jacobian machinery, or private research-directory imports are needed.
Exponents remain unrestricted: q**2 is not reduced to q.
"""
from __future__ import annotations
from typing import Dict, Iterable, List, Sequence, Tuple, Union

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
