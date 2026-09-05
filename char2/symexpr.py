from __future__ import annotations

"""
Tiny symbolic algebra for expressions in the polynomial ring F2[a0,a1,...].

This is used to reason about *structural* coefficient identities in characteristic 2
without relying on finite-field testing:

  - addition is XOR (symmetric difference of monomials)
  - multiplication is distributive, with monomials multiplying by concatenation

We intentionally do NOT apply any field-specific identities like (a^2 = a) or Frobenius;
we keep squares as monomials (a,a). When interpreting over a perfect char-2 field, those
monomials correspond to Frobenius powers.
"""

from dataclasses import dataclass
from functools import cached_property
from typing import FrozenSet, Iterable, Iterator, Mapping, Protocol, Tuple


Monomial = Tuple[str, ...]  # sorted tuple of variable names, e.g. ("a3","a7","a7")


def _mul_mono(m1: Monomial, m2: Monomial) -> Monomial:
    if not m1:
        return m2
    if not m2:
        return m1
    return tuple(sorted(m1 + m2))


@dataclass(frozen=True)
class Expr:
    """
    Expression as XOR of monomials in F2[vars].

    The empty monomial () represents constant 1.
    The empty set represents 0.
    """

    monos: FrozenSet[Monomial]

    @staticmethod
    def zero() -> "Expr":
        return Expr(frozenset())

    @staticmethod
    def one() -> "Expr":
        return Expr(frozenset({()}))

    @staticmethod
    def var(name: str) -> "Expr":
        return Expr(frozenset({(name,)}))

    def __xor__(self, other: "Expr") -> "Expr":
        # XOR = symmetric difference of monomial sets
        return Expr(self.monos ^ other.monos)

    __add__ = __xor__

    def __mul__(self, other: "Expr") -> "Expr":
        if not self.monos or not other.monos:
            return Expr.zero()
        out: set[Monomial] = set()
        # multiply and XOR-accumulate
        for m1 in self.monos:
            for m2 in other.monos:
                mm = _mul_mono(m1, m2)
                if mm in out:
                    out.remove(mm)
                else:
                    out.add(mm)
        return Expr(frozenset(out))

    def is_zero(self) -> bool:
        return not self.monos

    def is_one(self) -> bool:
        return self.monos == frozenset({()})

    @cached_property
    def vars(self) -> FrozenSet[str]:
        vs = set()
        for m in self.monos:
            for v in m:
                vs.add(v)
        return frozenset(vs)

    def iter_monos(self) -> Iterator[Monomial]:
        return iter(self.monos)

    def __str__(self) -> str:
        if not self.monos:
            return "0"
        parts = []
        for m in sorted(self.monos):
            if m == ():
                parts.append("1")
            else:
                parts.append("*".join(m))
        return " + ".join(parts)

    class _XorMulField(Protocol):
        def mul(self, a: int, b: int) -> int: ...

    def eval_xor_field(self, env: Mapping[str, int], *, F: _XorMulField) -> int:
        """
        Evaluate the expression in a characteristic-2 field representation.

        This assumes the field's additive operation is XOR on the underlying
        integer representation (as in `gf4.py` / `gf2k.py`), and uses `F.mul`
        for multiplication.
        """

        acc = 0
        for m in self.monos:
            term = 1
            for v in m:
                try:
                    vv = env[v]
                except KeyError as e:
                    raise KeyError(f"missing variable {v!r} in env") from e
                term = F.mul(term, int(vv))
            acc ^= term
        return acc


Poly = list[Expr]  # coefficient list: coeff[i] for x^i


def poly_xor(a: Poly, b: Poly) -> Poly:
    n = max(len(a), len(b))
    out = [Expr.zero() for _ in range(n)]
    for i in range(n):
        ea = a[i] if i < len(a) else Expr.zero()
        eb = b[i] if i < len(b) else Expr.zero()
        out[i] = ea ^ eb
    # trim trailing zeros
    while out and out[-1].is_zero():
        out.pop()
    return out


def poly_mul(a: Poly, b: Poly, *, max_deg: int) -> Poly:
    out = [Expr.zero() for _ in range(max_deg + 1)]
    for i, ai in enumerate(a):
        if ai.is_zero():
            continue
        for j, bj in enumerate(b):
            if bj.is_zero():
                continue
            k = i + j
            if k > max_deg:
                break
            out[k] = out[k] ^ (ai * bj)
    while out and out[-1].is_zero():
        out.pop()
    return out


def poly_coeff(p: Poly, i: int) -> Expr:
    if 0 <= i < len(p):
        return p[i]
    return Expr.zero()


def poly_monic_degree(p: Poly) -> int:
    if not p:
        return -1
    return len(p) - 1


def poly_from_terms(terms: Iterable[tuple[int, Expr]]) -> Poly:
    terms = list(terms)
    if not terms:
        return []
    deg = max(i for i, _ in terms)
    out = [Expr.zero() for _ in range(deg + 1)]
    for i, e in terms:
        out[i] = out[i] ^ e
    while out and out[-1].is_zero():
        out.pop()
    return out


def expr_substitute(e: Expr, substitutions: Mapping[str, Expr]) -> Expr:
    """Substitute polynomial expressions for variables in ``e`` over ``F2``."""

    out = Expr.zero()
    for monomial in e.monos:
        term = Expr.one()
        for variable in monomial:
            term = term * substitutions.get(variable, Expr.var(variable))
        out = out ^ term
    return out


def poly_substitute(p: Poly, substitutions: Mapping[str, Expr]) -> Poly:
    """Apply ``expr_substitute`` coefficientwise, trimming trailing zeroes."""

    out = [expr_substitute(e, substitutions) for e in p]
    while out and out[-1].is_zero():
        out.pop()
    return out
