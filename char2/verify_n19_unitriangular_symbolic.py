#!/usr/bin/env python3
"""Exact audit of the square-first characteristic-two (19, 10) circuit.

The proof calculation is in GF(2)[q0,...,q18][x].  It verifies the literal
unitriangular identities

    [x^(18-i)] P = q_i + K_i(q_0,...,q_(i-1)).

The final exhaustive GF(2) enumeration is only an independent diagnostic; the
unitriangular identities are the proof and remain valid after base change to
every characteristic-two field.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet, List, Tuple


NVAR = 19
Monomial = Tuple[int, ...]


@dataclass(frozen=True)
class MPoly:
    """Sparse multivariate polynomial over GF(2)."""

    terms: FrozenSet[Monomial]

    @staticmethod
    def zero() -> "MPoly":
        return MPoly(frozenset())

    @staticmethod
    def one() -> "MPoly":
        return MPoly(frozenset({(0,) * NVAR}))

    @staticmethod
    def variable(index: int) -> "MPoly":
        exponents = [0] * NVAR
        exponents[index] = 1
        return MPoly(frozenset({tuple(exponents)}))

    def __add__(self, other: "MPoly | int") -> "MPoly":
        if isinstance(other, int):
            other = ONE if other & 1 else ZERO
        return MPoly(self.terms.symmetric_difference(other.terms))

    __xor__ = __add__

    def __radd__(self, other: "MPoly | int") -> "MPoly":
        return self + other

    def __mul__(self, other: "MPoly | int") -> "MPoly":
        if isinstance(other, int):
            return self if other & 1 else ZERO
        parity: set[Monomial] = set()
        for left in self.terms:
            for right in other.terms:
                monomial = tuple(a + b for a, b in zip(left, right))
                if monomial in parity:
                    parity.remove(monomial)
                else:
                    parity.add(monomial)
        return MPoly(frozenset(parity))

    def __rmul__(self, other: "MPoly | int") -> "MPoly":
        return self * other

    def variables_used(self) -> set[int]:
        return {
            index
            for monomial in self.terms
            for index, exponent in enumerate(monomial)
            if exponent
        }


ZERO = MPoly.zero()
ONE = MPoly.one()
Q = [MPoly.variable(i) for i in range(NVAR)]
UPoly = List[MPoly]
X: UPoly = [ZERO, ONE]


def add(left: UPoly, right: UPoly) -> UPoly:
    size = max(len(left), len(right))
    result = [ZERO] * size
    for i in range(size):
        result[i] = (left[i] if i < len(left) else ZERO) + (
            right[i] if i < len(right) else ZERO
        )
    while len(result) > 1 and not result[-1].terms:
        result.pop()
    return result


def multiply(left: UPoly, right: UPoly) -> UPoly:
    result = [ZERO] * (len(left) + len(right) - 1)
    for i, left_coefficient in enumerate(left):
        for j, right_coefficient in enumerate(right):
            result[i + j] = result[i + j] + left_coefficient * right_coefficient
    while len(result) > 1 and not result[-1].terms:
        result.pop()
    return result


def add_constant(poly: UPoly, constant: MPoly) -> UPoly:
    return add(poly, [constant])


def add_many(*polys: UPoly) -> UPoly:
    result = [ZERO]
    for poly in polys:
        result = add(result, poly)
    return result


# Inverse of the polynomial q-coordinate change.
a = [ZERO] * 19
a[0] = Q[5]
a[1] = Q[4] + Q[5]
a[2] = Q[3]
a[3] = Q[8]
a[4] = Q[12] + Q[14]
a[5] = Q[14]
a[6] = Q[9]
a[7] = Q[6] + Q[8] + Q[9]
a[8] = Q[13]
a[9] = Q[11] + Q[12] + Q[14]
a[10] = Q[0]
a[11] = Q[1]
a[12] = Q[16]
a[13] = Q[17]
a[14] = Q[10] + Q[12]
a[15] = Q[7] + Q[10] + Q[12] + Q[13] + Q[8] * Q[8] + Q[8]
a[16] = Q[2]
a[17] = Q[15]
a[18] = Q[18]

q_forward = [
    a[10],
    a[11],
    a[16],
    a[2],
    a[0] + a[1],
    a[0],
    a[3] + a[6] + a[7],
    a[14] + a[15] + a[8] + a[3] * a[3] + a[3],
    a[3],
    a[6],
    a[14] + a[4] + a[5],
    a[4] + a[9],
    a[4] + a[5],
    a[8],
    a[5],
    a[17],
    a[12],
    a[13],
    a[18],
]
assert q_forward == Q

# Ten products, beginning with the key-free square.
y = multiply(X, X)
z = multiply(add_constant(y, a[0]), add_constant(add(X, y), a[1]))
t = multiply(add_constant(X, a[2]), add_constant(z, a[3]))
u = multiply(add_constant(add(y, t), a[4]), add_constant(add(z, t), a[5]))
v = multiply(add_constant(add(X, z), a[6]), add_constant(z, a[7]))
w = multiply(
    add_constant(add_many(X, y, z), a[8]),
    add_constant(add(y, v), a[9]),
)
s = multiply(add_constant(X, a[10]), add_constant(y, a[11]))
r = multiply(add_constant(X, a[12]), add_constant(y, a[13]))
q = multiply(add_constant(v, a[14]), add_constant(add_many(t, v, s), a[15]))
crown_factor = add_constant(add_many(u, w, q), a[17])
ell = multiply(add_constant(s, a[16]), crown_factor)
P = add_constant(add(r, ell), a[18])

assert [len(gate) - 1 for gate in (y, z, t, u, v, w, s, r, q, ell)] == [
    2,
    4,
    5,
    10,
    8,
    12,
    3,
    3,
    16,
    19,
]
assert len(P) - 1 == 19
assert P[19] == ONE

# Structural form of the certificate.  The inner crown has the fixed top
# signature (1,0,0,1), after which rows 12 down to 0 decode q3,...,q15.
assert len(crown_factor) - 1 == 16
assert crown_factor[16] == ONE
assert crown_factor[15] == ZERO
assert crown_factor[14] == ZERO
assert crown_factor[13] == ONE
for i in range(3, 16):
    coefficient = 15 - i
    earlier_part = crown_factor[coefficient] + Q[i]
    assert not (earlier_part.variables_used() & set(range(i, NVAR)))
    assert crown_factor[coefficient] == Q[i] + earlier_part

# The proof certificate.
c = P + [ZERO] * (20 - len(P))
term_counts: list[int] = []
for i in range(19):
    coefficient = 18 - i
    earlier_part = c[coefficient] + Q[i]
    assert not (earlier_part.variables_used() & set(range(i, NVAR))), (
        coefficient,
        i,
        earlier_part.variables_used(),
    )
    assert c[coefficient] == Q[i] + earlier_part
    term_counts.append(len(earlier_part.terms))

# Circuit-level accounting in the appendix convention.  Signal indices are
# x,y,z,t,u,v,w,s,r,q,ell.
gate_masks = [
    (0b10, 0b11),
    (0b1, 0b100),
    (0b1010, 0b1100),
    (0b101, 0b100),
    (0b111, 0b100010),
    (0b1, 0b10),
    (0b1, 0b10),
    (0b100000, 0b10101000),
    (0b10000000, 0b1001010000),
]
output_mask = 0b10100000000
def popcount(value: int) -> int:
    """Return the number of set bits (compatible with Python 3.9)."""
    return bin(value).count("1")


xor_count = sum(popcount(left) + popcount(right) for left, right in gate_masks)
xor_count += popcount(output_mask)
assert xor_count == 31

depths = [0, 1]
for left, right in gate_masks:
    used = left | right
    depths.append(1 + max(depths[i] for i in range(len(depths)) if used >> i & 1))
assert depths[-1] == 5


def clmul(left: int, right: int) -> int:
    result = 0
    while right:
        if right & 1:
            result ^= left
        left <<= 1
        right >>= 1
    return result


def evaluate_upper_over_gf2(key_word: int) -> int:
    """Return coefficients x^1,...,x^18 for keys a0,...,a17."""

    key = [(key_word >> i) & 1 for i in range(18)]
    xb = 0b10
    yb = clmul(xb, xb)
    zb = clmul(yb ^ key[0], xb ^ yb ^ key[1])
    tb = clmul(xb ^ key[2], zb ^ key[3])
    ub = clmul(yb ^ tb ^ key[4], zb ^ tb ^ key[5])
    vb = clmul(xb ^ zb ^ key[6], zb ^ key[7])
    wb = clmul(xb ^ yb ^ zb ^ key[8], yb ^ vb ^ key[9])
    sb = clmul(xb ^ key[10], yb ^ key[11])
    rb = clmul(xb ^ key[12], yb ^ key[13])
    qb = clmul(vb ^ key[14], tb ^ vb ^ sb ^ key[15])
    ellb = clmul(sb ^ key[16], ub ^ wb ^ qb ^ key[17])
    pb = rb ^ ellb
    assert (pb >> 19) == 1
    return (pb >> 1) & ((1 << 18) - 1)


def main() -> None:
    images = {evaluate_upper_over_gf2(key_word) for key_word in range(1 << 18)}
    assert len(images) == 1 << 18
    print("Exact GF(2)[q0,...,q18][x] verification passed.")
    print("Gate degrees: 2, 4, 5, 10, 8, 12, 3, 3, 16, 19")
    print("Output: monic degree 19; 10 product gates; 19 keys")
    print("Coefficient map: polynomial-unitriangular over every characteristic-2 field")
    print("Multiplication height: 5")
    print("Polynomial-level XORs: 31")
    print("Earlier-part term counts:", term_counts)
    print("Exhaustive GF(2) upper-coefficient permutation check passed.")


if __name__ == "__main__":
    main()
