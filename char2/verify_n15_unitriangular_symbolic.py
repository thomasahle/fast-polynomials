#!/usr/bin/env python3
"""Exact unitriangular certificate for the square-first ``(15, 8)`` circuit.

The calculation takes place in ``F_2[q_0, ..., q_14][x]``.  Consequently the
checked identities prove a polynomial inverse after base change to every field
of characteristic two; the optional exhaustive ``F_2`` check at the end is only
a diagnostic.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet, List, Tuple


NVAR = 15
Monomial = Tuple[int, ...]


@dataclass(frozen=True)
class MPoly:
    """A sparse polynomial in the key coordinates over ``F_2``."""

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
UPoly = List[MPoly]  # coefficients in x, in ascending order
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


# Inverse of the linear change from gate offsets a_i to decoder coordinates q_i.
a = [ZERO] * 15
a[0] = Q[2]
a[1] = Q[1] + Q[2]
a[2] = Q[0]
a[3] = Q[3]
a[4] = Q[4] + Q[5] + Q[7]
a[5] = Q[5]
a[6] = Q[8] + Q[11]
a[7] = Q[11]
a[8] = Q[6] + Q[12] + Q[13]
a[9] = Q[13]
a[10] = Q[12] + Q[13]
a[11] = Q[10] + Q[13]
a[12] = Q[7]
a[13] = Q[9]
a[14] = Q[14]

assert [
    a[2],
    a[0] + a[1],
    a[0],
    a[3],
    a[4] + a[5] + a[12],
    a[5],
    a[8] + a[10],
    a[12],
    a[6] + a[7],
    a[13],
    a[9] + a[11],
    a[7],
    a[9] + a[10],
    a[9],
    a[14],
] == Q


# Eight products, beginning with the parameter-free square y=x^2.
y = multiply(X, X)
z = multiply(add_constant(y, a[0]), add_constant(add(X, y), a[1]))
t = multiply(add_constant(X, a[2]), add_constant(z, a[3]))
u = multiply(add_constant(add(y, t), a[4]), add_constant(add(z, t), a[5]))
v = multiply(add_constant(add(X, z), a[6]), add_constant(z, a[7]))
w = multiply(
    add_constant(add(add(X, y), z), a[8]),
    add_constant(add(y, v), a[9]),
)
s = multiply(add_constant(z, a[10]), add_constant(v, a[11]))
r = multiply(add_constant(t, a[12]), add_constant(u, a[13]))
P = add_constant(add(add(w, s), r), a[14])

assert [len(gate) - 1 for gate in (y, z, t, u, v, w, s, r)] == [
    2,
    4,
    5,
    10,
    8,
    12,
    12,
    15,
]
assert len(P) - 1 == 15
assert P[15] == ONE


# The complete explicit decoder certificate.  Reading coefficients from x^14
# down to x^0 recovers q_0,...,q_14, each with unit slope.
c = P + [ZERO] * (16 - len(P))
term_counts: list[int] = []
for i in range(15):
    coefficient = 14 - i
    earlier_part = c[coefficient] + Q[i]
    assert not (earlier_part.variables_used() & set(range(i, NVAR)))
    assert c[coefficient] == Q[i] + earlier_part
    term_counts.append(len(earlier_part.terms))


def popcount(value: int) -> int:
    """Python-3.9-compatible population count."""

    return bin(value).count("1")


# Circuit-level counts under the appendix's polynomial-XOR convention.
gate_masks = [
    (0b10, 0b11),       # z
    (0b1, 0b100),       # t
    (0b1010, 0b1100),   # u
    (0b101, 0b100),     # v
    (0b111, 0b100010),  # w
    (0b100, 0b100000),  # s
    (0b1000, 0b10000),  # r
]
output_mask = 0b111000000  # w+s+r
assert sum(popcount(left) + popcount(right) for left, right in gate_masks) + popcount(
    output_mask
) == 24

depths = [0, 1]  # x and y
for left, right in gate_masks:
    used = left | right
    depths.append(
        1 + max(depths[i] for i in range(len(depths)) if (used >> i) & 1)
    )
assert depths[-1] == 5


def clmul(left: int, right: int) -> int:
    result = 0
    while right:
        if right & 1:
            result ^= left
        left <<= 1
        right >>= 1
    return result


def evaluate_over_gf2(key_word: int) -> int:
    key = [(key_word >> i) & 1 for i in range(15)]
    x_bits = 0b10
    y_bits = clmul(x_bits, x_bits)
    z_bits = clmul(y_bits ^ key[0], x_bits ^ y_bits ^ key[1])
    t_bits = clmul(x_bits ^ key[2], z_bits ^ key[3])
    u_bits = clmul(y_bits ^ t_bits ^ key[4], z_bits ^ t_bits ^ key[5])
    v_bits = clmul(x_bits ^ z_bits ^ key[6], z_bits ^ key[7])
    w_bits = clmul(x_bits ^ y_bits ^ z_bits ^ key[8], y_bits ^ v_bits ^ key[9])
    s_bits = clmul(z_bits ^ key[10], v_bits ^ key[11])
    r_bits = clmul(t_bits ^ key[12], u_bits ^ key[13])
    return w_bits ^ s_bits ^ r_bits ^ key[14]


if __name__ == "__main__":
    # This finite check is independent confirmation, not the proof.
    images = {
        evaluate_over_gf2(key_word) & ((1 << 15) - 1)
        for key_word in range(1 << 15)
    }
    assert len(images) == 1 << 15
    print("Exact GF(2)[q0,...,q14][x] unitriangular certificate: PASS")
    print("Gate degrees: 2, 4, 5, 10, 8, 12, 12, 15")
    print("Products: 8; polynomial-level XORs: 24; multiplication height: 5")
    print("Earlier-part term counts:", term_counts)
    print("Exhaustive GF(2) diagnostic: PASS")
