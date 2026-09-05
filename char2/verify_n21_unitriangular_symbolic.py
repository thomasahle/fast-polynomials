#!/usr/bin/env python3
"""Exact audit of the square-first characteristic-two (21, 11) circuit.

The proof calculation is in ``GF(2)[q0,...,q20][x]``.  After the explicitly
invertible polynomial change of key coordinates below, it verifies

    [x^(20-i)] P = q_i + K_i(q_0,...,q_(i-1)),  0 <= i <= 20.

Thus the coefficient map has a polynomial inverse after base change to every
field of characteristic two.  The exhaustive binary check at the end is an
independent diagnostic, not the proof.
"""
from __future__ import annotations

from dataclasses import dataclass
from typing import FrozenSet, List, Tuple

NVAR = 21
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
    for i, left_coeff in enumerate(left):
        for j, right_coeff in enumerate(right):
            result[i + j] = result[i + j] + left_coeff * right_coeff
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


# Inverse of the polynomial q-coordinate change: original keys in terms of q.
a = [ZERO] * 21
a[0] = Q[2]
a[1] = Q[1] + Q[2]
a[2] = Q[0]
a[3] = Q[3]
a[4] = Q[12] + Q[14]
a[5] = Q[14]
a[6] = Q[9]
a[7] = Q[6] + Q[8] + Q[3] + Q[9]
a[8] = Q[13]
a[9] = Q[11] + Q[12] + Q[14]
a[10] = Q[5]
a[11] = Q[8]
a[12] = Q[18]
a[13] = Q[19]
a[14] = Q[10] + Q[12]
a[15] = (
    Q[7]
    + Q[8]
    + Q[8] * Q[8]
    + Q[0] * Q[8]
    + Q[5] * Q[8]
    + Q[10]
    + Q[12]
    + Q[13]
    + Q[3] * Q[3]
    + Q[3]
)
a[16] = Q[4] + Q[16]
a[17] = Q[17]
a[18] = Q[16]
a[19] = Q[15]
a[20] = Q[20]

q_forward = [
    a[2],
    a[0] + a[1],
    a[0],
    a[3],
    a[16] + a[18],
    a[10],
    a[3] + a[6] + a[7] + a[11],
    a[14]
    + a[15]
    + a[8]
    + a[3] * a[3]
    + a[3]
    + a[11]
    + a[11] * a[11]
    + a[2] * a[11]
    + a[10] * a[11],
    a[11],
    a[6],
    a[14] + a[4] + a[5],
    a[4] + a[9],
    a[4] + a[5],
    a[8],
    a[5],
    a[19],
    a[18],
    a[17],
    a[12],
    a[13],
    a[20],
]
assert q_forward == Q

# Eleven products, beginning with the key-free square.
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
ell = multiply(add_constant(s, a[16]), add_constant(add_many(u, w, q), a[17]))
m = multiply(
    add_constant(add(t, s), a[18]),
    add_constant(add_many(z, u, w, q), a[19]),
)
P = add_constant(add_many(m, z, r, ell), a[20])

assert [len(gate) - 1 for gate in (y, z, t, u, v, w, s, r, q, ell, m)] == [
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
    21,
]
assert len(P) - 1 == 21
assert P[21] == ONE

c = P + [ZERO] * (22 - len(P))
term_counts: list[int] = []
for i in range(21):
    coefficient = 20 - i
    earlier_part = c[coefficient] + Q[i]
    assert not (earlier_part.variables_used() & set(range(i, NVAR))), (
        coefficient,
        i,
        earlier_part.variables_used(),
    )
    assert c[coefficient] == Q[i] + earlier_part
    term_counts.append(len(earlier_part.terms))

# The first rows quoted in the manuscript.
assert c[20] == ONE + Q[0]
assert c[19] == Q[0] + Q[1]
assert c[18] == ONE + Q[2] + Q[0] * Q[1]
assert c[17] == Q[3] + Q[2] * Q[2] + Q[0] * Q[2] + Q[1] * Q[2]
assert c[16] == (
    Q[4]
    + Q[0] * Q[0]
    + Q[0] * Q[3]
    + Q[0] * Q[2] * Q[2]
    + Q[0] * Q[1] * Q[2]
)
assert c[15] == ONE + Q[1] + Q[5]
assert c[14] == (
    ONE
    + Q[1]
    + Q[2]
    + Q[3]
    + Q[5]
    + Q[6]
    + Q[0] * Q[1]
    + Q[0] * Q[5]
)
assert c[13] == (
    Q[2]
    + Q[3]
    + Q[4]
    + Q[5]
    + Q[7]
    + Q[1] * Q[1] * Q[1] * Q[1]
    + Q[2] * Q[2]
    + Q[6] * Q[6]
    + Q[0] * Q[1]
    + Q[0] * Q[2]
    + Q[0] * Q[5]
    + Q[1] * Q[2]
    + Q[1] * Q[5]
)

# Polynomial-XOR count.  Signal indices are x,y,z,t,u,v,w,s,r,q,ell,m.
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
    (0b10001000, 0b1001010100),
]
output_mask = 0b110100000100


def popcount(value: int) -> int:
    """Number of set bits (spelled compatibly with Python 3.9)."""
    return bin(value).count("1")


xor_count = sum(popcount(left) + popcount(right) for left, right in gate_masks)
xor_count += popcount(output_mask)
assert xor_count == 39

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
    """Return coefficients x^1,...,x^20 for keys a0,...,a19."""
    key = [(key_word >> i) & 1 for i in range(20)]
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
    mb = clmul(tb ^ sb ^ key[18], zb ^ ub ^ wb ^ qb ^ key[19])
    pb = mb ^ zb ^ rb ^ ellb
    assert (pb >> 21) == 1
    return (pb >> 1) & ((1 << 20) - 1)


def main() -> None:
    seen = bytearray(1 << 20)
    for key_word in range(1 << 20):
        image = evaluate_upper_over_gf2(key_word)
        assert not seen[image], (key_word, image)
        seen[image] = 1

    print("Exact GF(2)[q0,...,q20][x] verification passed.")
    print("Gate degrees: 2, 4, 5, 10, 8, 12, 3, 3, 16, 19, 21")
    print("Output: monic degree 21; 11 product gates; 21 keys")
    print("Coefficient map: polynomial-unitriangular over every characteristic-2 field")
    print("Multiplication height: 5")
    print("Polynomial-level XORs: 39")
    print("Earlier-part term counts:", term_counts)
    print("Exhaustive GF(2) upper-coefficient permutation check passed.")


if __name__ == "__main__":
    main()
