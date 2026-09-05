from __future__ import annotations

"""
Tiny GF(2^k) field implementation (XOR-additive) for char2 experiments.

This is intended for correctness/proof experiments and decoder validation (e.g. GF(16)),
not high-performance arithmetic.

Representation:
  - Elements are k-bit integers (polynomial basis over GF(2)).
  - Addition is XOR.
  - Multiplication is carryless multiply reduced modulo an irreducible polynomial.
"""

from dataclasses import dataclass


@dataclass(frozen=True)
class GF2k:
    """
    GF(2^k) with a polynomial basis.

    Args:
      k: extension degree.
      mod: irreducible polynomial as an int bitmask including the x^k term.
           Example for GF(16): x^4 + x + 1 => 0b1_0011 (0x13).
    """

    k: int
    mod: int

    @property
    def mask(self) -> int:
        return (1 << self.k) - 1

    def add(self, a: int, b: int) -> int:
        return (a ^ b) & self.mask

    sub = add

    def mul(self, a: int, b: int) -> int:
        a &= self.mask
        b &= self.mask
        res = 0
        aa = a
        bb = b
        top_bit = 1 << self.k
        while bb:
            if bb & 1:
                res ^= aa
            bb >>= 1
            aa <<= 1
            if aa & top_bit:
                aa ^= self.mod
        return res & self.mask

    def sq(self, a: int) -> int:
        return self.mul(a, a)

    def pow(self, a: int, e: int) -> int:
        if e < 0:
            raise ValueError("negative exponent")
        a &= self.mask
        res = 1
        base = a
        ee = e
        while ee:
            if ee & 1:
                res = self.mul(res, base)
            ee >>= 1
            if ee:
                base = self.mul(base, base)
        return res & self.mask

    def inv(self, a: int) -> int:
        a &= self.mask
        if a == 0:
            raise ZeroDivisionError("0 has no inverse in GF(2^k)")
        # a^(2^k-2)
        return self.pow(a, (1 << self.k) - 2)

    def root_pow2(self, a: int, t: int) -> int:
        """
        Unique (2^t)-th root in GF(2^k):
          (a^(2^(k-t)))^(2^t) = a^(2^k) = a.
        """
        if t < 0 or t > self.k:
            raise ValueError("t must satisfy 0 <= t <= k")
        out = a & self.mask
        for _ in range(self.k - t):
            out = self.sq(out)
        return out

