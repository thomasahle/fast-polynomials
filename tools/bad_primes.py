#!/usr/bin/env python3
"""
bad_primes.py — the exact set of primes dividing a scalar pivot or block
determinant of the paper's decoder for the degree-n family P_n[alpha].

The paper (sections/constructions/*.tex) proves decodability of P_n over any
"n-admissible" field (characteristic 0 or p > n).  That hypothesis is only a
convenient sufficient condition: the displayed decoders divide by a finite
list of fixed integers, and the recursion of `alg:final-construction`
determines exactly which integers occur for a given n.  This script replays
that routing and returns

    Bad(n) = { p prime : p divides some scalar pivot or block determinant
                         that the decoder for P_n divides by }.

The decoder for P_n is defined, and inverts the construction, over every
field in which the integers listed by `pivots(n)` are units, i.e. whose
characteristic is not in Bad(n).

Pivot inventory (paper locations in parentheses):

  * 2 — monic square roots (`lem:monic-from-power` with m=2), square-gadget
    boundary (`lem:square-gadget-boundary`), scalar shifts of squares
    (`lem:scalar-shift-square`), the septic base and the finite bases 15/27/31.
  * 4k+1 crown (`lem:4k+1-splittable`): slopes 2k, 2k, -2k, k, k.
  * Q_{4k+1} given H_2 (`lem:Q4k+1-from-H2`): slopes 1, 2k, -2k, k, k.
  * perturbed T call (`lem:causal-perturbed-T`, inside the known-powers odd
    gadget `alg:constr-Q-odd`): slope M = 2k on the Q-block and delta rows.
  * T-recursion stage tables (`lem:Rk2l`, `alg:decode-Rk2l`):
      - k even, m = k/2: slopes -2m = -k and m, the boundary scalar with
        slope k/2 = m, one monic square root (2) and one scalar-shift (2);
        leading coefficient gamma_k = m.
      - k odd, m = (k-1)/2, c = k(k-1)/2: slopes -2c = -k(k-1), -2m = -(k-1),
        m; leading coefficient gamma_k = c.
    The seam corrections gamma_m, binom(m,2), tau = k(k-1)(k-2)/3 = 2*binom(k,3)
    and theta_m are integers that are subtracted, never divided by, so they
    contribute nothing.
  * barred gadget bar Q_{8k+7} (`lem:barQ8k+7`): block determinant
    det M = -k^2 and the two slopes k (rows for w and rho).
  * fill gadgets A_{2^l}, known-powers gadgets Q_{2^t-1}, the peeled
    Q^{peel}, Q_1, Q_3, Q_7, the degree-3 base, and the even lift use only
    unit pivots and monic division: no constants.

Usage:
    python3 tools/bad_primes.py 29            # Bad(29) and the pivot trace
    python3 tools/bad_primes.py 5 9 15 17 31  # several n
    python3 tools/bad_primes.py --table 3 64  # one line per n in [3, 64]
    python3 tools/bad_primes.py --check 4096  # sanity bounds for n <= 4096
"""

from __future__ import annotations

import argparse
import sys
from typing import List, Set, Tuple

Pivot = Tuple[str, int]  # (where it is divided, the integer)


# ---------------------------------------------------------------------------
# Number theory helpers
# ---------------------------------------------------------------------------


def prime_factors(m: int) -> Set[int]:
    m = abs(m)
    out: Set[int] = set()
    d = 2
    while d * d <= m:
        while m % d == 0:
            out.add(d)
            m //= d
        d += 1
    if m > 1:
        out.add(m)
    return out


# ---------------------------------------------------------------------------
# Pivot inventories of the individual gadgets
# ---------------------------------------------------------------------------


def T_pivots(k: int, l: int) -> List[Pivot]:
    """Pivots of the decoder of x R^{(1)}_{k,2^l} + R^{(2)}_{k,2^l} (alg:decode-Rk2l)."""

    if l < 2:
        raise ValueError("alg:decode-Rk2l is invoked with l >= 2")
    if k < 1:
        raise ValueError("k >= 1")
    if k == 1:
        return []
    tag = f"T({k},{2 ** l})"
    if k % 2 == 0:
        m = k // 2
        piv: List[Pivot] = [
            (f"{tag} even: slope -2m = -k on the S1/delta rows", -k),
            (f"{tag} even: monic square root of S1 (÷2)", 2),
            (f"{tag} even: scalar shift of the squared branch (÷2)", 2),
            (f"{tag} even: slope m on the S2 rows", m),
            (f"{tag} even: slope k/2 on the boundary scalar", m),
            (f"{tag} even: leading coefficient gamma_k = m", m),
        ]
        return piv + T_pivots(m, l + 1)
    m = (k - 1) // 2
    c = k * (k - 1) // 2
    if l == 2:
        piv = [
            (f"{tag} odd shared base: slope -k(k-1) for u", -k * (k - 1)),
            (f"{tag} odd shared base: slope -(k-1) for v", -(k - 1)),
            (f"{tag} odd shared base: slope m for w", m),
            (f"{tag} odd shared base: slope m for z", m),
            (f"{tag} odd shared base: leading coefficient gamma_k = k(k-1)/2", c),
        ]
        return piv + T_pivots(m, 3)
    piv = [
        (f"{tag} odd: slope -2c = -k(k-1) on the Q_+/delta rows", -k * (k - 1)),
        (f"{tag} odd: slope -2m = -(k-1) on the Q_0/epsilon rows", -(k - 1)),
        (f"{tag} odd: slope m on the Q_-/zeta rows", m),
        (f"{tag} odd: leading coefficient gamma_k = c", c),
    ]
    return piv + T_pivots(m, l + 1)


def crown_pivots(k: int) -> List[Pivot]:
    """Five top pivots of the 4k+1 construction (lem:4k+1-splittable)."""

    tag = f"crown(4·{k}+1)"
    return [
        (f"{tag}: slope 2k for b", 2 * k),
        (f"{tag}: slope 2k for c", 2 * k),
        (f"{tag}: slope -2k for a", -2 * k),
        (f"{tag}: slope k for e", k),
        (f"{tag}: slope k for rho", k),
    ]


def Q4k1_pivots(k: int) -> List[Pivot]:
    """Q_{4k+1}(x, H_2) decoded given H_2 (lem:Q4k+1-from-H2)."""

    tag = f"Q_{4 * k + 1}(H2)"
    piv: List[Pivot] = [
        (f"{tag}: slope 1 for beta", 1),
        (f"{tag}: slope 2k for gamma", 2 * k),
        (f"{tag}: slope -2k for a", -2 * k),
        (f"{tag}: slope k for e", k),
        (f"{tag}: slope k for rho", k),
    ]
    return piv + T_pivots(k, 2)


def perturbed_T_pivots(M: int, l: int) -> List[Pivot]:
    """The perturbed even call T_{M,2^l} (lem:causal-perturbed-T)."""

    tag = f"perturbed T({M},{2 ** l})"
    return [(f"{tag}: slope M on the Q-block and delta rows", M)] + T_pivots(M, l)


def Q_known_powers_odd_pivots(d: int, l: int) -> List[Pivot]:
    """Odd gadget Q_d, d = 2^{l+1} k + (2^l - 1), from (H_2..H_{2^l}) (alg:constr-Q-odd)."""

    if (d + 1) % (1 << (l + 1)) != (1 << l):
        raise ValueError(f"degree {d} is not of the form 2^{l + 1} k + 2^{l} - 1")
    k = (d + 1 - (1 << l)) >> (l + 1)
    # hat H_{2^l} = H_{2^l} + Q_{2^{l-1}-1}: unit pivots; outer A_{2^{l-1}}: unit pivots.
    return perturbed_T_pivots(2 * k, l)


def barQ_pivots(k: int) -> List[Pivot]:
    """The barred gadget bar Q_{8k+7} given (H_2, H_4) (lem:barQ8k+7)."""

    tag = f"barQ_{8 * k + 7}(H2,H4)"
    piv: List[Pivot] = [
        (f"{tag}: block determinant det M = -k^2", -k * k),
        (f"{tag}: slope k for w", k),
        (f"{tag}: slope k for rho", k),
    ]
    return piv + T_pivots(k, 3)


def selected_gadget_pivots(d: int) -> List[Pivot]:
    """The selected odd gadget script-Q_d of `lem:odd-gadgets-H2H4`."""

    if d in (1, 3, 7):
        return []  # Q_1, Q_3, Q_7: unit pivots only
    if d % 4 == 1:
        return Q4k1_pivots((d - 1) // 4)
    if d % 8 == 3:
        return Q_known_powers_odd_pivots(d, 2)
    if d % 8 == 7:
        return barQ_pivots((d - 7) // 8)
    raise ValueError(f"script-Q_{d}: d must be odd")


# ---------------------------------------------------------------------------
# alg:final-construction routing
# ---------------------------------------------------------------------------


def pair_pivots(n: int) -> List[Pivot]:
    """Pivots of the decoder of the splittable pair for odd n != 7."""

    if n < 3 or n % 2 == 0 or n == 7:
        raise ValueError("pair_pivots needs odd n >= 3, n != 7")
    if n == 3:
        return []  # lem:base-three-compatible: no division
    if n == 15:
        return [("P_15: relative square shell and H_4 block (÷2)", 2)]
    if n == 27:
        return [("P_27: square shells and H_2 block (÷2)", 2)] + Q4k1_pivots(3)
    if n == 31:
        return [("P_31: square gadget, square shells, H_4 block (÷2)", 2)] + barQ_pivots(1)
    if n % 4 == 1:
        k = (n - 1) // 4
        return crown_pivots(k) + T_pivots(k, 2)
    if n % 8 == 3:
        k = (n - 3) // 8
        piv: List[Pivot] = [
            (f"P_{n} (8k+3): square-gadget boundary (÷2)", 2),
            (f"P_{n} (8k+3): monic square roots of the smaller pair (÷2)", 2),
        ]
        piv += pair_pivots(2 * k + 1)
        piv += Q4k1_pivots(k)
        if k > 1:
            piv += selected_gadget_pivots(2 * k - 1)
        return piv
    # n = 8k+7 with k >= 2, k not in {1, 3}
    k = (n - 7) // 8
    piv = [
        (f"P_{n} (8k+7): first square-gadget boundary (÷2)", 2),
        (f"P_{n} (8k+7): second square-gadget boundary (÷2)", 2),
    ]
    piv += pair_pivots(2 * k + 1)
    piv += selected_gadget_pivots(2 * k + 1)
    piv += selected_gadget_pivots(4 * k + 3)
    return piv


def pivots(n: int) -> List[Pivot]:
    """Every integer the decoder of P_n divides by, with its location."""

    if n < 1:
        raise ValueError("n >= 1")
    if n == 1:
        return []
    if n % 2 == 0:
        return pivots(n - 1)  # even lift: read c_0, shift, recurse
    if n == 7:
        return [("P_7 (lem:septic-base): z_2 = c_6/2, z_1 = (...)/2", 2)]
    return pair_pivots(n)


def bad_primes(n: int) -> Set[int]:
    out: Set[int] = set()
    for _, v in pivots(n):
        out |= prime_factors(v)
    return out


def fmt_set(s: Set[int]) -> str:
    return "{" + ", ".join(str(p) for p in sorted(s)) + "}"


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def main(argv: List[str]) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("n", nargs="*", type=int)
    ap.add_argument("--table", nargs=2, type=int, metavar=("LO", "HI"), help="print Bad(n) for LO <= n <= HI")
    ap.add_argument("--check", type=int, metavar="N", help="verify structural bounds for all n <= N")
    ap.add_argument("--quiet", action="store_true", help="omit the pivot trace")
    args = ap.parse_args(argv)

    if args.check:
        for n in range(1, args.check + 1):
            bad = bad_primes(n)
            for p in bad:
                assert p <= n, (n, p)
                if p != 2:
                    assert p <= (n - 1) // 4, (n, p)
            if n >= 5:
                assert 2 in bad, n
        print(f"checked n <= {args.check}: Bad(n) ⊆ {{2}} ∪ {{p ≤ (n-1)/4}}, and 2 ∈ Bad(n) for n ≥ 5")
    if args.table:
        lo, hi = args.table
        for n in range(lo, hi + 1):
            print(f"{n:5d}  {fmt_set(bad_primes(n))}")
    for n in args.n:
        bad = bad_primes(n)
        print(f"Bad({n}) = {fmt_set(bad)}")
        if not args.quiet:
            for where, v in pivots(n):
                print(f"    {v:>8d}   {where}")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
