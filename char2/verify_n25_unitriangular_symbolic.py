#!/usr/bin/env python3
"""Exact polynomial audit of the square-first (25,13) circuit.

This works in a genuine polynomial ring over GF(2): exponents are not reduced
modulo any finite-field identities.  It checks every elementary pivot in the
24-step certificate from the supplied LaTeX fragment.  Search diagnostics and
the Jacobian play no role.
"""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from tools.char2_polynomial import F2Poly, ONE, X, XPoly, ZERO


def circuit(a: list[F2Poly]) -> tuple[list[XPoly], XPoly]:
    y = X * X
    z = (y + a[0]) * (X + y + a[1])
    t = (X + a[2]) * (z + a[3])
    u = (y + z + t + a[4]) * (z + t + a[5])
    v = (X + a[6]) * (y + z + a[7])
    w = (X + y + z + a[8]) * (y + v + a[9])
    s = (z + a[10]) * (v + a[11])
    r = (X + t + a[12]) * (u + a[13])
    g = (z + t + a[14]) * (X + u + a[15])
    ell = (X + a[16]) * (z + v + a[17])
    h = (y + z + t + a[18]) * (X + y + z + u + v + w + r + a[19])
    j = (X + y + t + a[20]) * (ell + a[21])
    n = (X + t + u + s + r + g + ell + h + j + a[22]) * (t + a[23])
    p = y + z + u + ell + n + a[24]
    return [y, z, t, u, v, w, s, r, g, ell, h, j, n], p


def certify(verbose: bool = True) -> dict:
    """Run the exact 24-step certificate; returns pivot_order, the tails tau_i, the baselines,
    the fully substituted keys a(q) and the final circuit output, for reuse by char2/verify_n25.py."""
    pivot_order = [
        2, 0, 1, 3, 4, 12, 6, 5, 23, 7, 9, 13,
        8, 17, 10, 11, 15, 19, 21, 22, 18, 16, 14, 20,
    ]
    assert sorted(pivot_order) == list(range(24))

    active = {j: F2Poly.var(f"b{j}") for j in range(24)}
    decoded = [F2Poly.var(f"q{i}") for i in range(24)]
    a = [active[j] for j in range(24)] + [F2Poly.var("a24")]
    remaining = set(range(24))
    baselines: list[F2Poly] = []
    tails: list[F2Poly] = []

    for i, pivot in enumerate(pivot_order):
        gates, p = circuit(a)
        if i == 0:
            assert [g.degree for g in gates] == [2, 4, 5, 10, 5, 9, 9, 15, 15, 6, 20, 11, 25]
            assert p.degree == 25 and p.coeff(25) == ONE

        row = 24 - i
        coeff = p.coeff(row)
        zero_later = {f"b{j}": ZERO for j in remaining}
        baseline = coeff.subs_many(zero_later)
        baselines.append(baseline)
        residual = coeff + baseline
        name = f"b{pivot}"

        # The claimed naked unit pivot, in the full polynomial ring.
        assert residual.degree(name) == 1, (i, row, pivot, residual.degree(name))
        assert residual.coeff_wrt(name, 1) == ONE, (i, row, pivot)
        tail = residual + active[pivot]
        assert name not in tail.variables(), (i, row, pivot)

        # q_i = b_pivot + tail; equivalently b_pivot = q_i + tail.
        tails.append(tail)
        replacement = decoded[i] + tail
        a = [expr.subs(name, replacement) for expr in a]
        remaining.remove(pivot)

        # Re-evaluate the row after the elementary coordinate change.  It must
        # now be exactly q_i plus its already-decoded baseline.
        _, p_after = circuit(a)
        assert p_after.coeff(row) == decoded[i] + baseline, (i, row, pivot)
        assert not (baseline.variables() & {f"b{j}" for j in remaining}), (i, row)

        if verbose:
            print(
                f"pivot {i:2d}: row {row:2d} -> a_{pivot:2d}; "
                f"tail {len(tail.t):5d} monomials"
            )

    # With all 24 elementary changes applied, the whole nonconstant window is
    # unitriangular in q_0,...,q_23.
    _, p_final = circuit(a)
    for i, qi in enumerate(decoded):
        row = 24 - i
        residual = p_final.coeff(row) + qi
        assert not (residual.variables() & {f"q{j}" for j in range(i, 24)}), (i, row)

    # The final scalar is a literal unit pivot in row zero.
    assert p_final.coeff(0).degree("a24") == 1
    assert p_final.coeff(0).coeff_wrt("a24", 1) == ONE
    return {
        "pivot_order": pivot_order,
        "tails": tails,
        "baselines": baselines,
        "a": a,
        "q": decoded,
        "p_final": p_final,
    }


def main() -> None:
    certify()
    print("PASS: all 24 unit pivots and the final scalar are exact over GF(2)[keys].")


if __name__ == "__main__":
    main()
