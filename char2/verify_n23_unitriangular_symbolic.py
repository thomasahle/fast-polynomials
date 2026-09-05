#!/usr/bin/env python3
"""Exact polynomial audit of the square-first (23,12) circuit.

The proof is replayed in GF(2)[q0,...,q22][x].  It verifies the supplied
polynomial key-coordinate inverse, the long unitriangular prefix, and the
explicit four-row terminal block.  No finite-field reduction, search, rank,
or Jacobian criterion is used.
"""

import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))

from tools.char2_inverse_finder import F2Poly, ONE, X, XPoly, ZERO


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
    m = (X + y + z + a[18]) * (X + y + z + w + s + g + ell + a[19])
    n = (z + a[20]) * (u + m + a[21])
    p = y + v + w + s + r + g + n + a[22]
    return [y, z, t, u, v, w, s, r, g, ell, m, n], p


def main() -> None:
    q = [F2Poly.var(f"q{i}") for i in range(23)]
    a = [ZERO] * 23

    a[0] = q[2]
    a[1] = q[1] + q[2]
    a[2] = q[0]
    a[3] = q[3] + q[5] + q[6]
    a[4] = q[4] + q[5] + q[6] + q[7]
    a[5] = q[16]
    a[6] = q[8]
    a[7] = q[11] + q[7] * q[16] + q[16] ** 2 + q[20]
    a[12] = q[15] + q[16]
    a[13] = q[17] + q[18]
    a[14] = q[7] + q[16]
    a[15] = q[20]
    a[16] = q[18]
    a[17] = q[21]
    a[18] = q[5]
    a[20] = q[6]
    a[21] = q[19]
    a[22] = q[22]

    rho = (
        q[0] * q[7] * q[16]
        + q[0] * q[16] ** 2
        + q[0] * q[20]
        + q[7] * q[8] * q[16]
        + q[7] * q[16]
        + q[8] * q[16] ** 2
        + q[8] * q[20]
        + q[16] ** 2
    )
    aa = q[0] + q[3] + q[5] + q[6] + q[7] ** 2 + q[8] + q[9] + q[11] + 1
    bb = (
        q[0] * q[7]
        + q[3] * q[7]
        + q[5] * q[7]
        + q[6] * q[7]
        + q[7] * q[8]
        + q[7] * q[9]
        + q[7] * q[11]
        + q[7]
        + 1
    )
    cc = q[0] + q[3] + q[5] + q[6] + q[8] + q[9] + q[11] + 1
    a[11] = q[13] + q[16] ** 4 + aa * q[16] ** 2 + bb * q[16] + q[20] ** 2 + cc * q[20] + q[18] + q[21]
    a[10] = q[12] + rho + q[16] + a[11] + a[12]
    a[9] = q[10] + rho + a[11] + q[20] + q[18]
    a[8] = q[9] + q[16] ** 2 + q[7] * q[16] + a[10] + q[20] + q[18]

    # The q14 coordinate is the row-eight output coefficient.  Its inverse is
    # triangular because a19 occurs in that row with unit slope and nowhere in
    # the previously reconstructed key formulas.
    a[19] = ZERO
    a22_saved = a[22]
    a[22] = ZERO
    _, p_hat = circuit(a)
    h14 = p_hat.coeff(8)
    a[19] = q[14] + h14
    a[22] = a22_saved

    gates, p = circuit(a)
    assert [g.degree for g in gates] == [2, 4, 5, 10, 5, 9, 9, 15, 15, 6, 19, 23]
    assert p.degree == 23 and p.coeff(23) == ONE

    # Replay the forward coordinate formulas (1)--(5).
    forward: list[F2Poly | None] = [None] * 23
    forward[0] = a[2]
    forward[1] = a[0] + a[1]
    forward[2] = a[0]
    forward[3] = a[3] + a[18] + a[20]
    forward[4] = a[4] + a[5] + a[14] + a[18] + a[20]
    forward[5] = a[18]
    forward[6] = a[20]
    forward[7] = a[5] + a[14]
    forward[8] = a[6]
    forward[9] = a[5] ** 2 + q[7] * a[5] + a[8] + a[10] + a[15] + a[16]
    forward[10] = rho + a[9] + a[11] + a[15] + a[16]
    forward[11] = q[7] * a[5] + a[5] ** 2 + a[7] + a[15]
    forward[12] = rho + a[5] + a[10] + a[11] + a[12]
    forward[13] = a[5] ** 4 + aa * a[5] ** 2 + bb * a[5] + a[15] ** 2 + cc * a[15] + a[11] + a[16] + a[17]
    forward[14] = p.coeff(8)
    forward[15] = a[5] + a[12]
    forward[16] = a[5]
    forward[17] = a[13] + a[16]
    forward[18] = a[16]
    forward[19] = a[21]
    forward[20] = a[15]
    forward[21] = a[17]
    forward[22] = a[22]
    assert forward == q

    # Long unitriangular prefix: rows 22,...,9 recover q0,...,q13.
    for i in range(14):
        residual = p.coeff(22 - i) + q[i]
        assert not (residual.variables() & {f"q{j}" for j in range(i, 23)}), (i, 22 - i)

    assert p.coeff(8) == q[14]
    for i, row in [(15, 7), (16, 6), (17, 5)]:
        residual = p.coeff(row) + q[i]
        assert not (residual.variables() & {f"q{j}" for j in range(i, 23)}), (i, row)

    # Explicit terminal four-row block (12)--(14).
    lam4 = q[1] ** 2 + q[1] + q[5] + q[6] + 1
    lam3 = q[1] + q[2] + q[5] + q[6]
    lam2 = q[1] * q[2] + q[1] * q[5] + q[1] * q[6] + q[2] + q[6]
    lam1 = q[1] * q[2] + q[2] ** 2 + q[2] * q[5] + q[2] * q[6] + q[6]
    es: dict[int, F2Poly] = {}
    for row, lam in [(4, lam4), (3, lam3), (2, lam2), (1, lam1)]:
        dj = p.coeff(row) + lam * q[14]
        kappa = dj.subs_many({f"q{j}": ZERO for j in range(18, 22)})
        es[row] = dj + kappa

    assert es[4] == (q[0] + q[8] + 1) * q[18] + q[19]
    assert es[3] == (q[0] + q[8]) * q[18] + q[19]
    assert es[2] == (q[1] * (q[0] + q[8] + 1) + q[8]) * q[18] + q[1] * q[19] + q[20]
    terminal_coeff = q[0] * q[2] + q[2] * q[8] + q[2] + q[3] + q[5] + q[6] + q[7] * q[16] + q[11] + q[16] ** 2 + 1
    assert es[1] == terminal_coeff * q[18] + q[2] * q[19] + q[8] * q[20] + q[18] * q[20] + q[20] + q[21]

    recovered18 = es[4] + es[3]
    recovered19 = es[3] + (q[0] + q[8]) * recovered18
    recovered20 = es[2] + (q[1] * (q[0] + q[8] + 1) + q[8]) * recovered18 + q[1] * recovered19
    recovered21 = es[1] + terminal_coeff * recovered18 + q[2] * recovered19 + q[8] * recovered20 + recovered18 * recovered20 + recovered20
    assert [recovered18, recovered19, recovered20, recovered21] == q[18:22]

    constant_without_q22 = p.coeff(0).subs("q22", ZERO)
    assert p.coeff(0) == q[22] + constant_without_q22
    print("PASS: key-coordinate inverse, 18 scalar pivots, four-row block, and final scalar are exact.")


if __name__ == "__main__":
    main()
