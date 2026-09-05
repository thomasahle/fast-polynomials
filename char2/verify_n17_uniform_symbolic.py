#!/usr/bin/env python3
from __future__ import annotations

"""Exact symbolic audit of the proposed uniform characteristic-two (17, 9) circuit.

The calculation takes place in the polynomial ring F2[z1,...,z17].  It checks two
logically separate assertions.

1.  The selected internal coefficients ``q0,...,q16`` give polynomial coordinates
    on the original gate offsets.  The inverse is constructed gate by gate using
    unequal-degree unit pivots (and the displayed two-row solve for ``t``).
2.  In the proposed coordinate order, every selected output coefficient is a
    Frobenius power of the new coordinate plus a polynomial in earlier coordinates.

Thus this is not a finite-field screen or a Jacobian calculation.  If it succeeds,
the asserted triangular decoder is a literal identity over F2 and hence over every
perfect field of characteristic two.
"""

from .symexpr import Expr, Poly, poly_coeff, poly_mul, poly_xor


ZERO = Expr.zero()
ONE = Expr.one()
MAX_DEG = 17


def _var(name: str) -> Expr:
    return Expr.var(name)


def _const(value: Expr) -> Poly:
    return [value]


def _affine(*polys: Poly, scalar: Expr = ZERO) -> Poly:
    out: Poly = []
    for poly in polys:
        out = poly_xor(out, poly)
    if not scalar.is_zero():
        out = poly_xor(out, _const(scalar))
    return out


def _mul(left: Poly, right: Poly) -> Poly:
    return poly_mul(left, right, max_deg=MAX_DEG)


def _degree(poly: Poly) -> int:
    return len(poly) - 1


def _pow2(value: Expr, exponent: int) -> Expr:
    if exponent < 0 or exponent & (exponent - 1):
        raise ValueError("exponent must be a nonnegative power of two")
    out = value
    step = 1
    while step < exponent:
        out = out * out
        step *= 2
    return out


def _unequal_degree_offsets(
    lower: Poly,
    higher: Poly,
    q_higher: Expr,
    q_lower: Expr,
) -> tuple[Expr, Expr]:
    """Invert ``(lower+a)*(higher+b)`` from rows deg(higher), deg(lower)."""

    dl = _degree(lower)
    dh = _degree(higher)
    assert 0 < dl < dh
    assert poly_coeff(lower, dl) == ONE
    assert poly_coeff(higher, dh) == ONE

    baseline = _mul(lower, higher)
    a = q_higher ^ poly_coeff(baseline, dh)
    with_a = poly_xor(baseline, _mul(_const(a), higher))
    b = q_lower ^ poly_coeff(with_a, dl)
    return a, b


def _build_from_triangular_coordinates() -> tuple[Poly, dict[str, Expr], dict[str, Expr]]:
    # These names are the z-order in the claimed triangular decoder.
    names = (
        "Q1 Q2 S R Q0 E Q14 Q6 Q5 Q15 Q8 Q9 Q12 Q13 Q10 Q11 Q16"
    ).split()
    z = {name: _var(name) for name in names}

    # Invert the elementary coordinate change
    #   S=Q0+Q3, R=Q5+Q7, E=Q4+Q5^2+Q5.
    q: dict[int, Expr] = {
        0: z["Q0"],
        1: z["Q1"],
        2: z["Q2"],
        3: z["S"] ^ z["Q0"],
        5: z["Q5"],
        6: z["Q6"],
        7: z["R"] ^ z["Q5"],
        8: z["Q8"],
        9: z["Q9"],
        10: z["Q10"],
        11: z["Q11"],
        12: z["Q12"],
        13: z["Q13"],
        14: z["Q14"],
        15: z["Q15"],
        16: z["Q16"],
    }
    q[4] = z["E"] ^ (q[5] * q[5]) ^ q[5]

    x = [ZERO, ONE]

    # y=(x+0)(x+a0), with q0=[y]_1.
    a: dict[int, Expr] = {0: q[0]}
    y = _mul(x, _affine(x, scalar=a[0]))
    assert poly_coeff(y, 1) == q[0]

    # z=(x+a1)(x+y+a2), using q1=[z]_2 and q2=[z]_1.
    lower_z = x
    higher_z = _affine(x, y)
    a[1], a[2] = _unequal_degree_offsets(lower_z, higher_z, q[1], q[2])
    z_wire = _mul(
        _affine(lower_z, scalar=a[1]),
        _affine(higher_z, scalar=a[2]),
    )
    assert poly_coeff(z_wire, 2) == q[1]
    assert poly_coeff(z_wire, 1) == q[2]

    # t=(y+a3)(x+y+a4).  The two selected rows have the explicit unit solve
    # sigma=a3+a4=q3+q0^2+q0, a3=q4+q0*sigma.
    sigma = q[3] ^ (q[0] * q[0]) ^ q[0]
    a[3] = q[4] ^ (q[0] * sigma)
    a[4] = sigma ^ a[3]
    t = _mul(_affine(y, scalar=a[3]), _affine(x, y, scalar=a[4]))
    assert poly_coeff(t, 2) == q[3]
    assert poly_coeff(t, 1) == q[4]

    # u=(y+z+a5)(z+t+a6), degrees 3 and 4.
    lower_u = _affine(y, z_wire)
    higher_u = _affine(z_wire, t)
    a[5], a[6] = _unequal_degree_offsets(lower_u, higher_u, q[5], q[6])
    u = _mul(
        _affine(lower_u, scalar=a[5]),
        _affine(higher_u, scalar=a[6]),
    )
    assert poly_coeff(u, 4) == q[5]
    assert poly_coeff(u, 3) == q[6]

    # v=(x+z+a7)(x+z+t+u+a8), degrees 3 and 7.
    lower_v = _affine(x, z_wire)
    higher_v = _affine(x, z_wire, t, u)
    a[7], a[8] = _unequal_degree_offsets(lower_v, higher_v, q[7], q[8])
    v = _mul(
        _affine(lower_v, scalar=a[7]),
        _affine(higher_v, scalar=a[8]),
    )
    assert poly_coeff(v, 7) == q[7]
    assert poly_coeff(v, 3) == q[8]

    # h=(y+a9)x, with q9=[h]_1.
    a[9] = q[9]
    h = _mul(_affine(y, scalar=a[9]), x)
    assert poly_coeff(h, 1) == q[9]

    # j=(y+a10)(x+a11).  Feed the lower-degree factor first to the helper.
    a[11], a[10] = _unequal_degree_offsets(x, y, q[10], q[11])
    j = _mul(_affine(y, scalar=a[10]), _affine(x, scalar=a[11]))
    assert poly_coeff(j, 2) == q[10]
    assert poly_coeff(j, 1) == q[11]

    # ell=(t+a12)(h+a13), degrees 4 and 3.
    a[13], a[12] = _unequal_degree_offsets(h, t, q[12], q[13])
    ell = _mul(_affine(t, scalar=a[12]), _affine(h, scalar=a[13]))
    assert poly_coeff(ell, 4) == q[12]
    assert poly_coeff(ell, 3) == q[13]

    # w=(x+u+a14)(u+v+a15), degrees 7 and 10.
    lower_w = _affine(x, u)
    higher_w = _affine(u, v)
    a[14], a[15] = _unequal_degree_offsets(lower_w, higher_w, q[14], q[15])
    w = _mul(
        _affine(lower_w, scalar=a[14]),
        _affine(higher_w, scalar=a[15]),
    )
    assert poly_coeff(w, 10) == q[14]
    assert poly_coeff(w, 7) == q[15]

    a[16] = q[16]
    output = _affine(j, ell, w, scalar=a[16])
    assert _degree(output) == 17
    assert poly_coeff(output, 17) == ONE
    return output, z, {f"a{i}": a[i] for i in range(17)}


def main() -> None:
    output, z, _ = _build_from_triangular_coordinates()
    order = (
        "Q1 Q2 S R Q0 E Q14 Q6 Q5 Q15 Q8 Q9 Q12 Q13 Q10 Q11 Q16"
    ).split()
    degrees = [16, 15, 13, 14, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
    frobenius_exponents = [1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 1]

    earlier: set[str] = set()
    residual_sizes: list[int] = []
    assert len(order) == len(degrees) == len(frobenius_exponents)
    for name, degree, exponent in zip(order, degrees, frobenius_exponents):
        pivot = _pow2(z[name], exponent)
        residual = poly_coeff(output, degree) ^ pivot
        forbidden = residual.vars - earlier
        if forbidden:
            raise AssertionError(
                f"row {degree} is not triangular at {name}^{exponent}: "
                f"later/current variables {sorted(forbidden)} remain"
            )
        residual_sizes.append(len(residual.monos))
        earlier.add(name)

    print("OK: exact F2-polynomial triangular identities for the uniform (17, 9) circuit")
    print("K_i monomial counts:", ",".join(map(str, residual_sizes)))


if __name__ == "__main__":
    main()
