#!/usr/bin/env python3
from __future__ import annotations

"""Explicit decoder for the uniform characteristic-two degree-17 circuit.

The decoder follows the triangular coefficient table in
``verify_n17_uniform_symbolic.py``.  At each row, the known term is evaluated by
setting the current and all later normalized coordinates to zero; the residual is
either the new coordinate itself, its square, or its fourth power.  No search,
factorization, or field-dependent linear solve is used.
"""

import random
from typing import Sequence

from .gf2k import GF2k
from .poly_generic import Poly, poly_add_many, poly_add_scalar, poly_mul, poly_x


MAX_DEG = 17


def _add(*values: int) -> int:
    out = 0
    for value in values:
        out ^= int(value)
    return out


def _affine(*polys: Sequence[int], scalar: int = 0) -> Poly:
    out = poly_add_many(polys, max_deg=MAX_DEG)
    return poly_add_scalar(out, scalar, max_deg=MAX_DEG)


def _mul(left: Sequence[int], right: Sequence[int], *, F: GF2k) -> Poly:
    return poly_mul(left, right, max_deg=MAX_DEG, F=F)


def _scale(poly: Sequence[int], scalar: int, *, F: GF2k) -> Poly:
    if len(poly) != MAX_DEG + 1:
        raise ValueError("length mismatch")
    return [F.mul(int(value), int(scalar)) for value in poly]


def eval_n17(params: Sequence[int], *, F: GF2k) -> Poly:
    """Evaluate the fixed nine-product circuit, returning coefficients 0..17."""

    if len(params) != 17:
        raise ValueError("expected 17 keys")
    a = [int(value) & F.mask for value in params]
    x = poly_x(max_deg=MAX_DEG)

    y = _mul(x, _affine(x, scalar=a[0]), F=F)
    z = _mul(_affine(x, scalar=a[1]), _affine(x, y, scalar=a[2]), F=F)
    t = _mul(_affine(y, scalar=a[3]), _affine(x, y, scalar=a[4]), F=F)
    u = _mul(_affine(y, z, scalar=a[5]), _affine(z, t, scalar=a[6]), F=F)
    v = _mul(
        _affine(x, z, scalar=a[7]),
        _affine(x, z, t, u, scalar=a[8]),
        F=F,
    )
    h = _mul(_affine(y, scalar=a[9]), x, F=F)
    j = _mul(_affine(y, scalar=a[10]), _affine(x, scalar=a[11]), F=F)
    ell = _mul(_affine(t, scalar=a[12]), _affine(h, scalar=a[13]), F=F)
    w = _mul(
        _affine(x, u, scalar=a[14]),
        _affine(u, v, scalar=a[15]),
        F=F,
    )
    return _affine(j, ell, w, scalar=a[16])


def _unequal_degree_offsets(
    lower: Poly,
    higher: Poly,
    q_higher: int,
    q_lower: int,
    *,
    degree_lower: int,
    degree_higher: int,
    F: GF2k,
) -> tuple[int, int]:
    """Invert ``(lower+a)*(higher+b)`` from its two direct pivot rows."""

    baseline = _mul(lower, higher, F=F)
    a = q_higher ^ baseline[degree_higher]
    with_a = _affine(baseline, _scale(higher, a, F=F))
    b = q_lower ^ with_a[degree_lower]
    return a, b


def keys_from_normalized(zc: Sequence[int], *, F: GF2k) -> list[int]:
    """Invert the normalized coordinates used by the coefficient decoder."""

    if len(zc) != 17:
        raise ValueError("expected 17 normalized coordinates")
    (
        q1,
        q2,
        ss,
        rr,
        q0,
        ee,
        q14,
        q6,
        q5,
        q15,
        q8,
        q9,
        q12,
        q13,
        q10,
        q11,
        q16,
    ) = [int(value) & F.mask for value in zc]
    q3 = ss ^ q0
    q4 = _add(ee, F.sq(q5), q5)
    q7 = rr ^ q5

    x = poly_x(max_deg=MAX_DEG)
    a = [0] * 17
    a[0] = q0
    y = _mul(x, _affine(x, scalar=a[0]), F=F)

    a[1], a[2] = _unequal_degree_offsets(
        x,
        _affine(x, y),
        q1,
        q2,
        degree_lower=1,
        degree_higher=2,
        F=F,
    )
    zw = _mul(_affine(x, scalar=a[1]), _affine(x, y, scalar=a[2]), F=F)

    sigma = _add(q3, F.sq(q0), q0)
    a[3] = q4 ^ F.mul(q0, sigma)
    a[4] = sigma ^ a[3]
    t = _mul(_affine(y, scalar=a[3]), _affine(x, y, scalar=a[4]), F=F)

    a[5], a[6] = _unequal_degree_offsets(
        _affine(y, zw),
        _affine(zw, t),
        q5,
        q6,
        degree_lower=3,
        degree_higher=4,
        F=F,
    )
    u = _mul(_affine(y, zw, scalar=a[5]), _affine(zw, t, scalar=a[6]), F=F)

    a[7], a[8] = _unequal_degree_offsets(
        _affine(x, zw),
        _affine(x, zw, t, u),
        q7,
        q8,
        degree_lower=3,
        degree_higher=7,
        F=F,
    )
    v = _mul(
        _affine(x, zw, scalar=a[7]),
        _affine(x, zw, t, u, scalar=a[8]),
        F=F,
    )

    a[9] = q9
    h = _mul(_affine(y, scalar=a[9]), x, F=F)

    a[11], a[10] = _unequal_degree_offsets(
        x,
        y,
        q10,
        q11,
        degree_lower=1,
        degree_higher=2,
        F=F,
    )

    a[13], a[12] = _unequal_degree_offsets(
        h,
        t,
        q12,
        q13,
        degree_lower=3,
        degree_higher=4,
        F=F,
    )

    a[14], a[15] = _unequal_degree_offsets(
        _affine(x, u),
        _affine(u, v),
        q14,
        q15,
        degree_lower=7,
        degree_higher=10,
        F=F,
    )
    a[16] = q16
    return a


def eval_from_normalized(zc: Sequence[int], *, F: GF2k) -> Poly:
    return eval_n17(keys_from_normalized(zc, F=F), F=F)


def decode_n17_coeffs(coeffs: Sequence[int], *, F: GF2k) -> list[int]:
    """Recover all keys from c0,...,c16 of an arbitrary monic degree-17 polynomial."""

    if len(coeffs) != 17:
        raise ValueError("expected c0,...,c16")
    c = [int(value) & F.mask for value in coeffs]
    degrees = [16, 15, 13, 14, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]
    root_depths = [0, 0, 1, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0]

    normalized = [0] * 17
    for index, (degree, root_depth) in enumerate(zip(degrees, root_depths)):
        baseline = eval_from_normalized(normalized, F=F)
        residual = c[degree] ^ baseline[degree]
        normalized[index] = F.root_pow2(residual, root_depth % F.k)
    return keys_from_normalized(normalized, F=F)


def _roundtrip_field(F: GF2k, *, trials: int, rng: random.Random) -> None:
    for _ in range(trials):
        keys = [rng.randrange(1 << F.k) for _ in range(17)]
        poly = eval_n17(keys, F=F)
        if poly[17] != 1:
            raise AssertionError("circuit output is not monic of degree 17")
        decoded = decode_n17_coeffs(poly[:17], F=F)
        if decoded != keys:
            raise AssertionError(
                f"key roundtrip failed over GF(2^{F.k}):\n"
                f"  keys={keys}\n  decoded={decoded}\n  coeffs={poly}"
            )

    for _ in range(max(1, trials // 4)):
        coefficients = [rng.randrange(1 << F.k) for _ in range(17)]
        decoded = decode_n17_coeffs(coefficients, F=F)
        poly = eval_n17(decoded, F=F)
        if poly[:17] != coefficients or poly[17] != 1:
            raise AssertionError(
                f"coefficient roundtrip failed over GF(2^{F.k}):\n"
                f"  coeffs={coefficients}\n  decoded={decoded}\n  output={poly}"
            )


def main() -> None:
    fields = [
        GF2k(1, 0b11),
        GF2k(2, 0b111),
        GF2k(3, 0b1011),
        GF2k(4, 0b10011),
        GF2k(5, 0b100101),
        GF2k(8, 0x11B),
    ]
    rng = random.Random(0x179C0DEC)
    for field in fields:
        _roundtrip_field(field, trials=250, rng=rng)
    print(
        "OK: explicit uniform degree-17 decoder over "
        "GF(2), GF(4), GF(8), GF(16), GF(32), and GF(256)"
    )


if __name__ == "__main__":
    main()
