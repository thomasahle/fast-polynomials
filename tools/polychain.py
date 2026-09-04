#!/usr/bin/env python3
"""
polychain.py — polynomial chains for the paper's decodable family P_n[α].

This is the user-facing companion tool for "Fast Evaluation of Polynomials
with Rational Preprocessing".  It provides, for the degree-n monic family
P_n[α_0..α_{n-1}] (sections/constructions.tex, Algorithm `alg:final-construction`):

  * ``chain(n)``        — the straight-line program ("polynomial chain") with
                          ⌊n/2⌋+1 multiplications, with the parameters kept
                          symbolic, renderable as text / LaTeX / JSON in the
                          style of sections/appendix_polynomials.tex;
  * ``encode(n, α, F)`` — expansion of P_n[α] to coefficients c_0..c_{n-1}
                          (of the monic polynomial x^n + Σ c_j x^j);
  * ``decode(n, c, F)`` — the paper's preprocessing: parameters α such that
                          P_n[α] = x^n + Σ c_j x^j, verified by re-expansion.

Decoding follows the structural recursion of the paper's final decoder
(`alg:final-decoder`): the even lift, the P_3/P_5/P_7 bases, the special
cases 15/27/31, the 4k+1 family (five outer pivots + `alg:decode-Rk2l`),
and the 8k+3 / 8k+7 induction steps (square gadgets, `lem:square-gadget`).
Sub-gadget parameter blocks (Q_{2^t-1}, Q_{4k+1}, odd-degree Q's, and the
bar-Q's) are extracted with the generic descending-affine-pivot primitive
`poly_schedule._decode_by_descending_pivots`, which realizes the paper's
unitriangular pivot lemmas (`lem:Q-unitriangular` etc.) numerically.

Fields: GF(p) for an odd prime p (default the Mersenne prime 2^61-1) and
exact rationals (`fractions.Fraction`).  Characteristic 2 is not supported
here (see `poly_schedule`'s char-2 septic base for that special case).

CLI:
  python3 tools/polychain.py chain 15 [--latex|--json]
  python3 tools/polychain.py encode 15 --alphas a0,...,a14 [--prime P|--rational]
  python3 tools/polychain.py decode 15 --coeffs c0,...,c14 [--prime P|--rational]
  python3 tools/polychain.py selftest [--max-n 120]
"""

from __future__ import annotations

import argparse
import dataclasses
import functools
import json
import random
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Optional, Sequence, Tuple, Union

_REPO_ROOT = Path(__file__).resolve().parents[1]
if str(_REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(_REPO_ROOT))

import tools.poly_schedule as ps  # noqa: E402

Number = ps.Number
Poly = List[Number]
Field = ps.Field

MERSENNE61 = (1 << 61) - 1


# =============================================================================
# Fields
# =============================================================================


def GF(p: int) -> Field:
    """The prime field GF(p) (odd p; characteristic 2 is rejected at decode time)."""

    return ps.Field(modulus=p)


def rationals() -> Field:
    """Exact rational arithmetic (`fractions.Fraction`)."""

    return ps.Field(modulus=None, use_fractions=True)


def default_field() -> Field:
    return GF(MERSENNE61)


def _require_odd_characteristic(field: Field, purpose: str) -> None:
    if field.modulus == 2:
        raise NotImplementedError(
            f"{purpose} over characteristic 2 is not supported by polychain; "
            "see poly_schedule's char-2 septic base for the GF(2^k) constructions"
        )


# =============================================================================
# Encoding (coefficient expansion of P_n[α])
# =============================================================================


def encode(n: int, alphas: Sequence[Number], field: Optional[Field] = None,
           *, peeled: bool = False) -> List[Number]:
    """
    Expand P_n[α_0..α_{n-1}] and return its non-leading coefficients
    [c_0, ..., c_{n-1}]  (the polynomial is x^n + Σ_j c_j x^j).

    With ``peeled=True`` the known-powers gadgets Q_{2^k-1} use the
    depth-balanced peeled recursion (same multiplications and additions,
    height O(log n) overall); the parameter layout inside those blocks
    changes accordingly.
    """

    field = field or default_field()
    if peeled:
        return _with_peeled(lambda: encode(n, alphas, field))
    if n < 1:
        raise ValueError("encode requires n >= 1")
    alphas = [field.coerce(a) for a in alphas]
    if len(alphas) != n:
        raise ValueError(f"P_{n} takes exactly {n} parameters, got {len(alphas)}")
    P = ps._poly_paper_P_from_params(params=alphas, field=field)
    P = ps._poly_trim(P, field)
    if ps._poly_degree(P) != n or P[-1] != field.one():
        raise RuntimeError("internal error: encoder did not produce a monic degree-n polynomial")
    return list(P[:n])


# =============================================================================
# Decoding (rational preprocessing: coefficients -> parameters)
# =============================================================================


def decode(n: int, coeffs: Sequence[Number], field: Optional[Field] = None,
           *, peeled: bool = False) -> List[Number]:
    """
    Invert `encode`: given the coefficients c_0..c_{n-1} of the monic
    polynomial x^n + Σ_j c_j x^j, return parameters α_0..α_{n-1} with
    P_n[α] equal to that polynomial.  The result is verified by re-expansion.

    Mirrors `alg:final-decoder` in sections/constructions.tex.
    """

    field = field or default_field()
    if peeled:
        return _with_peeled(lambda: decode(n, coeffs, field))
    _require_odd_characteristic(field, "decoding")
    if n < 1:
        raise ValueError("decode requires n >= 1")
    cs = [field.coerce(c) for c in coeffs]
    if len(cs) == n + 1:
        if cs[-1] != field.one():
            raise ValueError("decode expects a monic polynomial (leading coefficient 1)")
        cs = cs[:n]
    if len(cs) != n:
        raise ValueError(f"decode of degree {n} needs {n} coefficients c_0..c_{n-1}, got {len(cs)}")
    full: Poly = cs + [field.one()]

    alphas = _decode_monic(full, field)

    check = ps._poly_trim(ps._poly_paper_P_from_params(params=alphas, field=field), field)
    if check != ps._poly_trim(full, field):
        raise RuntimeError(f"decode(n={n}): parameters failed re-expansion verification")
    return alphas


def _decode_monic(coeffs: Poly, field: Field) -> List[Number]:
    """Even lift P_n = α_0 + x·P_{n-1}, then odd-degree dispatch."""

    coeffs = ps._poly_trim(coeffs, field)
    n = ps._poly_degree(coeffs)
    if n < 1:
        raise ValueError("polynomial must have positive degree")
    if coeffs[-1] != field.one():
        raise ValueError("decode expects a monic polynomial")
    if n % 2 == 0:
        return [coeffs[0]] + _decode_monic(coeffs[1:], field)
    return _decode_odd(coeffs, field, pair_context=False)


def _decode_odd(coeffs: Poly, field: Field, *, pair_context: bool) -> List[Number]:
    """
    Decode odd-degree P_n = x·T^{(1)}_n + T^{(2)}_n.

    ``pair_context`` selects the splittable-pair parameterization for n=5
    (used as the inner block of the 8k+7 step), which differs from the
    top-level P_5 base construction.  n=7 never occurs as an inner block
    (k=3 instances are the special cases 27 and 31).
    """

    coeffs = ps._poly_trim(coeffs, field)
    n = ps._poly_degree(coeffs)
    if n == 1:
        return [coeffs[0]]
    if pair_context and n == 5:
        # Splittable pair for 5 = k=1 instance of the 4k+1 family.
        def enc5(a: List[Number]) -> Poly:
            T1, T2, _ = ps._poly_paper_splittable_pair(n=5, alpha=list(a), field=field)
            return ps._poly_add(ps._poly_shift_xk(T1, 1, field), T2, field)

        return ps._decode_by_descending_pivots(
            target=coeffs, encode_fn=enc5, nparams=5, field=field, what="pair(5)"
        )
    if pair_context and n == 7:
        raise RuntimeError("internal error: no splittable pair exists for 7")
    if n in (3, 5, 7, 11, 15) or (n % 4) == 1:
        # Bases, the 4k+1 family (lem:4k+1-splittable + alg:decode-Rk2l),
        # and the specials 11/15 — all implemented in poly_schedule.
        return ps._decode_P_coeffs_to_paper_params(coeffs, field)
    if n == 27:
        return _decode_pair_27(coeffs, field)
    if n == 31:
        return _decode_pair_31(coeffs, field)
    if (n % 8) == 3:
        return _decode_pair_8k3(coeffs, field)
    if (n % 8) == 7:
        return _decode_pair_8k7(coeffs, field)
    raise RuntimeError(f"internal error: no decoding family matched odd n={n}")


# ---------------------------------------------------------------------------
# Shared helpers
# ---------------------------------------------------------------------------


def _x(field: Field) -> Poly:
    return [field.zero(), field.one()]


def _square_gadget_poly(S: Poly, delta: Number, field: Field) -> Poly:
    """x·S^2 + (S+δ)^2 (the square gadget of `lem:square-gadget`)."""

    S_sq = ps._poly_square(S, field)
    shifted = ps._poly_square(ps._poly_add_const(S, delta, field), field)
    return ps._poly_add(ps._poly_shift_xk(S_sq, 1, field), shifted, field)


def _shift_down(p: Poly, field: Field) -> Poly:
    """Divide by x, requiring a zero constant term is NOT required (drop it)."""

    return ps._poly_trim(list(p[1:]), field)


def _build_Q_encoder(deg: int, Hs_in: List[Poly], field: Field):
    """
    Mirror of the encoder's `build_Q` in `_poly_paper_splittable_pair` (8k+7
    branch): the odd-degree known-powers gadget when enough powers are
    available, the bar-Q fallback otherwise.  Returns (encode_fn, hs_out_fn).
    """

    l = ps._v2_positive(deg + 1)
    odd = (deg + 1) >> l
    kk = (odd - 1) // 2
    need = l + 1 if kk > 0 else l
    if len(Hs_in) >= need:
        def enc(a: List[Number]) -> Poly:
            q, _hs, _t = ps._poly_paper_Q_for_odd_degree_with_powers(
                deg=deg, alpha=list(a), Hs=Hs_in, field=field
            )
            return ps._poly_trim(q, field)

        def hs_out(a: List[Number]) -> List[Poly]:
            _q, hs, _t = ps._poly_paper_Q_for_odd_degree_with_powers(
                deg=deg, alpha=list(a), Hs=Hs_in, field=field
            )
            return list(hs)
    else:
        def enc(a: List[Number]) -> Poly:
            q, _hs = ps._poly_paper_barQ_odd_with_H2_H4_with_powers(
                deg=deg, alpha=list(a), Hs_in=Hs_in, field=field
            )
            return ps._poly_trim(q, field)

        def hs_out(a: List[Number]) -> List[Poly]:
            _q, hs = ps._poly_paper_barQ_odd_with_H2_H4_with_powers(
                deg=deg, alpha=list(a), Hs_in=Hs_in, field=field
            )
            return list(hs)
    return enc, hs_out


def _solve_Q4kp1(target: Poly, kk: int, H2: Poly, field: Field) -> List[Number]:
    """Parameter block of Q_{4k+1}(x, H_2) (lem:Q4k+1-from-H2) by descending pivots."""

    x = _x(field)

    def enc(av: List[Number]) -> Poly:
        q, _hs, _t = ps._poly_paper_Q_2lp1k_minus_1_with_powers(
            k=kk, l=1, alpha=list(av), Hs=[x, H2], field=field
        )
        return ps._poly_trim(q, field)

    return ps._decode_by_descending_pivots(
        target=target, encode_fn=enc, nparams=4 * kk + 1, field=field, what=f"Q_{{{4 * kk + 1}}} given H2"
    )


def _Q4kp1_powers(params: List[Number], kk: int, H2: Poly, field: Field) -> List[Poly]:
    """Known-power byproducts [x, H_2, H_4, ...] of a Q_{4k+1}(x,H_2) instance."""

    x = _x(field)
    _q, hs_raw, _t = ps._poly_paper_Q_2lp1k_minus_1_with_powers(
        k=kk, l=1, alpha=list(params), Hs=[x, H2], field=field
    )
    return [x, H2] + list(hs_raw[2:])


def _solve_Qodd(target: Poly, deg: int, Hs: List[Poly], field: Field) -> List[Number]:
    """Parameter block of the odd-degree known-powers gadget Q_deg (lem:Q-odd-degree-with-powers)."""

    def enc(av: List[Number]) -> Poly:
        q, _hs, _t = ps._poly_paper_Q_for_odd_degree_with_powers(deg=deg, alpha=list(av), Hs=Hs, field=field)
        return ps._poly_trim(q, field)

    return ps._decode_by_descending_pivots(
        target=target, encode_fn=enc, nparams=deg, field=field, what=f"Q_{{{deg}}} with powers"
    )


def _h4_block_params(H4: Poly, field: Field) -> List[Number]:
    """[α_4, α_5, α_6, α_7] from H_4 = H_2² − (x+α_5)² + α_4, H_2 = x² + α_7 x + α_6."""

    one = field.one()

    def enc(a: List[Number]) -> Poly:
        H2 = [a[2], a[3], one]
        return ps._poly_add_const(
            ps._poly_sub(ps._poly_square(H2, field), ps._poly_square([a[1], one], field), field),
            a[0],
            field,
        )

    return ps._decode_by_descending_pivots(target=H4, encode_fn=enc, nparams=4, field=field, what="H4 block")


def _decode_27_low_block(P3: Poly, field: Field) -> List[Number]:
    """
    Closed-form chain for P3 = −(x+1)·Q_3² + (x+1)·α_1 − H_2² + α_0 with
    Q_3 = x³+γ₂x²+γ₁x+γ₀ = Q_3[α_4,α_5,α_6](x,H_2) and H_2 = x²+bx+c
    (b = α_3, c = α_2).  Returns [α_0, ..., α_6].
    """

    one = field.one()
    inv2 = field.inv(field.add(one, one))
    c_ = lambda j: ps._poly_coeff(P3, j, field)  # noqa: E731
    mul, add, sub, neg = field.mul, field.add, field.sub, field.neg

    def dbl(v: Number) -> Number:
        return add(v, v)

    g2 = mul(sub(neg(c_(6)), one), inv2)                       # P3_6 = −(2γ₂ + 1)
    q5 = dbl(g2)                                               # [x^5]Q_3²
    g1 = mul(sub(sub(neg(c_(5)), mul(g2, g2)), q5), inv2)      # P3_5 = −(γ₂²+2γ₁ + q5)
    q4 = add(mul(g2, g2), dbl(g1))
    g0 = mul(sub(sub(sub(neg(c_(4)), one), dbl(mul(g2, g1))), q4), inv2)  # P3_4 = −(2γ₀+2γ₂γ₁ + q4) − 1
    q3 = add(dbl(g0), dbl(mul(g2, g1)))
    q2 = add(mul(g1, g1), dbl(mul(g2, g0)))
    b = mul(sub(sub(neg(c_(3)), q2), q3), inv2)                # P3_3 = −(q2+q3) − 2b
    q1 = dbl(mul(g1, g0))
    c = mul(sub(sub(sub(neg(c_(2)), q1), q2), mul(b, b)), inv2)  # P3_2 = −(q1+q2) − (b²+2c)
    q0 = mul(g0, g0)
    alpha1 = add(add(add(c_(1), q0), q1), dbl(mul(b, c)))      # P3_1 = −(q0+q1) + α_1 − 2bc
    alpha0 = add(sub(add(c_(0), q0), alpha1), mul(c, c))       # P3_0 = −q0 + α_1 + α_0 − c²

    alpha6 = sub(g2, b)                                        # γ₂ = b + α_6
    alpha5 = sub(sub(g1, c), mul(alpha6, b))                   # γ₁ = c + α_5 + α_6 b
    alpha4 = sub(g0, mul(alpha6, add(c, alpha5)))              # γ₀ = α_6 (c + α_5) + α_4
    return [alpha0, alpha1, c, b, alpha4, alpha5, alpha6]


# ---------------------------------------------------------------------------
# Inner pair from its squares: Ψ = x·T1² + T2²  (lem:compatible-power)
# ---------------------------------------------------------------------------
#
# The 8k+3 step exposes the inner splittable pair (T1, T2) only through
# Ψ = x·T1² + T2² on the degrees >= deg T1.  The paper recovers the pair via
# the square-closure certificate; numerically we solve the map vals -> Ψ by
# descending affine pivots after *re-parameterizing* the pair: every
# Q-sub-block is replaced by its free polynomial coefficients (the known-powers
# Q maps are coefficient-bijective by lem:Q-unitriangular), recursively through
# the family tree.  In these coordinates each unknown first appears affinely
# with a constant slope, so `_decode_by_descending_pivots` applies; the actual
# parameter blocks are then extracted from the recovered sub-polynomials by the
# same Q-decoders the top-level families use.


def _pairsq_psi(T1: Poly, T2: Poly, field: Field) -> Poly:
    return ps._poly_add(ps._poly_shift_xk(ps._poly_square(T1, field), 1, field), ps._poly_square(T2, field), field)


def _pair_free(m: int, field: Field):
    """
    Free-coordinate parameterization of the splittable pair for odd m.

    Returns (nvals, build, extract) with build(vals) -> (T1, T2) and
    extract(vals) -> the paper parameter block α' (extract runs the
    appropriate Q-block decoders on the recovered free polynomials).
    """

    one = field.one()
    sq = lambda p: ps._poly_square(p, field)  # noqa: E731
    add = lambda p, q: ps._poly_add(p, q, field)  # noqa: E731
    sub = lambda p, q: ps._poly_sub(p, q, field)  # noqa: E731
    addc = lambda p, c: ps._poly_add_const(p, c, field)  # noqa: E731

    if m <= 5 or (m % 4) == 1:
        # The T-tower families are descending-triangular in their own
        # parameters (cf. the pivot tables of lem:4k+1-splittable / lem:Rk2l).
        def build(vals: List[Number]):
            T1, T2, _ = ps._poly_paper_splittable_pair(n=m, alpha=list(vals), field=field)
            return T1, T2

        return m, build, (lambda vals: list(vals))

    if m == 15:
        # [α0..α7 | S free(7)] with S = Q7(x,H2,H4).
        def build(vals: List[Number]):
            a8 = vals[:8]
            S = list(vals[8:15]) + [one]
            H2 = [a8[6], a8[7], one]
            H4 = addc(sub(sq(H2), sq([a8[5], one])), a8[4])
            T1 = addc(sub(sq(S), sq(addc(H2, a8[3]))), a8[1])
            T2 = addc(add(T1, sub(sq(H4), sq(addc(H2, a8[2])))), a8[0])
            return T1, T2

        def extract(vals: List[Number]) -> List[Number]:
            H2 = [vals[6], vals[7], one]
            H4 = addc(sub(sq(H2), sq([vals[5], one])), vals[4])
            S = ps._poly_trim(list(vals[8:15]) + [one], field)
            q7 = ps._decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S, k=3, Hs=[_x(field), H2, H4], field=field)
            return list(vals[:8]) + list(q7)

        return 15, build, extract

    if m == 27:
        # [α0, α1, α2, α3 | Q3 free(3) | S3 free(7) | S1 free(13)].
        def build(vals: List[Number]):
            H2 = [vals[2], vals[3], one]
            q3 = list(vals[4:7]) + [one]
            S3 = list(vals[7:14]) + [one]
            S1 = list(vals[14:27]) + [one]
            T1 = addc(sub(sq(S1), sq(q3)), vals[1])
            T2 = add(T1, addc(sub(sq(S3), sq(H2)), vals[0]))
            return T1, T2

        def extract(vals: List[Number]) -> List[Number]:
            H2 = [vals[2], vals[3], one]
            q3poly = ps._poly_trim(list(vals[4:7]) + [one], field)
            S3poly = ps._poly_trim(list(vals[7:14]) + [one], field)
            S1poly = ps._poly_trim(list(vals[14:27]) + [one], field)
            q3block = ps._decode_Q3_coeffs_to_alpha_given_H2(q3poly, H2, field)
            q13 = _solve_Q4kp1(S1poly, 3, H2, field)
            H4 = _Q4kp1_powers(q13, 3, H2, field)[2]
            q7 = ps._decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S3poly, k=3, Hs=[_x(field), H2, H4], field=field)
            return [vals[0], vals[1], vals[2], vals[3]] + list(q3block) + list(q7) + list(q13)

        return 27, build, extract

    if m == 31:
        # [α0 | Q3 free(3) | H4 free(4) | S2 free(7) | α15 | S1 free(15)].
        def build(vals: List[Number]):
            S3q = list(vals[1:4]) + [one]
            H4 = list(vals[4:8]) + [one]
            S2 = list(vals[8:15]) + [one]
            a15 = vals[15]
            S1 = list(vals[16:31]) + [one]
            T1 = add(sub(sq(S1), sq(S2)), S3q)
            T2 = addc(sub(sq(addc(S1, a15)), sq(H4)), vals[0])
            return T1, T2

        def extract(vals: List[Number]) -> List[Number]:
            S3q = ps._poly_trim(list(vals[1:4]) + [one], field)
            H4 = ps._poly_trim(list(vals[4:8]) + [one], field)
            S2 = ps._poly_trim(list(vals[8:15]) + [one], field)
            S1 = ps._poly_trim(list(vals[16:31]) + [one], field)
            a47 = _h4_block_params(H4, field)
            H2 = [a47[2], a47[3], one]
            q3 = ps._decode_Q3_coeffs_to_alpha_given_H2(S3q, H2, field)
            q7 = ps._decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S2, k=3, Hs=[_x(field), H2, H4], field=field)

            def enc_bar(a: List[Number]) -> Poly:
                return ps._poly_trim(ps._poly_paper_barQ_15(alpha=list(a), H2=H2, H4=H4, field=field), field)

            bar = ps._decode_by_descending_pivots(
                target=S1, encode_fn=enc_bar, nparams=15, field=field, what="barQ15 given (H2,H4)"
            )
            return [vals[0]] + list(q3) + list(a47) + list(q7) + [vals[15]] + list(bar)

        return 31, build, extract

    if (m % 8) == 3:
        kk = (m - 3) // 8
        inner_len = 2 * kk + 1
        n_inner, build_inner, extract_inner = _pair_free(inner_len, field)
        s3_free = 1 if kk == 1 else 2 * kk - 1
        s2_free = 4 * kk + 1
        # [α0 | S3 free | inner | a | S2 free].
        nvals = 1 + s3_free + n_inner + 1 + s2_free

        def build(vals: List[Number]):
            alpha0 = vals[0]
            S3 = list(vals[1 : 1 + s3_free]) + ([] if kk == 1 else [one])
            S1_1, S1_2 = build_inner(vals[1 + s3_free : 1 + s3_free + n_inner])
            a = vals[1 + s3_free + n_inner]
            S2 = list(vals[-s2_free:]) + [one]
            T1 = add(sub(sq(S2), sq(S1_1)), S3)
            T2 = addc(sub(sq(addc(S2, a)), sq(S1_2)), alpha0)
            return T1, T2

        def extract(vals: List[Number]) -> List[Number]:
            alpha0 = vals[0]
            inner = extract_inner(vals[1 + s3_free : 1 + s3_free + n_inner])
            a = vals[1 + s3_free + n_inner]
            _t1, _t2, Hs = ps._poly_paper_splittable_pair(n=inner_len, alpha=inner, field=field)
            H2 = Hs[1]
            S2poly = ps._poly_trim(list(vals[-s2_free:]) + [one], field)
            S2block = _solve_Q4kp1(S2poly, kk, H2, field)
            if kk == 1:
                S3block = [vals[1]]
            else:
                S3poly = ps._poly_trim(list(vals[1 : 1 + s3_free]) + [one], field)
                Hs2 = _Q4kp1_powers(S2block, kk, H2, field)
                S3block = _solve_Qodd(S3poly, 2 * kk - 1, Hs2, field)
            return [alpha0] + list(S3block) + list(inner) + [a] + list(S2block)

        return nvals, build, extract

    if (m % 8) == 7:
        kk = (m - 7) // 8
        inner_len = 2 * kk + 1
        n_inner, build_inner, extract_inner = _pair_free(inner_len, field)
        s2_free = 2 * kk + 1
        s3_free = 4 * kk + 3
        # [inner | a | S2 free | b | S3 free].
        nvals = n_inner + 1 + s2_free + 1 + s3_free

        def build(vals: List[Number]):
            S1_1, S1_2 = build_inner(vals[:n_inner])
            a = vals[n_inner]
            S2 = list(vals[n_inner + 1 : n_inner + 1 + s2_free]) + [one]
            b = vals[n_inner + 1 + s2_free]
            S3 = list(vals[-s3_free:]) + [one]
            T1 = add(sub(sq(S3), sq(S2)), S1_1)
            T2 = add(sub(sq(addc(S3, b)), sq(addc(S2, a))), S1_2)
            return T1, T2

        def extract(vals: List[Number]) -> List[Number]:
            inner = extract_inner(vals[:n_inner])
            a = vals[n_inner]
            S2poly = ps._poly_trim(list(vals[n_inner + 1 : n_inner + 1 + s2_free]) + [one], field)
            b = vals[n_inner + 1 + s2_free]
            S3poly = ps._poly_trim(list(vals[-s3_free:]) + [one], field)
            _t1, _t2, Hs = ps._poly_paper_splittable_pair(n=inner_len, alpha=inner, field=field)
            enc2, hs2 = _build_Q_encoder(2 * kk + 1, Hs, field)
            S2block = ps._decode_by_descending_pivots(
                target=S2poly, encode_fn=enc2, nparams=2 * kk + 1, field=field, what="Q_{2k+1}"
            )
            Hs = hs2(S2block)
            enc3, _hs3 = _build_Q_encoder(4 * kk + 3, Hs, field)
            S3block = ps._decode_by_descending_pivots(
                target=S3poly, encode_fn=enc3, nparams=4 * kk + 3, field=field, what="Q_{4k+3}"
            )
            return list(inner) + [a] + list(S2block) + [b] + list(S3block)

        return nvals, build, extract

    raise RuntimeError(f"internal error: no pair parameterization for m={m}")


def _decode_pairsq(m: int, psi: Poly, field: Field) -> List[Number]:
    """
    Parameter block α' of the inner splittable pair for odd m from
    Ψ = x·T1(α')² + T2(α')² known in degrees >= m−1 (lem:compatible-power).
    """

    n = m - 1
    nvals, build, extract = _pair_free(m, field)

    def enc(vals: List[Number]) -> Poly:
        T1, T2 = build(vals)
        return _pairsq_psi(T1, T2, field)

    vals = ps._decode_by_descending_pivots(
        target=psi, encode_fn=enc, nparams=nvals, field=field, rows=range(n, 2 * n + 2),
        what=f"pair-squares (m={m})",
    )
    alpha = extract(vals)

    T1, T2, _ = ps._poly_paper_splittable_pair(n=m, alpha=alpha, field=field)
    chk = _pairsq_psi(T1, T2, field)
    for w in range(n, 2 * n + 2):
        if ps._poly_coeff(chk, w, field) != ps._poly_coeff(psi, w, field):
            raise ValueError(f"pair-squares (m={m}): decoded block failed verification at degree {w}")
    return alpha


# ---------------------------------------------------------------------------
# The 8k+3 induction step (lem:8k+3-splittable)
# ---------------------------------------------------------------------------


def _decode_pair_8k3(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode P_{8k+3} = x·S_2² + (S_2+a)² − x·S1_1² − S1_2² + x·S_3 + α_0
    following the proof of `lem:8k+3-splittable`:

      1. square gadget at degree 4k+1 recovers (S_2, a); boundary error −1;
      2. the window ≥ 2k of Ψ = x·S1_1² + S1_2² recovers the inner
         splittable-pair block for 2k+1 (descending pivots — the numerical
         realization of the compatibility/square-closure certificate);
      3. the residual x·S_3 + α_0 gives α_0 and the S_3 = Q_{2k-1} block;
      4. S_2 = Q_{4k+1}(x, H_2) is decoded given the recovered H_2.
    """

    n = ps._poly_degree(coeffs)
    k = (n - 3) // 8
    m = 2 * k + 1
    one = field.one()
    x = _x(field)

    # 1. Outer square gadget; the error term −x·S1_1² contributes −1 at degree 4k+1.
    S2poly, a = ps._decode_square_gadget(
        G=coeffs, field=field, boundary_error_coeff_deg_d=field.neg(one)
    )
    P1 = ps._poly_sub(coeffs, _square_gadget_poly(S2poly, a, field), field)

    # 2. Ψ = x·S1_1² + S1_2² on the window ≥ 2k (boundary at 2k corrected by
    #    the known top coefficient of x·S_3: 1 for k>1, 0 for k=1).
    psi: Poly = [field.zero()] * (2 * m)
    for d in range(2 * k + 1, 4 * k + 2):
        psi[d] = field.neg(ps._poly_coeff(P1, d, field))
    s3_top = one if k > 1 else field.zero()
    psi[2 * k] = field.sub(s3_top, ps._poly_coeff(P1, 2 * k, field))

    inner = _decode_pairsq(m, psi, field)
    T1i, T2i, Hs = ps._poly_paper_splittable_pair(n=m, alpha=inner, field=field)
    H2 = Hs[1]

    # 3. Residual x·S_3 + α_0.
    psi_full = ps._poly_add(
        ps._poly_shift_xk(ps._poly_square(T1i, field), 1, field),
        ps._poly_square(T2i, field),
        field,
    )
    low = ps._poly_add(P1, psi_full, field)
    alpha0 = ps._poly_coeff(low, 0, field)
    S3poly = _shift_down(low, field)

    # 4. Sub-gadget parameter blocks.
    def enc_S2(av: List[Number]) -> Poly:
        q, _hs, _t = ps._poly_paper_Q_2lp1k_minus_1_with_powers(
            k=k, l=1, alpha=list(av), Hs=[x, H2], field=field
        )
        return ps._poly_trim(q, field)

    S2block = ps._decode_by_descending_pivots(
        target=S2poly, encode_fn=enc_S2, nparams=4 * k + 1, field=field, what="Q_{4k+1} given H2"
    )

    if k == 1:
        if ps._poly_degree(S3poly) > 0:
            raise ValueError("8k+3 decode: expected scalar S_3 for k=1")
        S3block = [ps._poly_coeff(S3poly, 0, field)]
    else:
        _q, hs2_raw, _t = ps._poly_paper_Q_2lp1k_minus_1_with_powers(
            k=k, l=1, alpha=S2block, Hs=[x, H2], field=field
        )
        Hs2 = [x, H2] + list(hs2_raw[2:])

        def enc_S3(av: List[Number]) -> Poly:
            q, _hs, _t = ps._poly_paper_Q_for_odd_degree_with_powers(
                deg=2 * k - 1, alpha=list(av), Hs=Hs2, field=field
            )
            return ps._poly_trim(q, field)

        S3block = ps._decode_by_descending_pivots(
            target=S3poly, encode_fn=enc_S3, nparams=2 * k - 1, field=field, what="Q_{2k-1}"
        )

    alpha = [alpha0] + list(S3block) + list(inner) + [a] + list(S2block)
    if len(alpha) != n:
        raise RuntimeError("internal error: 8k+3 parameter count mismatch")
    return alpha


# ---------------------------------------------------------------------------
# The 8k+7 induction step (lem:8k+7-splittable)
# ---------------------------------------------------------------------------


def _decode_pair_8k7(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode P_{8k+7} = x·S_3² + (S_3+b)² − x·S_2² − (S_2+a)² + P_{2k+1}
    following the proof of `lem:8k+7-splittable`: two nested square gadgets,
    then recursion on P_{2k+1}, then the Q blocks for S_2 and S_3.
    """

    n = ps._poly_degree(coeffs)
    k = (n - 7) // 8
    if k < 2:
        raise RuntimeError("internal error: 8k+7 decoding requires k >= 2 (15 is special-cased)")
    one = field.one()

    S3poly, b = ps._decode_square_gadget(
        G=coeffs, field=field, boundary_error_coeff_deg_d=field.neg(one)
    )
    P1 = ps._poly_sub(coeffs, _square_gadget_poly(S3poly, b, field), field)

    G2 = ps._poly_scale_int(P1, -1, field)  # = x·S_2² + (S_2+a)² − P_{2k+1}
    S2poly, a = ps._decode_square_gadget(
        G=G2, field=field, boundary_error_coeff_deg_d=field.neg(one)
    )
    Pm = ps._poly_add(P1, _square_gadget_poly(S2poly, a, field), field)  # = P_{2k+1}

    inner = _decode_odd(ps._poly_trim(Pm, field), field, pair_context=True)
    _T1i, _T2i, Hs = ps._poly_paper_splittable_pair(n=2 * k + 1, alpha=inner, field=field)

    enc2, hs2 = _build_Q_encoder(2 * k + 1, Hs, field)
    S2block = ps._decode_by_descending_pivots(
        target=S2poly, encode_fn=enc2, nparams=2 * k + 1, field=field, what="Q_{2k+1}"
    )
    Hs = hs2(S2block)

    enc3, _hs3 = _build_Q_encoder(4 * k + 3, Hs, field)
    S3block = ps._decode_by_descending_pivots(
        target=S3poly, encode_fn=enc3, nparams=4 * k + 3, field=field, what="Q_{4k+3}"
    )

    alpha = list(inner) + [a] + list(S2block) + [b] + list(S3block)
    if len(alpha) != n:
        raise RuntimeError("internal error: 8k+7 parameter count mismatch")
    return alpha


# ---------------------------------------------------------------------------
# Special case 27
# ---------------------------------------------------------------------------


def _decode_pair_27(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode the special-case construction for 27:
      P = (x+1)·T_1 + S_3² − H_2² + α_0,   T_1 = S_1² − S_2² + α_1,
      S_1 = Q_13(x,H_2)  (which yields H_4),  S_2 = Q_3(x,H_2),
      S_3 = Q_7(x,H_2,H_4).
    """

    one = field.one()
    x = _x(field)
    x_plus_1 = [one, one]

    # T_1 top coefficients by back-substitution on (x+1)T_1 (rows >= 15 clean;
    # row 14 carries the +1 of the monic S_3²).
    t: Dict[int, Number] = {26: one}
    for j in range(26, 14, -1):
        t[j - 1] = field.sub(ps._poly_coeff(coeffs, j, field), t[j])
    t[13] = field.sub(field.sub(ps._poly_coeff(coeffs, 14, field), t[14]), one)

    # S_1² agrees with T_1 in degrees >= 13; monic square root (lem:monic-from-power, m=2).
    S1_sq: Poly = [field.zero()] * 27
    for j in range(13, 27):
        S1_sq[j] = t[j]
    S1 = ps._monic_sqrt_from_high_square_coeffs(ps._poly_trim(S1_sq, field), root_deg=13, field=field)

    P2 = ps._poly_sub(coeffs, ps._poly_mul(x_plus_1, ps._poly_square(S1, field), field), field)

    # S_3² from rows 8..14 of P2 (+1 correction at row 7 from the monic Q_3²).
    S3_sq: Poly = [field.zero()] * 15
    for j in range(8, 15):
        S3_sq[j] = ps._poly_coeff(P2, j, field)
    S3_sq[7] = field.add(ps._poly_coeff(P2, 7, field), one)
    S3 = ps._monic_sqrt_from_high_square_coeffs(ps._poly_trim(S3_sq, field), root_deg=7, field=field)

    P3 = ps._poly_sub(P2, ps._poly_square(S3, field), field)

    # Remaining low block: P3 = −(x+1)·Q_3² + (x+1)·α_1 − H_2² + α_0, read
    # from degree 6 downwards in the coefficients of Q_3 = x³+γ₂x²+γ₁x+γ₀
    # and H_2 = x²+bx+c (a triangular chain, one new quantity per degree).
    low = _decode_27_low_block(P3, field)
    H2 = [low[2], low[3], one]

    # S_1 = Q_13(x, H_2): the k=3, l=1 known-powers gadget; byproduct H_4.
    def enc_q13(a: List[Number]) -> Poly:
        q, _hs, _t = ps._poly_paper_Q_2lp1k_minus_1_with_powers(
            k=3, l=1, alpha=list(a), Hs=[x, H2], field=field
        )
        return ps._poly_trim(q, field)

    q13 = ps._decode_by_descending_pivots(
        target=S1, encode_fn=enc_q13, nparams=13, field=field, what="Q13 given H2"
    )
    _q, hs_raw, _t = ps._poly_paper_Q_2lp1k_minus_1_with_powers(
        k=3, l=1, alpha=q13, Hs=[x, H2], field=field
    )
    H4 = hs_raw[2]

    q7 = ps._decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S3, k=3, Hs=[_x(field), H2, H4], field=field)

    alpha = list(low) + list(q7) + list(q13)
    if len(alpha) != 27:
        raise RuntimeError("internal error: 27 parameter count mismatch")
    return alpha


# ---------------------------------------------------------------------------
# Special case 31
# ---------------------------------------------------------------------------


def _decode_pair_31(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode the special-case construction for 31:
      P = x·S_1² + (S_1+α_15)² − x·S_2² − H_4² + x·S_3 + α_0,
      S_1 = bar-Q_15(x,H_2,H_4), S_2 = Q_7(x,H_2,H_4), S_3 = Q_3(x,H_2),
      H_4 = H_2² − (x+α_5)² + α_4.
    """

    one = field.one()

    S1, a15 = ps._decode_square_gadget(
        G=coeffs, field=field, boundary_error_coeff_deg_d=field.neg(one)
    )
    P1 = ps._poly_sub(coeffs, _square_gadget_poly(S1, a15, field), field)

    # S_2² from −P1 on rows 9..15 (row 8 corrected by the monic H_4²).
    S2_sq: Poly = [field.zero()] * 15
    for d in range(9, 16):
        S2_sq[d - 1] = field.neg(ps._poly_coeff(P1, d, field))
    S2_sq[7] = field.neg(field.add(ps._poly_coeff(P1, 8, field), one))
    S2 = ps._monic_sqrt_from_high_square_coeffs(ps._poly_trim(S2_sq, field), root_deg=7, field=field)

    P2 = ps._poly_add(P1, ps._poly_shift_xk(ps._poly_square(S2, field), 1, field), field)

    # H_4² from −P2 on rows 5..8 (row 4 corrected by the monic x·S_3).
    H4_sq: Poly = [field.zero()] * 9
    for d in range(5, 9):
        H4_sq[d] = field.neg(ps._poly_coeff(P2, d, field))
    H4_sq[4] = field.sub(one, ps._poly_coeff(P2, 4, field))
    H4 = ps._monic_sqrt_from_high_square_coeffs(ps._poly_trim(H4_sq, field), root_deg=4, field=field)

    low = ps._poly_add(P2, ps._poly_square(H4, field), field)  # = x·S_3 + α_0
    alpha0 = ps._poly_coeff(low, 0, field)
    S3 = _shift_down(low, field)

    # α_4..α_7 from H_4 = H_2² − (x+α_5)² + α_4 with H_2 = x² + α_7 x + α_6.
    def enc_H4(a: List[Number]) -> Poly:
        H2 = [a[2], a[3], one]
        return ps._poly_add_const(
            ps._poly_sub(ps._poly_square(H2, field), ps._poly_square([a[1], one], field), field),
            a[0],
            field,
        )

    a47 = ps._decode_by_descending_pivots(
        target=H4, encode_fn=enc_H4, nparams=4, field=field, what="H4 block"
    )
    H2 = [a47[2], a47[3], one]

    q3 = ps._decode_Q3_coeffs_to_alpha_given_H2(S3, H2, field)
    q7 = ps._decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S2, k=3, Hs=[_x(field), H2, H4], field=field)

    def enc_bar(a: List[Number]) -> Poly:
        return ps._poly_trim(ps._poly_paper_barQ_15(alpha=list(a), H2=H2, H4=H4, field=field), field)

    bar = ps._decode_by_descending_pivots(
        target=S1, encode_fn=enc_bar, nparams=15, field=field, what="barQ15 given (H2,H4)"
    )

    alpha = [alpha0] + list(q3) + list(a47) + list(q7) + [a15] + list(bar)
    if len(alpha) != 31:
        raise RuntimeError("internal error: 31 parameter count mismatch")
    return alpha


# =============================================================================
# Symbolic parameters and the chain printer
# =============================================================================


class Sym:
    """
    Tiny sparse multivariate polynomial over Q in the parameters a_0, a_1, ...
    Used as the scalar type when building a chain with symbolic parameters
    (in the constructions, parameters only ever enter affinely as constant
    terms of the multiplied forms, so these stay simple).
    """

    __slots__ = ("terms",)

    def __init__(self, terms: Optional[Dict[Tuple[int, ...], Fraction]] = None):
        self.terms: Dict[Tuple[int, ...], Fraction] = {}
        if terms:
            for mono, c in terms.items():
                if c:
                    self.terms[mono] = c

    @staticmethod
    def const(c: Union[int, Fraction]) -> "Sym":
        return Sym({(): Fraction(c)})

    @staticmethod
    def var(i: int) -> "Sym":
        return Sym({(i,): Fraction(1)})

    @staticmethod
    def _lift(v) -> Optional["Sym"]:
        if isinstance(v, Sym):
            return v
        if isinstance(v, (int, Fraction)):
            return Sym.const(v)
        return None

    def __add__(self, other):
        o = Sym._lift(other)
        if o is None:
            return NotImplemented
        out = dict(self.terms)
        for mono, c in o.terms.items():
            out[mono] = out.get(mono, Fraction(0)) + c
        return Sym(out)

    __radd__ = __add__

    def __neg__(self):
        return Sym({m: -c for m, c in self.terms.items()})

    def __sub__(self, other):
        o = Sym._lift(other)
        if o is None:
            return NotImplemented
        return self + (-o)

    def __rsub__(self, other):
        o = Sym._lift(other)
        if o is None:
            return NotImplemented
        return o + (-self)

    def __mul__(self, other):
        o = Sym._lift(other)
        if o is None:
            return NotImplemented
        out: Dict[Tuple[int, ...], Fraction] = {}
        for m1, c1 in self.terms.items():
            for m2, c2 in o.terms.items():
                mono = tuple(sorted(m1 + m2))
                out[mono] = out.get(mono, Fraction(0)) + c1 * c2
        return Sym(out)

    __rmul__ = __mul__

    def __mod__(self, other):  # pragma: no cover - defensive
        raise TypeError("symbolic values do not support %")

    def __eq__(self, other):
        o = Sym._lift(other)
        if o is None:
            return NotImplemented
        return self.terms == o.terms

    def __hash__(self):
        return hash(frozenset(self.terms.items()))

    def is_const(self) -> bool:
        return all(m == () for m in self.terms)

    def __rtruediv__(self, other):
        if self.is_const():
            c = self.terms.get((), Fraction(0))
            if c == 0:
                raise ZeroDivisionError("division by zero symbolic constant")
            o = Sym._lift(other)
            return Sym({m: cc / c for m, cc in o.terms.items()})
        raise TypeError("cannot invert a non-constant symbolic value")

    def render(self, var_fmt) -> str:
        if not self.terms:
            return "0"
        parts: List[str] = []
        for mono in sorted(self.terms, key=lambda m: (len(m), m)):
            c = self.terms[mono]
            body = "*".join(var_fmt(i) for i in mono)
            if not mono:
                term = str(c)
            elif c == 1:
                term = body
            elif c == -1:
                term = "-" + body
            else:
                term = f"{c}*{body}"
            parts.append(term)
        out = parts[0]
        for term in parts[1:]:
            if term.startswith("-"):
                out += " - " + term[1:]
            else:
                out += " + " + term
        return out


_WIRE_LETTERS = ["y", "z", "t", "u", "v", "w", "s", "r", "q", "p", "o", "m", "j", "h", "g", "f", "e", "d", "c", "b"]


def _wire_name(i: int) -> str:
    """Name for the i-th multiplication output (appendix style: y, z, t, ...)."""

    if i < len(_WIRE_LETTERS):
        return _WIRE_LETTERS[i]
    return f"g{i}"


@dataclass
class Program:
    """A symbolic polynomial chain for P_n[a_0..a_{n-1}]."""

    n: int
    chain: ps.PolynomialChain
    param_name: str = "a"

    @property
    def mul_count(self) -> int:
        return self.chain.mul_count

    @property
    def height(self) -> int:
        """Multiplicative height: depth of the multiplication DAG (Horner: n-1)."""

        depth: Dict[int, int] = {}
        for g in self.chain.gates:
            d = 0
            for aff in (g.left, g.right):
                for w in aff.terms:
                    d = max(d, depth.get(w, 0))
            depth[g.out_wire] = d + 1
        return max((depth.get(w, 0) for w in self.chain.output.terms), default=0)

    @property
    def add_count(self) -> int:
        """Additions/subtractions in the paper's share-aware ledger
        convention: a let-bound subexpression used more than once is charged
        once.  Gadget output values (registered by the builders as
        ``marked_values``) are materialized once at their own cost; a form
        that reuses such a value pays a single addition for it (negation is
        free), plus one per surviving nonzero key constant."""

        def is_zero(c) -> bool:
            if isinstance(c, Sym):
                return not c.terms
            return c == 0

        def neg(c):
            return c * (-1) if isinstance(c, Sym) else -c

        marked = getattr(self.chain, "marked_values", [])
        registry: List[Tuple[Dict[int, int], object]] = []

        def cost(a, reg) -> int:
            terms = dict(a.terms)
            const = a.const
            groups = 0
            for sig, sc in sorted(reg, key=lambda e: -len(e[0])):
                if not sig or (len(sig) == 1 and is_zero(sc)):
                    continue
                for eps in (1, -1):
                    if all(terms.get(w) == eps * c0 for w, c0 in sig.items()):
                        for w in sig:
                            del terms[w]
                        if not is_zero(sc):
                            const = const - sc if eps == 1 else const + sc
                        groups += 1
                        break
            n_ops = len(terms) + groups
            return max(0, n_ops - 1) + (0 if is_zero(const) else 1)

        total = 0
        for form in marked:
            total += cost(form, registry)
            registry.append((dict(form.terms), form.const))
        for g in self.chain.gates:
            total += cost(g.left, registry) + cost(g.right, registry)
        return total + cost(self.chain.output, registry)

    # -- rendering helpers ---------------------------------------------------

    def _const_str(self, c, var_fmt) -> str:
        if isinstance(c, Sym):
            return c.render(var_fmt)
        return str(c)

    def _affine_str(self, aff: ps.AffineForm, var_fmt) -> str:
        parts: List[str] = []
        for w in sorted(aff.terms):
            coef = aff.terms[w]
            nm = self.chain.wire_names[w]
            if coef == 1:
                parts.append(nm)
            elif coef == -1:
                parts.append("-" + nm)
            else:
                parts.append(f"{coef}*{nm}")
        cs = self._const_str(aff.const, var_fmt)
        if cs != "0" or not parts:
            parts.append(cs)
        out = parts[0]
        for term in parts[1:]:
            if term.startswith("-"):
                out += " - " + term[1:]
            else:
                out += " + " + term
        return out

    def render_text(self) -> str:
        """One line per multiplication, in the style of appendix_polynomials.tex."""

        pn = self.param_name
        var_fmt = lambda i: f"{pn}{i}"  # noqa: E731
        lines = [
            f"# P_{self.n}[{pn}0..{pn}{self.n - 1}]: "
            f"{self.mul_count} multiplications, height {self.height}"
        ]
        for g in self.chain.gates:
            out = self.chain.wire_names[g.out_wire]
            lines.append(
                f"{out} = ({self._affine_str(g.left, var_fmt)})({self._affine_str(g.right, var_fmt)})"
            )
        lines.append(f"P = {self._affine_str(self.chain.output, var_fmt)}")
        return "\n".join(lines)

    def render_latex(self) -> str:
        pn = self.param_name
        var_fmt = lambda i: f"{pn}_{{{i}}}"  # noqa: E731
        lines = ["\\begin{aligned}"]
        for g in self.chain.gates:
            out = self.chain.wire_names[g.out_wire]
            left = self._affine_str(g.left, var_fmt)
            right = self._affine_str(g.right, var_fmt)
            lines.append(f"{out} &= ({left})({right}) \\\\")
        lines.append(f"P &= {self._affine_str(self.chain.output, var_fmt)}")
        lines.append("\\end{aligned}")
        return "\n".join(lines)

    def to_json(self) -> str:
        pn = self.param_name
        var_fmt = lambda i: f"{pn}{i}"  # noqa: E731

        def aff(a: ps.AffineForm):
            return {
                "const": self._const_str(a.const, var_fmt),
                "terms": {self.chain.wire_names[w]: k for w, k in sorted(a.terms.items())},
            }

        doc = {
            "n": self.n,
            "multiplications": self.mul_count,
            "height": self.height,
            "parameters": [f"{pn}{i}" for i in range(self.n)],
            "wires": list(self.chain.wire_names),
            "gates": [
                {
                    "out": self.chain.wire_names[g.out_wire],
                    "left": aff(g.left),
                    "right": aff(g.right),
                }
                for g in self.chain.gates
            ],
            "output": aff(self.chain.output),
        }
        return json.dumps(doc, indent=2)

    def __str__(self) -> str:
        return self.render_text()


def _with_peeled(thunk):
    """Run a callable with the peeled known-powers gadget mode enabled."""

    ps.set_peeled_q(True)
    try:
        return thunk()
    finally:
        ps.set_peeled_q(False)


def chain(n: int, *, peeled: bool = False) -> Program:
    """
    The paper's polynomial chain for P_n[a_0..a_{n-1}] with symbolic
    parameters; ⌊n/2⌋+1 multiplications for n >= 3.

    With ``peeled=True`` the known-powers gadgets use the depth-balanced
    peeled recursion: identical multiplication and addition counts, height
    O(log n) instead of Θ((log n)^2).
    """

    if peeled:
        return _with_peeled(lambda: chain(n))

    if n < 1:
        raise ValueError("chain requires n >= 1")
    field = ps.Field(modulus=None, use_fractions=False)
    params: List[Number] = [Sym.var(i) for i in range(n)]
    builder = ps.ChainBuilder(field)

    def build_P(deg: int, a: List[Number]) -> ps.AffineForm:
        if deg == 1:
            return builder.x.add_const(a[0], field)
        if deg == 5:
            return ps._paper_P5(builder, a)
        if deg == 7:
            return ps._paper_P7(builder, a)
        if deg % 2 == 0:
            q = build_P(deg - 1, a[1:])
            return builder.mul(q, builder.x).add_const(a[0], field)
        T1, T2, _H2 = ps._paper_splittable_pair(builder, deg, a)
        return builder.mul(T1, builder.x).add(T2, field)

    out = build_P(n, params)
    ch = builder.finalize(out)
    ch.marked_values = list(builder.marked_values)
    ch.validate()
    ch.wire_names = ["1", "x"] + [_wire_name(i) for i in range(len(ch.gates))]
    return Program(n=n, chain=ch)


# =============================================================================
# Key normalization ("reduced" chains)
# =============================================================================


def _sym_linear_parts(c: Sym) -> Tuple[Fraction, Dict[int, Fraction]]:
    """Split a linear symbolic constant into (scalar, {key index: coefficient})."""

    scalar = Fraction(0)
    coeffs: Dict[int, Fraction] = {}
    for mono, k in c.terms.items():
        if mono == ():
            scalar += k
        elif len(mono) == 1:
            coeffs[mono[0]] = coeffs.get(mono[0], Fraction(0)) + k
        else:
            raise ValueError("gate constant is not linear in the keys")
    return scalar, coeffs


def _fraction_matrix_inverse(m: List[List[Fraction]]) -> Tuple[List[List[Fraction]], Fraction]:
    """Inverse and determinant of a square Fraction matrix (Gauss-Jordan)."""

    n = len(m)
    aug = [[Fraction(v) for v in row] + [Fraction(int(i == j)) for j in range(n)]
           for i, row in enumerate(m)]
    det = Fraction(1)
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if piv is None:
            raise ValueError("key map is singular")
        if piv != col:
            aug[col], aug[piv] = aug[piv], aug[col]
            det = -det
        det *= aug[col][col]
        inv = 1 / aug[col][col]
        aug[col] = [v * inv for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [v - f * w for v, w in zip(aug[r], aug[col])]
    return [row[n:] for row in aug], det


def _fraction_to_field(fr: Fraction, field: Field) -> Number:
    if field.modulus is None:
        return fr
    p = field.modulus
    return (fr.numerator % p) * pow(fr.denominator % p, -1, p) % p


@dataclass
class ReducedProgram:
    """
    The chain of `chain(n)` after the unitriangular key normalization: every
    gate constant is a single fresh key `b_i`.  The keys are related by
    `b_i = rows[i](a_0..a_{n-1})` (an affine form with a unit determinant of
    the shape ±2^k, so the two parameterizations are interchangeable whenever
    2 is invertible).  The index of each `b_i` is the pivot slot of the
    original key it replaces, so the decoder order is unchanged.
    """

    program: Program
    rows: List[Sym]
    det: Fraction

    def key_matrix(self) -> Tuple[List[List[Fraction]], List[Fraction]]:
        """`b = M a + v` as a Fraction matrix and offset vector."""

        n = self.program.n
        mat = [[Fraction(0)] * n for _ in range(n)]
        off = [Fraction(0)] * n
        for i, row in enumerate(self.rows):
            scalar, coeffs = _sym_linear_parts(row)
            off[i] = scalar
            for j, c in coeffs.items():
                mat[i][j] = c
        return mat, off


def reduce_keys(prog: Program) -> ReducedProgram:
    """
    Normalize the keys of a symbolic chain so that every gate constant is a
    single fresh key.  Constants that are pure numbers (0 in particular) are
    left alone.  The construction guarantees each remaining constant contains
    at least one key not seen in any earlier constant; that key's slot names
    the new key, giving an affine key change with determinant ±2^k.
    """

    ch = prog.chain
    n = prog.n

    # 1. the distinct key-bearing constants, in program order (a square's two
    #    identical factors contribute one constant)
    consts: List[Sym] = []
    seen: Dict[Sym, int] = {}
    def visit(aff: ps.AffineForm) -> None:
        c = aff.const
        if isinstance(c, Sym) and not c.is_const() and c not in seen:
            seen[c] = len(consts)
            consts.append(c)
    for g in ch.gates:
        visit(g.left)
        visit(g.right)
    visit(ch.output)
    if len(consts) != n:
        raise ValueError(
            f"expected exactly n={n} distinct key-bearing constants, got {len(consts)}")

    # 2. slot assignment: greedy fresh-pivot naming where possible (stable,
    #    decoder-ordered), remaining constants take the remaining slots in
    #    program order
    slot_of: Dict[Sym, int] = {}
    used_slots = set()
    for c in consts:
        _, coeffs = _sym_linear_parts(c)
        fresh = [i for i in coeffs if i not in used_slots]
        unit_fresh = [i for i in fresh if abs(coeffs[i]) == 1]
        if unit_fresh or fresh:
            pivot = min(unit_fresh) if unit_fresh else min(fresh)
            slot_of[c] = pivot
            used_slots.add(pivot)
    leftover = [i for i in range(n) if i not in used_slots]
    for c in consts:
        if c not in slot_of:
            slot_of[c] = leftover.pop(0)

    # 3. rewrite every constant occurrence as its slot's fresh key
    def normalized(aff: ps.AffineForm) -> ps.AffineForm:
        c = aff.const
        if isinstance(c, Sym) and not c.is_const():
            return ps.AffineForm(Sym.var(slot_of[c]), dict(aff.terms))
        return aff
    gates = [
        dataclasses.replace(g, left=normalized(g.left), right=normalized(g.right))
        for g in ch.gates
    ]
    newch = dataclasses.replace(ch, gates=gates, output=normalized(ch.output))

    rows: List[Sym] = [Sym.var(i) for i in range(n)]
    for c, i in slot_of.items():
        rows[i] = c
    red = ReducedProgram(
        program=Program(n=n, chain=newch, param_name="b"), rows=rows,
        det=Fraction(1))
    mat, off = red.key_matrix()
    inv, det = _fraction_matrix_inverse(mat)
    red.det = det
    # `det` is a product of the construction's small integer slopes; the two key
    # spaces are interchangeable over any field in which it is invertible (its
    # prime factors are at most n, so n-admissibility suffices).
    return red


def reduced_chain(n: int) -> ReducedProgram:
    """The key-normalized chain for `P_n`."""

    return reduce_keys(chain(n))


def encode_reduced(n: int, bs: Sequence[Number], field: Optional[Field] = None) -> List[Number]:
    """Coefficients of the reduced-key chain at keys `b` (solves `M a = b - v`)."""

    field = field or default_field()
    red = reduced_chain(n)
    mat, off = red.key_matrix()
    inv, _ = _fraction_matrix_inverse(mat)
    bs = [field.coerce(v) for v in bs]
    shifted = [field.sub(b, _fraction_to_field(off[i], field)) for i, b in enumerate(bs)]
    alphas = [
        functools.reduce(
            field.add,
            (field.mul(_fraction_to_field(inv[i][j], field), shifted[j]) for j in range(n)),
            field.zero(),
        )
        for i in range(n)
    ]
    return encode(n, alphas, field)


def decode_reduced(n: int, coeffs: Sequence[Number], field: Optional[Field] = None) -> List[Number]:
    """Reduced keys `b` of the monic polynomial with the given coefficients."""

    field = field or default_field()
    alphas = decode(n, coeffs, field)
    red = reduced_chain(n)
    out: List[Number] = []
    for row in red.rows:
        scalar, cf = _sym_linear_parts(row)
        acc = _fraction_to_field(scalar, field)
        for j, c in cf.items():
            acc = field.add(acc, field.mul(_fraction_to_field(c, field), alphas[j]))
        out.append(acc)
    return out


# =============================================================================
# Self-test and CLI
# =============================================================================


def _selftest(max_n: int, *, seed: int = 0, verbose: bool = True) -> None:
    field = default_field()
    rng = random.Random(seed)
    for n in range(1, max_n + 1):
        alphas = [rng.randrange(field.modulus) for _ in range(n)]
        cs = encode(n, alphas, field)
        back = decode(n, cs, field)
        if [field.coerce(a) for a in alphas] != back:
            raise SystemExit(f"selftest FAILED at n={n}: decoded parameters differ")
        prog = chain(n)
        want = 0 if n <= 1 else (1 if n == 2 else n // 2 + 1)
        if prog.mul_count != want:
            raise SystemExit(f"selftest FAILED at n={n}: {prog.mul_count} muls, want {want}")
        if n >= 3:
            ln = (n - 1).bit_length()  # = ceil(log2 n) for n >= 2
            hbound = ln * ln // 4 + ln + 2
            if prog.height > hbound:
                raise SystemExit(
                    f"selftest FAILED at n={n}: height {prog.height} > bound {hbound}")
        if n >= 3:
            pp = chain(n, peeled=True)
            if pp.mul_count != prog.mul_count:
                raise SystemExit(f"selftest FAILED at n={n}: peeled mults differ")
            if pp.add_count > prog.add_count:
                raise SystemExit(
                    f"selftest FAILED at n={n}: peeled adds {pp.add_count} > {prog.add_count}")
            if pp.height > prog.height:
                raise SystemExit(f"selftest FAILED at n={n}: peeled height regressed")
            lnn = (n - 1).bit_length()  # ceil(log2 n) for n >= 2
            if pp.height > 2 * lnn + 6:
                raise SystemExit(
                    f"selftest FAILED at n={n}: peeled height {pp.height} > 2L+6")
            csp = encode(n, alphas, field, peeled=True)
            if decode(n, csp, field, peeled=True) != [field.coerce(a) for a in alphas]:
                raise SystemExit(f"selftest FAILED at n={n}: peeled round-trip")
        if n >= 3:
            red = reduce_keys(prog)
            for g in red.program.chain.gates:
                for aff in (g.left, g.right):
                    c = aff.const
                    if isinstance(c, Sym) and not c.is_const():
                        if list(c.terms.keys()) not in ([()],) and (
                            len(c.terms) != 1 or any(len(m) != 1 for m in c.terms)
                            or any(v != 1 for v in c.terms.values())
                        ):
                            raise SystemExit(
                                f"selftest FAILED at n={n}: reduced const {c.terms}")
            bs = [rng.randrange(field.modulus) for _ in range(n)]
            cs2 = encode_reduced(n, bs, field)
            if decode_reduced(n, cs2, field) != [field.coerce(b) for b in bs]:
                raise SystemExit(f"selftest FAILED at n={n}: reduced round-trip")
        if verbose and (n % 10 == 0 or n == max_n):
            print(f"  n <= {n}: ok")
    print(f"selftest OK (n <= {max_n}, GF(2^61-1))")


def _parse_values(text: str, field: Field) -> List[Number]:
    items = [s for s in text.replace(",", " ").split() if s]
    out: List[Number] = []
    for s in items:
        if "/" in s and field.modulus is None:
            out.append(Fraction(s))
        else:
            out.append(int(s))
    return [field.coerce(v) for v in out]


def _field_from_args(args) -> Field:
    if getattr(args, "rational", False):
        return rationals()
    return GF(args.prime)


def main(argv: Optional[List[str]] = None) -> None:
    p = argparse.ArgumentParser(description=__doc__.splitlines()[1])
    sub = p.add_subparsers(dest="cmd", required=True)

    pc = sub.add_parser("chain", help="print the degree-n polynomial chain")
    pc.add_argument("n", type=int)
    pc.add_argument("--reduced", action="store_true",
                    help="normalize keys so every gate constant is one fresh key")
    pc.add_argument("--peeled", action="store_true",
                    help="depth-balanced known-powers gadgets: same multiplications "
                         "and additions, height O(log n)")
    fmt = pc.add_mutually_exclusive_group()
    fmt.add_argument("--latex", action="store_true")
    fmt.add_argument("--json", action="store_true")

    pd = sub.add_parser("decode", help="coefficients -> parameters")
    pd.add_argument("n", type=int)
    pd.add_argument("--coeffs", required=True, help="c0,c1,...,c_{n-1} (monic x^n implied)")
    pd.add_argument("--prime", type=int, default=MERSENNE61)
    pd.add_argument("--rational", action="store_true")
    pd.add_argument("--reduced", action="store_true",
                    help="return the normalized keys b instead of the a's")
    pd.add_argument("--peeled", action="store_true",
                    help="use the depth-balanced parameter layout")

    pe = sub.add_parser("encode", help="parameters -> coefficients")
    pe.add_argument("n", type=int)
    pe.add_argument("--alphas", required=True, help="a0,a1,...,a_{n-1}")
    pe.add_argument("--prime", type=int, default=MERSENNE61)
    pe.add_argument("--rational", action="store_true")
    pe.add_argument("--reduced", action="store_true",
                    help="interpret the given values as normalized keys b")
    pe.add_argument("--peeled", action="store_true",
                    help="use the depth-balanced parameter layout")

    st = sub.add_parser("selftest", help="round-trip encode/decode + chain counts")
    st.add_argument("--max-n", type=int, default=120)
    st.add_argument("--seed", type=int, default=0)

    args = p.parse_args(argv)

    if args.cmd == "chain":
        if args.reduced and args.peeled:
            prog = _with_peeled(lambda: reduced_chain(args.n).program)
        elif args.reduced:
            prog = reduced_chain(args.n).program
        else:
            prog = chain(args.n, peeled=args.peeled)
        if args.latex:
            print(prog.render_latex())
        elif args.json:
            print(prog.to_json())
        else:
            print(prog.render_text())
        return

    if args.cmd == "decode":
        field = _field_from_args(args)
        cs = _parse_values(args.coeffs, field)
        if args.reduced:
            fn = (lambda *a: _with_peeled(lambda: decode_reduced(*a))) if args.peeled else decode_reduced
            alphas = fn(args.n, cs, field)
        else:
            alphas = decode(args.n, cs, field, peeled=args.peeled)
        print(",".join(str(a) for a in alphas))
        return

    if args.cmd == "encode":
        field = _field_from_args(args)
        alphas = _parse_values(args.alphas, field)
        if args.reduced:
            fn = (lambda *a: _with_peeled(lambda: encode_reduced(*a))) if args.peeled else encode_reduced
            cs = fn(args.n, alphas, field)
        else:
            cs = encode(args.n, alphas, field, peeled=args.peeled)
        print(",".join(str(c) for c in cs))
        return

    if args.cmd == "selftest":
        _selftest(args.max_n, seed=args.seed)
        return


if __name__ == "__main__":
    main()
