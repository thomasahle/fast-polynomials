#!/usr/bin/env python3
"""
poly_schedule.py — build a multiplication schedule (“polynomial chain”) for evaluating a polynomial.

Terminology (matching the notes/papers):
- A "polynomial chain" is a straight-line program with multiplication gates.
- Each multiplication gate computes the product of two affine-linear forms in
  previously computed values (wires).

This module compiles a *specific* monic polynomial
    P(x) = a_0 + a_1 x + ... + a_{n-1} x^{n-1} + x^n
into such a chain, returning a schedule (gates + final affine form).

Cost model / restrictions (paper-style)
--------------------------------------
We count *all* field multiplications, including scalar multiplies. Therefore:
- Linear forms may use only *integer* coefficients on wires (so no hidden `a*x`).
  Small integer multiples are understood as repeated additions/subtractions.
- Scalar multiplication is represented explicitly as a multiplication gate where
  one side is a constant affine form.

Implemented constructions
------------------------
This file implements the paper-style base constructions for monic degrees:
- 1 (trivial)
- 3 (`Q_3` / 2 multiplications)
- 5 (`Q_5` / 3 multiplications)
- 7 (`Q_7` / 4 multiplications; paper variant requires `2 ≠ 0`, but a char-2-specific
  variant is implemented for GF(2))
and an even-degree lift:
    P(x) = a_0 + x * Q(x)    where Q is monic of degree n-1.

Horner is used only inside `--check` as a reference evaluator; it is not used
to generate schedules.
"""

from __future__ import annotations

import dataclasses
import math
import random
from dataclasses import dataclass
from fractions import Fraction
from typing import Dict, Iterable, List, Optional, Tuple, Union

Number = Union[int, float, Fraction]



# =============================================================================
# Peeled ("depth-balanced") known-powers gadget mode
# =============================================================================
#
# When enabled, the known-powers gadget Q_{2^k-1} (k >= 3) is built by the
# peeled recursion
#     Q_{2^k-1} = (H_{2^{k-1}} + gamma) * W + B,      W, B = Q_{2^{k-1}-1},
# instead of the sequential fill A_{2^{k-2}}.  Same multiplications
# (2^{k-1}-1) and additions (5*2^{k-2}-2), height exactly k instead of ~2k.
# The decoder divides by the known monic H (quotient = W), reads gamma at the
# residual's top row (both children are monic), and subtracts.  Parameter
# layout: [gamma] + W-params + B-params, recursively; k <= 2 is unchanged.

PEELED_Q = False


def set_peeled_q(flag: bool) -> None:
    global PEELED_Q
    PEELED_Q = bool(flag)

class Field:
    """Minimal field-like wrapper for exact rationals or prime fields."""

    def __init__(self, modulus: Optional[int] = None, use_fractions: bool = True):
        self.modulus = modulus
        self.use_fractions = use_fractions and modulus is None

    def coerce(self, x: Number) -> Number:
        if self.modulus is not None:
            return int(x) % self.modulus
        if self.use_fractions:
            return x if isinstance(x, Fraction) else Fraction(x)
        return x

    def zero(self) -> Number:
        return self.coerce(0)

    def one(self) -> Number:
        return self.coerce(1)

    def add(self, a: Number, b: Number) -> Number:
        if self.modulus is not None:
            return (a + b) % self.modulus
        return a + b

    def sub(self, a: Number, b: Number) -> Number:
        if self.modulus is not None:
            return (a - b) % self.modulus
        return a - b

    def neg(self, a: Number) -> Number:
        if self.modulus is not None:
            return (-a) % self.modulus
        return -a

    def mul(self, a: Number, b: Number) -> Number:
        if self.modulus is not None:
            return (a * b) % self.modulus
        return a * b

    def inv(self, a: Number) -> Number:
        if self.modulus is not None:
            p = self.modulus
            a = a % p
            if a == 0:
                raise ZeroDivisionError("division by zero in prime field")
            return pow(a, p - 2, p)
        if a == 0:
            raise ZeroDivisionError("division by zero")
        return self.one() / a

    def div(self, a: Number, b: Number) -> Number:
        return self.mul(a, self.inv(b))

    def sqrt(self, a: Number) -> Number:
        """
        Square root in the underlying field.

        Notes:
        - For the prime field GF(2), Frobenius is the identity so sqrt(a)=a.
        - For other prime fields this is not implemented (add Tonelli–Shanks if needed).
        """

        if self.modulus is None:
            raise NotImplementedError("sqrt() is only implemented for prime fields")
        if self.modulus == 2:
            return a % 2
        raise NotImplementedError("sqrt() is not implemented for odd prime fields")

    def is_zero(self, a: Number) -> bool:
        if self.modulus is not None:
            return (a % self.modulus) == 0
        return a == 0


@dataclass(frozen=True)
class AffineForm:
    """
    Affine form in previously-computed wires:
        const + sum_{w in terms} (k_w * wire[w])   where k_w is an integer

    Restriction: wire coefficients are *integers* (typically small). This matches
    the cost model used in the notes: additions/subtractions are free, so we can
    form `y+y` (i.e., coefficient 2) without a multiplication gate. However we do
    **not** allow arbitrary field-element coefficients on wires inside a linear
    form, since that would hide scalar multiplications that the papers count.

    Wire 0 is the constant 1 (implicit via `const`), wire 1 is x, and wires ≥2
    are multiplication outputs.

    `src` records how the form was produced (``("add", A, B)``, ``("sub", A, B)``,
    ``("addc", A)`` or ``("scale", A, k)``; ``None`` for wires, constants and
    forms built directly).  It is provenance only: it does not take part in
    equality, and `Program.add_count` (tools/polychain.py) walks it to count the
    additions of the builder's schedule as a DAG (including let-bound values
    that the printed chain does not show; `chain n --dag` lists them).
    """

    const: Number
    terms: Dict[int, int]  # wire -> integer coefficient
    src: Optional[tuple] = dataclasses.field(default=None, compare=False, repr=False)

    @staticmethod
    def const_only(c: Number) -> "AffineForm":
        return AffineForm(c, {})

    @staticmethod
    def wire(w: int, coef: int = 1) -> "AffineForm":
        if not isinstance(coef, int):
            raise TypeError("wire coefficient must be an int")
        if coef == 0:
            return AffineForm(0, {})
        return AffineForm(0, {w: coef})

    @staticmethod
    def sum_wires(wires: Iterable[int], const: Number = 0) -> "AffineForm":
        terms: Dict[int, int] = {}
        for w in wires:
            terms[w] = terms.get(w, 0) + 1
            if terms[w] == 0:
                del terms[w]
        return AffineForm(const, terms)

    def add_const(self, c: Number, field: Field) -> "AffineForm":
        return AffineForm(field.add(self.const, c), dict(self.terms), ("addc", self))

    def add(self, other: "AffineForm", field: Field) -> "AffineForm":
        const = field.add(self.const, other.const)
        terms: Dict[int, int] = dict(self.terms)
        for w, k in other.terms.items():
            terms[w] = terms.get(w, 0) + k
            if terms[w] == 0:
                del terms[w]
        return AffineForm(const, terms, ("add", self, other))

    def sub(self, other: "AffineForm", field: Field) -> "AffineForm":
        const = field.sub(self.const, other.const)
        terms: Dict[int, int] = dict(self.terms)
        for w, k in other.terms.items():
            terms[w] = terms.get(w, 0) - k
            if terms[w] == 0:
                del terms[w]
        return AffineForm(const, terms, ("sub", self, other))

    def eval(self, wires: List[Number], field: Field) -> Number:
        acc = field.coerce(self.const)
        for w, k in self.terms.items():
            if not isinstance(k, int):
                raise TypeError(f"wire coefficient must be int, got {type(k).__name__}")
            if k == 0:
                continue
            v = wires[w]
            if k < 0:
                v = field.neg(v)
                k = -k
            # Multiply by a small integer using additions (no field multiplication).
            # Use double-and-add to keep this O(log k) additions.
            addend = v
            while k:
                if k & 1:
                    acc = field.add(acc, addend)
                k >>= 1
                if k:
                    addend = field.add(addend, addend)
        return acc


@dataclass(frozen=True)
class MulGate:
    left: AffineForm
    right: AffineForm
    out_wire: int


@dataclass
class PolynomialChain:
    """
    A straight-line program:
    - wire 0 is constant 1
    - wire 1 is x
    - each gate appends one wire (a multiplication)
    - output is a LinearForm in the wires
    """

    wire_names: List[str]
    gates: List[MulGate]
    output: AffineForm
    field: Field

    def eval(self, x: Number) -> Number:
        wires: List[Number] = [self.field.one(), self.field.coerce(x)]
        for gate in self.gates:
            left_val = gate.left.eval(wires, self.field)
            right_val = gate.right.eval(wires, self.field)
            wires.append(self.field.mul(left_val, right_val))
        return self.output.eval(wires, self.field)

    def validate(self) -> None:
        if len(self.wire_names) != 2 + len(self.gates):
            raise ValueError(
                f"wire_names length mismatch: {len(self.wire_names)} != 2 + {len(self.gates)}"
            )

        for i, gate in enumerate(self.gates):
            # Before gate i, wires are [0..(2+i-1)] == [0..(1+i)].
            max_in_wire = 1 + i
            for side_name, lf in (("left", gate.left), ("right", gate.right)):
                for w, k in lf.terms.items():
                    if w > max_in_wire:
                        raise ValueError(
                            f"gate {i} {side_name} references future wire {w} (max allowed {max_in_wire})"
                        )
                    if not isinstance(k, int):
                        raise TypeError(
                            f"gate {i} {side_name} wire {w} coefficient must be int, got {type(k).__name__}"
                        )

        max_out_wire = 1 + len(self.gates)
        for w, k in self.output.terms.items():
            if w > max_out_wire:
                raise ValueError(
                    f"output references future wire {w} (max allowed {max_out_wire})"
                )
            if not isinstance(k, int):
                raise TypeError(
                    f"output wire {w} coefficient must be int, got {type(k).__name__}"
                )

    def as_dense_schedule(self) -> Tuple[List[List[Number]], List[List[Number]], List[Number]]:
        """
        Return the schedule in the "c_i / b_i" style:

        For gate i (0-based), we have
            y_i = (sum_j c[i][j] * w_j) * (sum_j b[i][j] * w_j)
        where the available wires before this gate are
            w_0 = 1, w_1 = x, w_{2..i+1} = y_{0..i-1}.

        The output polynomial is
            P(x) = sum_j out[j] * w_j
        where out has length 2 + #gates.
        """

        def dense(lf: AffineForm, length: int) -> List[Number]:
            vec: List[Number] = [self.field.zero() for _ in range(length)]
            vec[0] = self.field.coerce(lf.const)
            for w, k in lf.terms.items():
                if w >= length:
                    raise ValueError(f"affine form references future wire {w} (len={length})")
                if not isinstance(k, int):
                    raise TypeError(f"wire coefficient must be int, got {type(k).__name__}")
                vec[w] = self.field.coerce(k)
            return vec

        c_list: List[List[Number]] = []
        b_list: List[List[Number]] = []
        for i, g in enumerate(self.gates):
            n_wires_in = 2 + i
            c_list.append(dense(g.left, n_wires_in))
            b_list.append(dense(g.right, n_wires_in))

        out = dense(self.output, 2 + len(self.gates))
        return c_list, b_list, out

    def describe(self) -> str:
        def fmt_lf(lf: AffineForm) -> str:
            def is_neg(v: Number) -> bool:
                if self.field.modulus is not None:
                    return False
                return v < 0  # type: ignore[operator]

            chunks: List[str] = []

            def add_term(term: str, sign: int) -> None:
                if not chunks:
                    chunks.append(term if sign == 1 else f"-{term}")
                else:
                    chunks.append(f"+ {term}" if sign == 1 else f"- {term}")

            for w in sorted(lf.terms):
                k = lf.terms[w]
                if not isinstance(k, int):
                    raise TypeError(f"wire coefficient must be int, got {type(k).__name__}")
                if k == 0:
                    continue
                nm = self.wire_names[w] if w < len(self.wire_names) else f"w{w}"

                # Prefer spelling small integer multiples as repeated additions/subtractions
                # to avoid suggesting a “free” scalar multiplication.
                if abs(k) <= 3:
                    sign = 1 if k > 0 else -1
                    for _ in range(abs(k)):
                        add_term(nm, sign)
                else:
                    sign = 1 if k > 0 else -1
                    add_term(f"{abs(k)}*{nm}", sign)

            if not self.field.is_zero(lf.const) or not chunks:
                c = lf.const
                if not chunks:
                    chunks.append(f"{c}")
                elif is_neg(c):
                    chunks.append(f"- {-c}")  # type: ignore[operator]
                else:
                    chunks.append(f"+ {c}")

            return " ".join(chunks)

        lines: List[str] = []
        for g in self.gates:
            out = self.wire_names[g.out_wire]
            lines.append(f"{out} = ({fmt_lf(g.left)}) * ({fmt_lf(g.right)})")
        lines.append(f"out = {fmt_lf(self.output)}")
        return "\n".join(lines)

    @property
    def mul_count(self) -> int:
        return len(self.gates)


class ChainBuilder:
    """Helper for incrementally building a PolynomialChain."""

    def __init__(self, field: Field):
        self.field = field
        self.wire_names: List[str] = ["1", "x"]
        self.gates: List[MulGate] = []
        # Gadget output values registered as let-bound ("materialized") sums,
        # for share-aware addition counting (the paper's ledger convention:
        # a let-bound subexpression used more than once is charged once).
        self.marked_values: List[AffineForm] = []

    def mark_value(self, form: "AffineForm") -> "AffineForm":
        self.marked_values.append(form)
        return form

    @property
    def x(self) -> AffineForm:
        return AffineForm.wire(1)

    def wire(self, w: int, coef: int = 1) -> AffineForm:
        return AffineForm.wire(w, coef=coef)

    def const(self, c: Number) -> AffineForm:
        return AffineForm.const_only(self.field.coerce(c))

    def add_gate(self, left: AffineForm, right: AffineForm, name: Optional[str] = None) -> int:
        out_wire = len(self.wire_names)
        self.gates.append(MulGate(left=left, right=right, out_wire=out_wire))
        self.wire_names.append(name or f"y{out_wire - 2}")
        return out_wire

    def mul(self, left: AffineForm, right: AffineForm, name: Optional[str] = None) -> AffineForm:
        return AffineForm.wire(self.add_gate(left, right, name=name))

    def finalize(self, output: AffineForm) -> PolynomialChain:
        return PolynomialChain(
            wire_names=list(self.wire_names),
            gates=list(self.gates),
            output=output,
            field=self.field,
        )


def _paper_square_diff(builder: ChainBuilder, A: AffineForm, B: AffineForm, name: Optional[str] = None) -> AffineForm:
    """One-multiplication helper: (A+B)(A-B)."""

    field = builder.field
    return builder.mul(A.add(B, field), A.sub(B, field), name=name)


def _paper_H2(builder: ChainBuilder, alpha0: Number, alpha1: Number) -> AffineForm:
    """
    Base known power:
        H_2[α0,α1](x) = (x + α1)x + α0
    """

    field = builder.field
    x = builder.x
    t = builder.mul(x.add_const(field.coerce(alpha1), field), x)
    return t.add_const(field.coerce(alpha0), field)


def _paper_q3(builder: ChainBuilder, alpha0: Number, alpha1: Number, alpha2: Number, H2: AffineForm) -> AffineForm:
    """
    Q_3[α0,α1,α2](x, H2) = (x + α2)(H2 + α1) + α0

    This uses 1 multiplication, assuming H2 is already available.
    """

    field = builder.field
    x = builder.x
    a0 = field.coerce(alpha0)
    a1 = field.coerce(alpha1)
    a2 = field.coerce(alpha2)
    t = builder.mul(x.add_const(a2, field), H2.add_const(a1, field))
    return t.add_const(a0, field)


def _paper_P5(builder: ChainBuilder, alpha: List[Number]) -> AffineForm:
    """
    Paper base construction for degree 5 (3 multiplications):

      P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0

    This is the degree-5 base used by the paper family `P_n[α]` and matches the
    `n==5` chain in `_compile_paper_monic` (when the polynomial coefficients are
    interpreted as α-parameters).
    """

    field = builder.field
    if len(alpha) != 5:
        raise ValueError(f"P5 needs 5 params, got {len(alpha)}")
    a0, a1, a2, a3, a4 = (field.coerce(alpha[i]) for i in range(5))

    x = builder.x
    x2 = builder.mul(x, x)
    z = builder.mul(x2.add_const(a4, field), x2.add(x, field).add_const(a3, field))
    w = builder.mul(x.add_const(a2, field), z.add_const(a1, field))
    return w.add_const(a0, field)


def _paper_P7(builder: ChainBuilder, alpha: List[Number]) -> AffineForm:
    """
    Septic base construction (degree 7, 4 multiplications).

    This matches the "paper-style" chain used by `_compile_paper_monic` for n=7
    (where it is shown to be decodable in characteristic != 2).

        y = x * (x + α6)
        z = (α5 + x + y) * (α4 + x)
        w = (α3 + z) * x
        v = (α2 + x + z) * (α1 + w)
        P7 = α0 + y + w + v
    """

    if len(alpha) != 7:
        raise ValueError(f"P7 needs 7 params, got {len(alpha)}")

    field = builder.field
    alpha = [field.coerce(a) for a in alpha]
    x = builder.x

    y = builder.mul(x, x.add_const(alpha[6], field))
    z = builder.mul(x.add(y, field).add_const(alpha[5], field), x.add_const(alpha[4], field))
    w = builder.mul(z.add_const(alpha[3], field), x)
    v = builder.mul(x.add(z, field).add_const(alpha[2], field), w.add_const(alpha[1], field))
    return y.add(w, field).add(v, field).add_const(alpha[0], field)


def _paper_P7_char2(builder: ChainBuilder, u: List[Number]) -> AffineForm:
    """
    Septic base construction tailored for characteristic 2 (degree 7, 4 multiplications).

    This is the chain from `fast-polyhash.tex` (Polynomial for characteristic 2):

        y = (x + u6) * x
        z = (x + u5) * (y + u4)
        w = (z + u3) * z
        v = (x + u1) * (y + w + u2)
        P = v + u0

    All additions/subtractions are the same in characteristic 2; we spell everything
    using `add`/`add_const`.

    Notes:
    - Decoding (coeffs -> u) for this family requires Frobenius inverse (square roots)
      in general characteristic-2 fields.
    """

    if len(u) != 7:
        raise ValueError(f"P7_char2 needs 7 params, got {len(u)}")

    field = builder.field
    u = [field.coerce(a) for a in u]
    x = builder.x

    y = builder.mul(x.add_const(u[6], field), x, name="y")
    z = builder.mul(x.add_const(u[5], field), AffineForm.wire(y).add_const(u[4], field), name="z")
    w = builder.mul(AffineForm.wire(z).add_const(u[3], field), AffineForm.wire(z), name="w")
    v = builder.mul(
        x.add_const(u[1], field),
        AffineForm.wire(y).add(AffineForm.wire(w), field).add_const(u[2], field),
        name="v",
    )
    return AffineForm.wire(v).add_const(u[0], field)


def _field_mul_int(field: Field, value: Number, k: int) -> Number:
    """Multiply a field element by an integer using additions (no field-mul)."""

    if k == 0:
        return field.zero()
    if k < 0:
        return field.neg(_field_mul_int(field, value, -k))

    acc = field.zero()
    addend = field.coerce(value)
    kk = k
    while kk:
        if kk & 1:
            acc = field.add(acc, addend)
        kk >>= 1
        if kk:
            addend = field.add(addend, addend)
    return acc


def _affine_scale_int(field: Field, lf: AffineForm, k: int) -> AffineForm:
    if k == 0:
        return AffineForm.const_only(field.zero())
    const = _field_mul_int(field, lf.const, k)
    terms: Dict[int, int] = {}
    for w, c in lf.terms.items():
        cc = c * k
        if cc != 0:
            terms[w] = cc
    return AffineForm(const, terms, ("scale", lf, k))


def _paper_T(
    builder: ChainBuilder,
    k: int,
    l: int,
    alpha: List[Number],
    Hs: List[AffineForm],
    tilde_H_2l: AffineForm,
) -> Tuple[AffineForm, AffineForm, List[AffineForm], AffineForm]:
    """
    Construct the pair (T^{(1)}_{k,2^l}, T^{(2)}_{k,2^l}) from sections/constructions.tex.

    This is the core subroutine used for the 4k+1 family; it also produces (as a
    byproduct) higher known powers H_{2^{l+1}} / \\tilde H_{2^{l+1}} in the
    recursive cases.

    Args:
        k: positive integer
        l: >= 1 (so 2^l >= 2)
        alpha: parameter list of length (k-1)*2^l
        Hs: known powers list with Hs[i] = H_{2^i}, Hs[0]=x, len(Hs) >= l+1
        tilde_H_2l: the \\tilde H_{2^l} input for the second component

    Returns:
        (T1, T2, Hs_out, tilde_H_out) where:
          - T1, T2 are the constructed polynomials
          - Hs_out extends Hs with any newly constructed H_{2^i}
          - tilde_H_out is the corresponding \\tilde H_{2^{l'}} at the output scale
    """

    field = builder.field
    two = field.add(field.one(), field.one())
    is_char2 = field.is_zero(two)
    if k < 1:
        raise ValueError("T requires k >= 1")
    if l < 1:
        raise ValueError("T requires l >= 1")
    if len(Hs) <= l:
        raise ValueError(f"T(k={k},l={l}) requires Hs up to index {l} (H_{{2^{l}}})")

    block = 1 << l
    need = (k - 1) * block
    if len(alpha) != need:
        raise ValueError(f"T(k={k},l={l}) needs {(k-1)}*2^{l}={need} alpha params, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    if k == 1:
        # Base: T^{(1)} = H_{2^l}, T^{(2)} = \\tilde H_{2^l}.
        return Hs[l], tilde_H_2l, Hs, tilde_H_2l

    # Even k
    if (k % 2) == 0:
        # Split: prefix params for recursion, tail block for constructing new powers.
        rec_len = (k // 2 - 1) * (2 * block)
        tail = alpha[rec_len:]
        rec_params = alpha[:rec_len]
        if len(tail) != block:
            raise ValueError("internal error: T even tail length mismatch")

        # Special case: l = 1 (paper Algorithm `alg:constr-Tk2l-base`, even-k branch).
        if l == 1:
            # H4 = (H2 + (x + a1))(H2 - (x + a1)) + a0
            # tilde_H4 = H4 + (tilde_H2-H2)
            a0, a1 = tail[0], tail[1]
            x = builder.x
            # In all paper call-sites, tilde_H2 is a scalar shift of H2.
            delta = tilde_H_2l.sub(Hs[1], field)
            can_fast_shift = not delta.terms
            delta_int: Optional[int] = None
            if can_fast_shift:
                try:
                    delta_int = int(delta.const)  # works for GF(p) elements represented as ints
                except Exception:
                    delta_int = None
            if is_char2:
                # Characteristic-2 replacement: H4 = H2 * (H2 + (x + a1)) + a0.
                #
                # This avoids the `(A+B)(A-B)` square-difference gadget, which collapses
                # in char 2, and is decodable given H2 by polynomial division.
                H4 = builder.mul(Hs[1], Hs[1].add(x.add_const(a1, field), field)).add_const(a0, field)
                if delta_int is not None:
                    # In char 2: (H2+δ)(H2+δ+x+a1) = H2(H2+x+a1) + δ(x+a1) + δ^2.
                    delta_sq = field.mul(delta.const, delta.const)
                    delta_x_plus = _affine_scale_int(field, x.add_const(a1, field), delta_int)
                    tilde_H4 = H4.add(delta_x_plus, field).add_const(delta_sq, field)
                else:
                    tilde_H4 = builder.mul(
                        tilde_H_2l, tilde_H_2l.add(x.add_const(a1, field), field)
                    ).add_const(a0, field)
            else:
                t_plus = Hs[1].add(x.add_const(a1, field), field)
                t_minus = Hs[1].sub(x.add_const(a1, field), field)
                H4 = builder.mul(t_plus, t_minus).add_const(a0, field)
                if not can_fast_shift:
                    raise ValueError("The shared l=1 base requires tilde_H2-H2 to be scalar")
                # This is the exact-count repair: the shifted quartic is a
                # scalar shift of the first quartic, so no second product is
                # needed.
                tilde_H4 = H4.add(delta, field)
            Hs_next = list(Hs)
            if len(Hs_next) <= 2:
                Hs_next.extend([AffineForm.const_only(field.zero())] * (3 - len(Hs_next)))
            Hs_next[2] = H4
            return _paper_T(builder, k // 2, l + 1, rec_params, Hs_next, tilde_H4)

        # Main even case: l >= 2.
        half = 1 << (l - 1)
        q_hi = _paper_Q_known_powers(builder, l - 1, tail[half + 1 :], Hs[: l - 1])
        q_lo = _paper_Q_known_powers(builder, l - 1, tail[1:half], Hs[: l - 1])

        S1_1 = Hs[l - 1].add(q_hi, field)
        S1_2 = q_lo
        if is_char2:
            # Char-2 replacement: H_next = H * (H + S1_1) + S1_2.
            H_next = builder.mul(Hs[l], Hs[l].add(S1_1, field)).add(S1_2, field)
        else:
            H_next = builder.mul(Hs[l].add(S1_1, field), Hs[l].sub(S1_1, field)).add(S1_2, field)

        S2_1 = Hs[l - 1].add_const(tail[half], field)
        S2_2 = tail[0]
        if is_char2:
            tilde_next = builder.mul(tilde_H_2l, tilde_H_2l.add(S2_1, field)).add_const(S2_2, field)
        else:
            tilde_next = (
                builder.mul(tilde_H_2l.add(S2_1, field), tilde_H_2l.sub(S2_1, field))
                .add_const(S2_2, field)
            )

        Hs_next = list(Hs)
        if len(Hs_next) <= l + 1:
            Hs_next.extend([AffineForm.const_only(field.zero())] * (l + 2 - len(Hs_next)))
        Hs_next[l + 1] = H_next
        return _paper_T(builder, k // 2, l + 1, rec_params, Hs_next, tilde_next)

    # Odd k
    m = (k - 1) // 2
    if l == 2:
        # Special case: k odd, l = 2 (paper Algorithm `alg:constr-Tk2l-base`, odd-k branch).
        #
        # Layout: head block (size 4) + mid (for recursion) + tail block (size 4).
        if block != 4:
            raise ValueError("internal error: expected block=4 for l=2")

        head = alpha[:4]
        tail = alpha[-4:]
        mid = alpha[4:-4]

        # Tail parameters:
        #   tail[0]=α_{4k-8} : shift from H8 to tilde_H8
        #   tail[1]=α_{4k-7} : S1_3
        #   tail[2]=α_{4k-6} : S1_2 shift in (x+α)
        #   tail[3]=α_{4k-5} : shift in S1_1 = H2 + (x+α)
        next_shift, s1_3, s1_2_shift, s1_1_shift = tail[0], tail[1], tail[2], tail[3]

        # First-branch (unshifted) auxiliaries:
        #   S1_1 = H2 + (x + s1_1_shift)
        #   S1_2 = x + s1_2_shift
        #   S1_3 = s1_3
        S1_1 = Hs[1].add(builder.x.add_const(s1_1_shift, field), field)
        core = Hs[2].add(S1_1, field)
        S1_2 = builder.x.add_const(s1_2_shift, field)
        H8 = builder.mul(core.add(S1_2, field), core.sub(S1_2, field)).add_const(s1_3, field)

        Hs_next = list(Hs)
        if len(Hs_next) <= 3:
            Hs_next.extend([AffineForm.const_only(field.zero())] * (4 - len(Hs_next)))
        Hs_next[3] = H8

        # The input quartics differ by a scalar rho.  Put S2_1=S1_1-rho,
        # S2_2=S1_2 and S2_3=S1_3+next_shift.  The square-difference cores
        # are then identical, so tilde_H8=H8+next_shift shares the H8 gate.
        rho = tilde_H_2l.sub(Hs[2], field)
        if rho.terms:
            raise ValueError("The shared odd l=2 base requires tilde_H4-H4 to be scalar")
        tilde_H8 = H8.add_const(next_shift, field)

        T1_rec, T2_rec, Hs_out, tilde_out = _paper_T(builder, m, l + 1, mid, Hs_next, tilde_H8)

        # Q3(head[1..3]) is the additive term on the first branch.
        q3 = _paper_Q_known_powers(builder, 2, head[1:], Hs[:2])

        # (H4 - (k-1)S1_1) * T1_rec + Q3
        factor1 = Hs[2].sub(_affine_scale_int(field, S1_1, k - 1), field)
        T1 = builder.mul(factor1, T1_rec).add(q3, field)

        # (tilde_H4 - (k-1)S2_1) * T2_rec + α0.  With S2_1 = S1_1 - rho and
        # tilde_H4 = H4 + rho the second factor is a scalar shift of the
        # first, tilde_H4 - (k-1)S2_1 = factor1 + k*rho (eq. shared-factor in
        # sections/addition_accounting.tex), so neither tilde_H4 nor S2_1 is
        # materialized: one addition instead of three.
        factor2 = factor1.add_const(_field_mul_int(field, rho.const, k), field)
        T2 = builder.mul(factor2, T2_rec).add_const(head[0], field)
        return T1, T2, Hs_out, tilde_out

    if l < 3:
        raise ValueError("T odd case requires l >= 3 (or special l=2)")

    # Main odd case: l >= 3.
    # Layout: head block (size 2^l) + mid (for recursion) + tail block (size 2^l).
    head = alpha[:block]
    tail = alpha[-block:]
    mid = alpha[block:-block]

    half = 1 << (l - 1)
    quarter = 1 << (l - 2)

    # H_{2^{l+1}} = ((H_{2^l} + S1_1) + S1_2) * ((H_{2^l} + S1_1) - S1_2) + S1_3
    q_hi = _paper_Q_known_powers(builder, l - 1, tail[half + 1 :], Hs[: l - 1])
    S1_1 = Hs[l - 1].add(q_hi, field)

    q_mid = _paper_Q_known_powers(builder, l - 2, tail[quarter + 1 : half], Hs[: l - 2])
    S1_2 = Hs[l - 2].add(q_mid, field)

    S1_3 = _paper_Q_known_powers(builder, l - 2, tail[1:quarter], Hs[: l - 2])

    base = Hs[l].add(S1_1, field)
    H_next = builder.mul(base.add(S1_2, field), base.sub(S1_2, field)).add(S1_3, field)

    S2_1 = Hs[l - 1].add_const(tail[half], field)
    S2_2 = Hs[l - 2].add_const(tail[quarter], field)
    S2_3 = tail[0]
    base2 = tilde_H_2l.add(S2_1, field)
    tilde_next = builder.mul(base2.add(S2_2, field), base2.sub(S2_2, field)).add_const(S2_3, field)

    Hs_next = list(Hs)
    if len(Hs_next) <= l + 1:
        Hs_next.extend([AffineForm.const_only(field.zero())] * (l + 2 - len(Hs_next)))
    Hs_next[l + 1] = H_next

    T1_rec, T2_rec, Hs_out, tilde_out = _paper_T(builder, m, l + 1, mid, Hs_next, tilde_next)

    q_low = _paper_Q_known_powers(builder, l, head[1:], Hs[:l])
    factor1 = Hs[l].sub(_affine_scale_int(field, S1_1, k - 1), field)
    T1 = builder.mul(factor1, T1_rec).add(q_low, field)

    factor2 = tilde_H_2l.sub(_affine_scale_int(field, S2_1, k - 1), field)
    T2 = builder.mul(factor2, T2_rec).add_const(head[0], field)
    return T1, T2, Hs_out, tilde_out


def _paper_Q_2lp1k_minus_1(
    builder: ChainBuilder,
    k: int,
    l: int,
    alpha: List[Number],
    Hs: List[AffineForm],
) -> AffineForm:
    """
    Implement the construction in sections/constructions.tex, subsection
    “Constructions for 4k+1 and 4k+3 using known powers”.

    This constructs the polynomial
        Q_{2^{l+1}k + (2^l - 1)}(x, H2, ..., H_{2^l})
    given access to H2..H_{2^l}.

    See `_paper_Q_2lp1k_minus_1_with_powers` for the exact parameter mapping used
    in this implementation (which follows the paper’s intent, fixing only obvious
    index typos).
    """

    out, _, _ = _paper_Q_2lp1k_minus_1_with_powers(builder, k, l, alpha, Hs)
    return builder.mark_value(out)


def _paper_Q_2lp1k_minus_1_with_powers(
    builder: ChainBuilder,
    k: int,
    l: int,
    alpha: List[Number],
    Hs: List[AffineForm],
) -> Tuple[AffineForm, List[AffineForm], AffineForm]:
    """
    Like `_paper_Q_2lp1k_minus_1`, but also returns the (possibly extended) list of
    known powers produced along the way, plus the terminal `\\tilde H` from the
    internal `T` call.

    Returns:
        (Q, Hs_out, tilde_out)
    """

    field = builder.field
    if k < 0 or l < 1:
        raise ValueError("Q_2lp1k_minus_1 requires k>=0 and l>=1")
    # For k=0 we only need H2..H_{2^{l-1}} (since we dispatch to Q_{2^l-1}).
    # For k>0 we additionally need H_{2^l}.
    if k == 0:
        if len(Hs) < l:
            raise ValueError(
                f"Q_2lp1k_minus_1(k=0,l={l}) requires Hs up to index {l-1} (H_{{2^{l-1}}})"
            )
    else:
        if len(Hs) <= l:
            raise ValueError(f"Q_2lp1k_minus_1 requires Hs up to index {l} (H_{{2^{l}}})")

    deg = (1 << (l + 1)) * k + ((1 << l) - 1)
    if deg == 0:
        if len(alpha) != 1:
            raise ValueError("degree-0 Q requires 1 parameter")
        z = AffineForm.const_only(field.coerce(alpha[0]))
        return z, list(Hs), z

    if len(alpha) != deg:
        raise ValueError(f"Q_2lp1k_minus_1(k={k},l={l}) needs {deg} alpha params, got {len(alpha)}")

    alpha = [field.coerce(a) for a in alpha]

    if k == 0:
        # Q_{2^l-1} is the known-powers construction.
        out = _paper_Q_known_powers(builder, l, alpha, Hs[:l])
        return out, list(Hs), Hs[0]

    if l == 1:
        # Special case needed for the `8k+3` induction: build `Q_{4k+1}(x,H2)` from
        # `T_{2k,2}` using only a shifted quadratic input and a single top-level
        # `(x+β0)` extraction.
        #
        # Parameter layout (deg = 4k+1):
        #   - α0..α_{4k-3}   : T-params for `T_{2k,2}`
        #   - α_{4k-2}       : shift for `\\tilde H2 = \\hat H2 + α_{4k-2}`
        #   - α_{4k-1}       : quadratic shift `\\hat H2 = H2 + α_{4k-1}`
        #   - α_{4k}         : extraction parameter `β0` in `(x+β0)S1 + S2`
        field = builder.field
        deg = 4 * k + 1
        if len(alpha) != deg:
            raise ValueError(f"Q_2lp1k_minus_1(k={k},l=1) needs {deg} alpha params, got {len(alpha)}")
        if len(Hs) < 2:
            raise ValueError("Q_2lp1k_minus_1(l=1) requires Hs=[x,H2]")
        alpha = [field.coerce(a) for a in alpha]

        t_params = alpha[: 4 * k - 2]
        tilde_shift = alpha[4 * k - 2]
        hat_shift = alpha[4 * k - 1]
        beta0 = alpha[4 * k]

        x = Hs[0]
        H2 = Hs[1]
        H_hat = H2.add_const(hat_shift, field)
        tilde_H2 = H_hat.add_const(tilde_shift, field)

        S1, S2, Hs_out, tilde_out = _paper_T(builder, 2 * k, 1, t_params, [x, H_hat], tilde_H2)
        out = builder.mark_value(builder.mul(builder.x.add_const(beta0, field), S1).add(S2, field))
        return out, Hs_out, tilde_out

    block = 1 << l
    a_alpha = alpha[: block - 2]  # α0..α_{2^l-3}
    t_start = block - 2
    shift_idx = (1 << (l + 1)) * k - 2  # α_{2^{l+1}k-2}
    t_params = alpha[t_start:shift_idx]  # α_{2^l-2}..α_{2^{l+1}k-3}
    shift = alpha[shift_idx]

    # Q_{2^{l-1}-1} parameters: length 2^{l-1}-1.
    # For l=1 this is 0, i.e. Q_0 is treated as the zero polynomial here.
    qhat_start = shift_idx + 1
    qhat_len = (1 << (l - 1)) - 1
    qhat_params = alpha[qhat_start : qhat_start + qhat_len]

    beta_start = qhat_start + qhat_len
    beta_len = (1 << (l - 1)) + 1
    beta_params = alpha[beta_start : beta_start + beta_len]
    if len(beta_params) != beta_len or (beta_start + beta_len) != len(alpha):
        raise ValueError("internal error: beta param count mismatch in Q_2lp1k_minus_1")

    # \\hat H_{2^l} = H_{2^l} + Q_{2^{l-1}-1}(qhat_params)
    if l == 1:
        H_hat = Hs[1]
    else:
        qhat = _paper_Q_known_powers(builder, l - 1, qhat_params, Hs[: l - 1])
        H_hat = Hs[l].add(qhat, field)

    # Run T_{2k,2^l} with H_{2^l} replaced by \\hat H_{2^l}.
    Hs_hat = list(Hs)
    Hs_hat[l] = H_hat
    need_t = (2 * k - 1) * block
    if len(t_params) != need_t:
        raise ValueError(f"internal error: expected {need_t} T-params, got {len(t_params)}")
    S1, S2, Hs_out, tilde_out = _paper_T(
        builder, 2 * k, l, t_params, Hs_hat, H_hat.add_const(shift, field)
    )

    # Final fill: A_{2^{l-1}} on (S1,S2).
    A_l = l - 1
    A_alpha_need = (1 << (A_l + 1)) - 2  # == 2^l - 2 (and 0 when l=1)
    if len(a_alpha) != A_alpha_need:
        raise ValueError("internal error: A_alpha length mismatch in Q_2lp1k_minus_1")

    A_beta = [field.zero() for _ in range((1 << A_l) + 1)]  # β0..β_{2^{l-1}}
    for i, v in enumerate(beta_params):
        A_beta[(1 << A_l) - i] = v

    out = builder.mark_value(_paper_A_fill(builder, A_l, list(a_alpha), A_beta, S1, S2, Hs[: A_l + 1]))
    return out, Hs_out, tilde_out


def _paper_barQ_4k_plus_1_with_H4(
    builder: ChainBuilder, k: int, alpha: List[Number], H2: AffineForm
) -> Tuple[AffineForm, AffineForm]:
    """
    Convenience wrapper for the frequently used `\\bar{Q}_{4k+1}(x,H2)` calls in
    sections/constructions.tex (notably the `8k+3` induction step).

    In sections/constructions.tex this is the gadget used in the `8k+3` induction step:
    it must compute a degree-(4k+1) polynomial from (x,H2) and additionally
    provide an `H4`-like monic degree-4 polynomial as a byproduct.

    We implement this using the paper’s `Q_{4k+1}(x,H2)` construction
    (i.e. the `l=1` instance of the “4k+1 using known powers” family), which
    naturally produces such an `H4` byproduct during its internal `T` recursion.
    """

    q, powers_out = _paper_barQ_4k_plus_1_with_powers(builder, k=k, alpha=alpha, H2=H2)
    if len(powers_out) <= 2:
        raise ValueError("internal error: expected an H4 byproduct in barQ_{4k+1}")
    return q, powers_out[2]


class _GoodPolyVarSource:
    """
    Internal helper: produces “variables” used as additive shifts in good-polynomial
    constructions.

    Depending on the construction, these “variables” may be constants (fresh α_i),
    or higher-degree polynomials built from blocks of α_i's.
    """

    def next(self) -> AffineForm:
        raise NotImplementedError


class _GoodPolyConstVarSource(_GoodPolyVarSource):
    def __init__(self, builder: ChainBuilder, alpha: List[Number]):
        self._builder = builder
        self._field = builder.field
        self._alpha = [self._field.coerce(a) for a in alpha]
        self._i = 0

    @property
    def remaining(self) -> int:
        return len(self._alpha) - self._i

    def next(self) -> AffineForm:
        if self._i >= len(self._alpha):
            raise ValueError("ran out of good-poly parameters")
        v = self._alpha[self._i]
        self._i += 1
        return self._builder.const(v)


class _GoodPolyBlockVarSource(_GoodPolyVarSource):
    """
    A “block-variable” source: each `next()` returns a *degree-m* good polynomial,
    consuming exactly m underlying constant parameters.

    This is the mechanism used in Jakob's experimental constructions (tools/holes3.py):
    higher-level polynomials treat entire degree-m blocks as “variables”, while the
    blocks themselves are built recursively from the underlying α stream.
    """

    def __init__(
        self,
        builder: ChainBuilder,
        m: int,
        base_powers: List[AffineForm],
        base_source: _GoodPolyVarSource,
    ):
        self._builder = builder
        self._m = m
        self._base_powers = list(base_powers)
        self._base_source = base_source

    def next(self) -> AffineForm:
        poly, _powers_out = _goodpoly_k_given_powers(self._builder, self._m, self._base_powers, self._base_source)
        return poly


def _goodpoly_k_given_powers(
    builder: ChainBuilder, k: int, powers: List[AffineForm], ss: _GoodPolyVarSource
) -> Tuple[AffineForm, List[AffineForm]]:
    """
    Build a “good polynomial” of (scaled) degree k from a list of available “powers”.

    This is a direct transliteration of the construction used in `tools/holes3.py`
    (with the bookkeeping removed). It is used to realize the paper’s barred
    `\\bar{Q}` gadget family in a way that composes correctly in the `8k+3` and
    `8k+7` induction steps.

    Args:
        k: positive integer (the target degree multiplier relative to `powers[0]`)
        powers: list [P0, P1, ...] with (intended) degree pattern
               deg(P_{i+1}) = 2*deg(P_i)
        ss: variable source providing additive shifts (constants or blocks)

    Returns:
        (poly, powers_out) where powers_out may extend `powers` with newly created
        “known powers” as byproducts.
    """

    field = builder.field
    if k < 1:
        raise ValueError("goodpoly_k_given_powers requires k>=1")
    if not powers:
        raise ValueError("goodpoly_k_given_powers: ran out of power polynomials")

    # Base cases.
    if k == 1:
        var = ss.next()
        return powers[0].add(var, field), list(powers)

    if k == 2:
        if len(powers) < 2:
            raise ValueError("goodpoly_k_given_powers(k=2) requires powers[1]")
        var = ss.next()
        return powers[1].add(var, field), list(powers)

    # Odd k.
    if (k % 2) == 1:
        if (k % 4) == 1:
            # We recurse on k-1 (a multiple of 4) and then do one (x+var) multiply.
            P, powers2 = _goodpoly_k_given_powers(builder, k - 1, powers, ss)

            if (k % 8) == 5:
                # The `k=5` case is a small base tweak in the original construction.
                if k == 5:
                    R = ss.next()
                else:
                    if len(powers2) < 3:
                        raise ValueError("goodpoly_k_given_powers: expected powers2[2:] to exist")
                    R, _ = _goodpoly_k_given_powers(builder, k // 4, powers2[2:], ss)
            elif (k % 8) == 1:
                if len(powers2) < 2:
                    raise ValueError("goodpoly_k_given_powers: expected powers2[1:] to exist")
                R, _ = _goodpoly_k_given_powers(builder, k // 2, powers2[1:], ss)
            else:
                raise ValueError("internal error: k%4==1 implies k%8 in {1,5}")

        elif (k % 4) == 3:
            # Recurse at the “next power” scale.
            if len(powers) < 2:
                raise ValueError("goodpoly_k_given_powers(k%4==3) requires powers[1]")
            P, powers2 = _goodpoly_k_given_powers(builder, k // 2, powers[1:], ss)
            powers2 = [powers[0]] + powers2
            R, _ = _goodpoly_k_given_powers(builder, k // 2, powers[1:], ss)
        else:
            raise ValueError("internal error: odd k must be 1 or 3 mod 4")

        var = ss.next()
        T = builder.mul(P, powers[0].add(var, field)).add(R, field)
        return T, powers2

    # k divisible by 4.
    if (k % 4) == 0:
        if len(powers) < 2:
            raise ValueError("goodpoly_k_given_powers(k%4==0) requires at least 2 powers")

        # The construction keeps only the first two powers at this scale, and
        # synthesizes higher ones as needed.
        powers2: List[AffineForm] = list(powers[:2])

        P, _ = _goodpoly_k_given_powers(builder, 2, powers2, ss)
        kk = k // 2
        m = 2
        while (kk % 2) == 0:
            Q, _ = _goodpoly_k_given_powers(builder, m // 2, powers2[:2], ss)
            R, _ = _goodpoly_k_given_powers(builder, m // 2, powers2[:2], ss)
            P = builder.mul(P.add(Q, field), P.sub(Q, field)).add(R, field)
            powers2 = powers2 + [P]
            m *= 2
            kk //= 2

        return _goodpoly_four_k_builder(builder, P, kk, m, powers2, ss)

    # The original construction expects this to never happen (other than k=2 handled above).
    raise ValueError(f"goodpoly_k_given_powers: unsupported k={k} (k%4==2)")


def _goodpoly_four_k_builder(
    builder: ChainBuilder,
    P: AffineForm,
    k: int,
    m: int,
    powers: List[AffineForm],
    ss: _GoodPolyVarSource,
) -> Tuple[AffineForm, List[AffineForm]]:
    """
    Helper used by `_goodpoly_k_given_powers` for the “k divisible by 4” branch.

    This is again a transliteration of `tools/holes3.py` with only the polynomial
    expressions retained.
    """

    field = builder.field
    if k < 1:
        raise ValueError("goodpoly_four_k_builder requires k>=1")

    if k == 1:
        return P, list(powers)

    # k odd
    if (k % 2) == 1:
        if m < 4:
            raise ValueError("goodpoly_four_k_builder expects m>=4 when k is odd")

        Q, _ = _goodpoly_k_given_powers(builder, m // 4, powers[:2], ss)
        R, _ = _goodpoly_k_given_powers(builder, m // 4, powers[:2], ss)
        S, _ = _goodpoly_k_given_powers(builder, m // 2, powers[:2], ss)

        P_plus_S = P.add(S, field)
        T = builder.mul(P_plus_S.add(Q, field), P_plus_S.sub(Q, field)).add(R, field)

        # Replace the last “power” by the shifted one.
        P_shift = P.sub(_affine_scale_int(field, S, k - 1), field)
        powers_here = list(powers)
        if not powers_here:
            raise ValueError("internal error: empty powers list in goodpoly_four_k_builder")
        powers_here[-1] = P_shift
        powers_here = powers_here + [T]

        # Create a block-variable stream at scale m (each var is a degree-m good poly).
        old_powers = powers_here[:2]
        new_ss = _GoodPolyBlockVarSource(builder, m, old_powers, ss)

        # Recurse and then fill the remaining piece (R2) using the new powers.
        T2, powers2 = _goodpoly_four_k_builder(builder, T, k // 2, m, powers_here, ss)

        if (k % 4) == 1:
            if (k % 8) == 5:
                R2, _ = _goodpoly_k_given_powers(builder, k // 4, powers2[len(powers_here) :], new_ss)
            elif (k % 8) == 1:
                R2, _ = _goodpoly_k_given_powers(builder, k // 2, powers2[len(powers_here) - 1 :], new_ss)
            else:
                raise ValueError("internal error: k%4==1 implies k%8 in {1,5}")
        else:
            # k % 4 == 3
            R2, _ = _goodpoly_k_given_powers(builder, k // 2, powers2[len(powers_here) - 1 :], new_ss)

        out = builder.mul(T2, P_shift).add(R2, field)
        return out, powers2

    # k even
    # Block-variable stream at scale m.
    new_ss = _GoodPolyBlockVarSource(builder, m, powers[:2], ss)

    new_powers = list(powers[-2:])
    new_m = 2
    kk = k
    PP = P
    while (kk % 2) == 0:
        Q, _ = _goodpoly_k_given_powers(builder, new_m // 2, new_powers[:2], new_ss)
        R, _ = _goodpoly_k_given_powers(builder, new_m // 2, new_powers[:2], new_ss)
        PP = builder.mul(PP.add(Q, field), PP.sub(Q, field)).add(R, field)
        new_powers = new_powers + [PP]
        new_m *= 2
        kk //= 2

    out, powers2 = _goodpoly_four_k_builder(builder, PP, kk, new_m, new_powers, new_ss)
    return out, list(powers[:-2]) + powers2


def _paper_barQ_4k_plus_1_with_powers(
    builder: ChainBuilder, k: int, alpha: List[Number], H2: AffineForm
) -> Tuple[AffineForm, List[AffineForm]]:
    field = builder.field
    if k < 1:
        raise ValueError("barQ_{4k+1} requires k>=1")
    deg = 4 * k + 1
    if len(alpha) != deg:
        raise ValueError(f"barQ_{{4k+1}} needs {deg} parameters, got {len(alpha)}")

    # Realize \\bar{Q}_{4k+1}(x,H2) using Jakob's “good polynomial” construction
    # (good-polynomials.tex / tools/holes3.py), instantiated at base powers
    #   powers = [x, H2].
    #
    # Key properties needed by sections/constructions.tex:
    #   - uses exactly (4k+1)//2 = 2k multiplications given (x,H2),
    #   - produces a monic degree-4 polynomial (H4) as a byproduct (powers_out[2]),
    #   - yields a polynomially decodable (constant-Jacobian) parameterization.
    ss = _GoodPolyConstVarSource(builder, alpha)
    q, powers_out = _goodpoly_k_given_powers(builder, deg, [builder.x, H2], ss)
    if ss.remaining != 0:
        raise ValueError("internal error: goodpoly var source did not consume all parameters")
    return q, powers_out


def _paper_barQ_odd_with_H2(
    builder: ChainBuilder, deg: int, alpha: List[Number], H2: AffineForm
) -> AffineForm:
    """
    A concrete definition of the (otherwise undefined) `\\bar{Q}_deg` family used in sections/constructions.tex.

    Definition:
      - If deg = 4m+1:   \\bar{Q}_{4m+1} := Q_{4m+1}(x, H2).
      - If deg = 4m+3:   \\bar{Q}_{4m+3} := (H2 + α_{4m+1}) * \\bar{Q}_{4m+1} + α_{4m+2}.

    This matches the text’s intent that these constructions only require access to H2/H4
    (H4 is a byproduct of the `Q_{4m+1}` call for m>0).
    """

    field = builder.field
    if deg < 1 or (deg % 2) == 0:
        raise ValueError("barQ requires odd deg >= 1")
    if len(alpha) != deg:
        raise ValueError(f"barQ_{deg} needs {deg} alpha params, got {len(alpha)}")

    alpha = [field.coerce(a) for a in alpha]

    if deg == 1:
        return builder.x.add_const(alpha[0], field)

    if (deg % 4) == 1:
        m = (deg - 1) // 4
        q, _H4 = _paper_barQ_4k_plus_1_with_H4(builder, k=m, alpha=alpha, H2=H2)
        return q

    # deg = 4m+3.
    m = (deg - 3) // 4
    q = _paper_barQ_odd_with_H2(builder, 4 * m + 1, alpha[: 4 * m + 1], H2)
    shift = alpha[4 * m + 1]
    const = alpha[4 * m + 2]
    prod = builder.mul(H2.add_const(shift, field), q)
    return prod.add_const(const, field)


def _paper_barQ_odd_with_H2_H4_with_powers(
    builder: ChainBuilder, deg: int, alpha: List[Number], Hs_in: List[AffineForm]
) -> Tuple[AffineForm, List[AffineForm]]:
    """
    Concrete realization of the paper's “good polynomial” gadget \\bar{Q}_deg.

    sections/constructions.tex only specifies how \\bar{Q} is *used* (not its exact formula),
    but the surrounding text implies two requirements:
      1) \\bar{Q}_deg should be decodable given (H2,H4), and
      2) it should fit the tight multiplication budget (deg//2 multiplications,
         since (H2,H4) are treated as auxiliary wires).

    We implement the minimal family that matches these constraints and the paper's
    surrounding intent:

      - If deg = 4m+1:  \\bar{Q}_{4m+1} := Q_{4m+1}(x,H2)  (the l=1 known-powers construction)
      - If deg = 4m+3 (m>=1):
            \\bar{Q}_{4m+3} := (H2 + s) * Q_{4m+1}(x,H2) + (H4 + t)
        which costs exactly one extra multiplication on top of Q_{4m+1} and uses
        H4 only additively.

    Returns:
        (barQ, Hs_out) where Hs_out is Hs_in extended with any newly created
        “known powers” produced as byproducts of the internal Q_{4m+1} call.
    """

    field = builder.field
    if deg < 1 or (deg % 2) == 0:
        raise ValueError("barQ requires odd deg >= 1")
    if len(alpha) != deg:
        raise ValueError(f"barQ_{deg} needs {deg} alpha params, got {len(alpha)}")
    if len(Hs_in) < 2:
        raise ValueError("barQ requires Hs_in=[x,H2,...]")

    alpha = [field.coerce(a) for a in alpha]

    # Prefer the paper’s known-powers `Q_deg` construction whenever the required
    # known powers are already available. This matches how \\bar{Q} is used in
    # the induction steps: we thread through the byproduct powers from earlier
    # computations and use them when possible.
    l_need = _v2_positive(deg + 1)
    odd = (deg + 1) >> l_need
    kk = (odd - 1) // 2
    need = l_need + 1 if kk > 0 else l_need
    if len(Hs_in) >= need:
        q, Hs_out, _ = _paper_Q_for_odd_degree_with_powers(builder, deg=deg, alpha=alpha, Hs=Hs_in)
        return q, Hs_out

    if len(Hs_in) < 3:
        raise ValueError("barQ fallback requires H4 (Hs_in[2]) to be available")
    H2 = Hs_in[1]
    H4 = Hs_in[2]

    # Keep the hand-crafted \\bar{Q}_{15} used by the n=31 special case stable.
    if deg == 15:
        return _paper_barQ_15(builder, alpha=alpha, H2=H2, H4=H4), list(Hs_in)

    # Fallback for deg ≡ 7 (mod 8), i.e. deg = 8k+7 (k>=2 here since deg=15 is
    # handled above):
    #
    # Here v2(deg+1) >= 3, so the paper’s `Q_deg` construction would require
    # higher known powers (H8/H16/...) that may not be available from earlier
    # steps. sections/constructions.tex instead assumes the existence of a “good
    # polynomial” gadget \\bar{Q}_{4k+3} that is decodable given only (H2,H4).
    #
    # We realize the required instances using a tight-budget construction based
    # on the paper’s own subroutines:
    #   - synthesize an H8 + \\tilde H8,
    #   - run `T_{k,8}` to get a degree-(8k) compatible pair,
    #   - apply `A_4` to reach degree (8k+7).
    #
    # This keeps the Jacobian determinant constant and fits the exact (deg//2)
    # multiplication budget given (H2,H4).
    if (deg % 8) == 7 and deg >= 23:
        k = (deg - 7) // 8
        out, powers_out = _paper_barQ_8k_plus_7_with_powers(builder, k=k, alpha=alpha, H2=H2, H4=H4)
        Hs_out = list(Hs_in)
        if len(Hs_out) < len(powers_out):
            Hs_out.extend(powers_out[len(Hs_out) :])
        return out, Hs_out

    raise ValueError(f"internal error: no barQ fallback case matched for deg={deg} (need={need}, have={len(Hs_in)})")


def _paper_barQ_odd_with_H2_H4(
    builder: ChainBuilder, deg: int, alpha: List[Number], H2: AffineForm, H4: AffineForm
) -> AffineForm:
    q, _ = _paper_barQ_odd_with_H2_H4_with_powers(builder, deg, alpha, [builder.x, H2, H4])
    return q


def _paper_barQ_15(builder: ChainBuilder, alpha: List[Number], H2: AffineForm, H4: AffineForm) -> AffineForm:
    """
    Concrete construction for \\bar{Q}_{15}(x,H2,H4) used in sections/constructions.tex (Special case 31).

    We implement `\\bar{Q}_{15}` as a direct `A_4` (fill) instance, using only
    `H2` and `H4` plus one internally constructed monic degree-8 polynomial `H8`.

    Total multiplications given H2,H4: 1 (H8) + 6 (A_4) = 7.
    """

    field = builder.field
    if len(alpha) != 15:
        raise ValueError(f"barQ_15 needs 15 parameters, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    x = builder.x

    # Parameter partition:
    #   - 3 params for H8: a,b,c
    #   - 1 param for shifting S2: d
    #   - 6 params for A_4 alpha: α0..α5
    #   - 5 params for A_4 beta:  β0..β4
    a_h8, b_h8, c_h8 = alpha[0], alpha[1], alpha[2]
    d_shift = alpha[3]

    a_alpha = alpha[4:10]
    beta = alpha[10:15]

    # H8 proxy (monic degree 8). We deliberately mix in both `x` and `H2` so the
    # low-degree part has enough structure for the downstream `A_4` fill.
    A = x.add_const(b_h8, field)  # degree 1
    B = H2.add_const(c_h8, field)  # degree 2
    H8 = builder.mul(H4.add(A, field), H4.add(B, field)).add_const(a_h8, field)

    S1 = H8
    S2 = H8.add_const(d_shift, field)
    return _paper_A_fill(builder, 2, a_alpha, beta, S1, S2, [x, H2, H4])


def _paper_barQ_8k_plus_7_with_powers(
    builder: ChainBuilder, k: int, alpha: List[Number], H2: AffineForm, H4: AffineForm
) -> Tuple[AffineForm, List[AffineForm]]:
    """
    Strong construction for \\bar{Q}_{8k+7}(x,H2,H4) (k >= 2).

    This matches the “\\bar Q only needs (H2,H4)” assumption in the induction
    steps, while keeping the Jacobian determinant constant (the property required
    by `tools/test_paper_bijection.py --require-constant`).

    Structure (tight multiplication budget):
      - Build a monic degree-8 power H8 and a shifted \\tilde H8.
      - Use `T_{k,8}` (Algorithm 3) to obtain a degree-(8k) compatible pair.
      - Apply `A_4` (i.e. `A_fill(l=2)`) to reach degree (8k+7).

    Parameter partition (8k+7 total):
      - 4 params for (H8, \\tilde H8): a,b,c,d
      - (k-1)*8 params for T_{k,8}
      - 11 params for A_4 (6 alpha + 5 beta)
    """

    field = builder.field
    if k < 2:
        raise ValueError("barQ_{8k+7} requires k>=2")
    deg = 8 * k + 7
    if len(alpha) != deg:
        raise ValueError(f"barQ_{{8k+7}} (k={k}) needs {deg} parameters, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    x = builder.x

    a_h8, b_h8, c_h8, d_tilde = alpha[0:4]
    t_len = (k - 1) * 8
    t_params = alpha[4 : 4 + t_len]
    fill = alpha[4 + t_len :]
    a_alpha = fill[:6]
    beta = fill[6:]
    if len(t_params) != t_len or len(a_alpha) != 6 or len(beta) != 5:
        raise ValueError("internal error: barQ_{8k+7} parameter partition mismatch")

    # H8 proxy (monic degree 8) + tilde shift.
    H8 = builder.mul(
        H4.add(x.add_const(b_h8, field), field),
        H4.add(H2.add_const(c_h8, field), field),
    ).add_const(a_h8, field)
    tilde_H8 = H8.add_const(d_tilde, field)

    # Degree-(8k) compatible pair from T_{k,8}.
    S1, S2, Hs_out, _tilde_out = _paper_T(builder, k=k, l=3, alpha=t_params, Hs=[x, H2, H4, H8], tilde_H_2l=tilde_H8)

    # Final A_4 fill adds 7 degrees: 8k -> 8k+7.
    out = _paper_A_fill(builder, 2, a_alpha, beta, S1, S2, [x, H2, H4])

    # Expose any higher known powers produced by the internal T recursion.
    return out, list(Hs_out)


def _paper_barQ_31(
    builder: ChainBuilder, alpha: List[Number], H2: AffineForm, H4: AffineForm
) -> Tuple[AffineForm, AffineForm, AffineForm]:
    """
    Concrete construction for \\bar{Q}_{31}(x,H2,H4) used by the first nontrivial
    `8k+7` induction instance (n=63).

    sections/constructions.tex assumes an (otherwise unspecified) family \\bar{Q}_n
    decodable given only (H2,H4). The earlier draft attempted to realize
    \\bar{Q}_{31} as an `A_8` instance with a hand-crafted degree-16 compatible
    pair, but that choice was not bijective (Jacobian det=0).

    We instead build \\bar{Q}_{31} via a “larger-input fill” that leaves enough
    room to synthesize the missing higher powers inside the tight 15-multiplication
    budget:

      1) Build a monic degree-8 polynomial `H8` and a shifted `\\tilde H8`.
      2) Use the paper’s `T_{3,8}` construction to obtain a degree-24 compatible
         pair (S1,S2) (and, as a byproduct, a monic degree-16 polynomial `H16`).
      3) Apply the fill construction `A_4` (i.e. `A_fill(l=2)`) to (S1,S2) to
         obtain a degree-31 polynomial.

    Parameter partition (31 total):
      - 4 params for (H8, \\tilde H8): a,b,c,d
      - 16 params for `T_{3,8}`: t0..t15
      - 6 params for `A_4` alpha: α0..α5
      - 5 params for `A_4` beta:  β0..β4

    Total multiplications given (H2,H4): 1 (H8) + 8 (T_{3,8}) + 6 (A_4) = 15.

    Returns:
        (barQ31, H8, H16)
    """

    field = builder.field
    if len(alpha) != 31:
        raise ValueError(f"barQ_31 needs 31 parameters, got {len(alpha)}")
    out, Hs_out = _paper_barQ_8k_plus_7_with_powers(builder, k=3, alpha=alpha, H2=H2, H4=H4)
    if len(Hs_out) <= 4:
        raise ValueError("internal error: expected an H16 byproduct from barQ_{31}")
    return out, Hs_out[3], Hs_out[4]


def _paper_barQ_4k_plus_3_using_H2_H4(
    builder: ChainBuilder, k: int, alpha: List[Number], H2: AffineForm, H4: AffineForm
) -> AffineForm:
    """
    Construct \\bar{Q}_{4k+3}(x,H2,H4) using the provided (H2,H4).

    sections/constructions.tex claims a family \\bar{Q}_{4k+3} that is decodable given only
    H2 and H4, but the explicit polynomial is not written down. For the global
    P_n[α] construction, we need a version that fits the tight multiplication
    budget (2k+1 mults for degree 4k+3).

    The actual implementation is delegated to `_paper_barQ_odd_with_H2_H4`, which
    selects the appropriate paper construction given the available known powers.
    """

    deg = 4 * k + 3
    return _paper_barQ_odd_with_H2_H4(builder, deg=deg, alpha=alpha, H2=H2, H4=H4)


def _paper_splittable_pair(
    builder: ChainBuilder, n: int, alpha: List[Number]
) -> Tuple[AffineForm, AffineForm, List[AffineForm]]:
    """
    Build (T^{(1)}_n, T^{(2)}_n) and return a byproduct list of “known powers”.

    This implements the casework / induction steps in sections/constructions.tex, plus the
    explicit special cases 15/27/31.

    Return value:
      - (T1, T2, Hs) where Hs[i] is a monic degree-2^i polynomial (“known power”),
        with Hs[0]=x. (We do not enforce that these are literal iterated squares;
        the paper’s constructions only require the degree/monicity structure.)
    """

    field = builder.field
    if n < 1 or (n % 2) == 0:
        raise ValueError("splittable_pair requires odd n >= 1")
    if n == 7:
        raise ValueError("no splittable pair is used for n=7; use the septic base construction instead")
    if len(alpha) != n:
        raise ValueError(f"splittable_pair({n}) needs {n} params, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    # Tiny bases.
    if n == 1:
        x = builder.x
        return builder.const(field.one()), builder.const(alpha[0]), [x]

    if n == 3:
        # H2 = (x + α2)x + α1
        # T1 = H2, T2 = H2 + α0
        x = builder.x
        H2 = _paper_H2(builder, alpha0=alpha[1], alpha1=alpha[2])
        return H2, H2.add_const(alpha[0], field), [x, H2]

    # Explicit special cases from sections/constructions.tex.
    if n == 15:
        H2 = _paper_H2(builder, alpha0=alpha[6], alpha1=alpha[7])
        x = builder.x
        x_shift = x.add_const(alpha[5], field)
        H4 = _paper_square_diff(builder, H2, x_shift).add_const(alpha[4], field)

        S1 = _paper_Q_known_powers(builder, 3, alpha[8:15], [x, H2, H4])
        S2 = H2.add_const(alpha[3], field)
        T1 = _paper_square_diff(builder, S1, S2).add_const(alpha[1], field)

        # sections/constructions.tex defines
        #   T2_low = H4^2 - (H2+α2)^2 + α0
        # which has degree 8. For the later induction steps we need the second
        # component to have degree 14. We “promote” it by adding `T1` (no extra
        # multiplications), mirroring the fix used in the `n=27` special case.
        T2_low = _paper_square_diff(builder, H4, H2.add_const(alpha[2], field)).add_const(alpha[0], field)
        T2 = T2_low.add(T1, field)
        # Expose the monic degree-8 byproduct (used as H8 in the 8k+7 induction).
        H8 = T2_low
        return T1, T2, [x, H2, H4, H8]

    if n == 27:
        H2 = _paper_H2(builder, alpha0=alpha[2], alpha1=alpha[3])
        x = builder.x

        # Special case 27 from sections/constructions.tex.
        #
        # Note: sections/constructions.tex writes `T^{(2)}_{27}` as a low-degree (deg 14)
        # expression. That version is bijective by itself, but it does not compose
        # correctly as a “splittable pair” inside the later `8k+3` induction.
        #
        # We repair it by following the same template as the `n=31` special case:
        # use the *same* high-degree polynomial (`Q13`) in both components, but
        # introduce an external shift (here we reuse `α13`, which is not used by
        # `Q13`) so the map remains generically invertible.
        S1, Hs_out, _ = _paper_Q_2lp1k_minus_1_with_powers(builder, k=3, l=1, alpha=alpha[14:27], Hs=[x, H2])
        if len(Hs_out) <= 2:
            raise ValueError("internal error: expected H4 byproduct in Q_13")
        H4 = Hs_out[2]
        Hs = [x, H2] + list(Hs_out[2:])

        S2 = _paper_q3(builder, alpha[4], alpha[5], alpha[6], H2)
        S3 = _paper_Q_known_powers(builder, 3, alpha[7:14], [x, H2, H4])

        T1 = _paper_square_diff(builder, S1, S2).add_const(alpha[1], field)
        # Promote the low-degree second component by adding `T1` (no extra multiplications).
        # This yields a degree-26 `T2` that composes correctly in later induction steps.
        T2_low = _paper_square_diff(builder, S3, H2).add_const(alpha[0], field)
        T2 = T2_low.add(T1, field)
        return T1, T2, Hs

    if n == 31:
        H2 = _paper_H2(builder, alpha0=alpha[6], alpha1=alpha[7])
        x = builder.x
        x_shift = x.add_const(alpha[5], field)
        H4 = _paper_square_diff(builder, H2, x_shift).add_const(alpha[4], field)

        # sections/constructions.tex (Special case 31) references a “good polynomial”
        # gadget \bar{Q}_{15}(x,H2,H4).
        S1 = _paper_barQ_odd_with_H2_H4(builder, deg=15, alpha=alpha[16:31], H2=H2, H4=H4)
        S2 = _paper_Q_known_powers(builder, 3, alpha[8:15], [x, H2, H4])
        S3 = _paper_q3(builder, alpha[1], alpha[2], alpha[3], H2)
        T1 = _paper_square_diff(builder, S1, S2).add(S3, field)

        T2 = _paper_square_diff(builder, S1.add_const(alpha[15], field), H4).add_const(alpha[0], field)
        return T1, T2, [x, H2, H4]

    # Main families / induction steps.
    if (n % 4) == 1:
        # n = 4k+1
        k = (n - 1) // 4
        # Paper indexing/layout (sections/constructions.tex, Lemma “The 4k+1 family is splittable”):
        #   - α0..α_{4k-3}   : parameters for the internal `T_{2k,2}` call
        #   - α_{4k-2}       : scalar shift in \\tilde H2 = H2 + α_{4k-2}
        #   - α_{4k-1},α_{4k}: H2 = (x + α_{4k})x + α_{4k-1}
        #
        # This “high-indexed H2” convention is important for the paper-faithful
        # coefficient→parameter decoding algorithms, which recover H2 from the
        # top coefficients of P_{4k+1}.
        t_params = alpha[: n - 3]
        tilde_shift = alpha[n - 3]
        h2_const = alpha[n - 2]
        h2_lin = alpha[n - 1]

        H2 = _paper_H2(builder, alpha0=h2_const, alpha1=h2_lin)
        tilde_H2 = H2.add_const(tilde_shift, field)
        x = builder.x
        T1, T2, Hs_out, _tilde_out = _paper_T(
            builder, k=2 * k, l=1, alpha=t_params, Hs=[x, H2], tilde_H_2l=tilde_H2
        )
        # Keep the “known powers” produced by the internal T recursion.
        return T1, T2, Hs_out

    if (n % 8) == 3:
        # n = 8k+3 (k>=1 here; n=3 handled above)
        k = (n - 3) // 8
        sub_n = 2 * k + 1
        S1_1, S1_2, Hs = _paper_splittable_pair(builder, sub_n, alpha[2 * k : 4 * k + 1])
        if len(Hs) < 2:
            raise ValueError("internal error: expected H2 in splittable_pair output")
        x = Hs[0]
        H2 = Hs[1]

        # Paper induction step (sections/constructions.tex, Algorithm “If 2k+1 is splittable
        # then 8k+3 is splittable”):
        #   S2 = Q_{4k+1}(x,H2), which also makes an H4 derivable as a byproduct.
        S2, Hs2_raw, _tilde_out = _paper_Q_2lp1k_minus_1_with_powers(
            builder, k=k, l=1, alpha=alpha[4 * k + 2 : 8 * k + 3], Hs=[x, H2]
        )
        if len(Hs2_raw) <= 2:
            raise ValueError("internal error: expected an H4 byproduct in Q_{4k+1}")

        # The l=1 Q_{4k+1} construction internally shifts H2 to \\hat H2; the
        # known-powers byproducts beyond H2 are still valid, but we must keep
        # the original H2 at Hs[1] for downstream Q calls.
        Hs2 = [x, H2] + list(Hs2_raw[2:])

        # S3 = Q_{2k-1}(x, H2, H4, ..., H_{2^ℓ}).
        #
        # sections/constructions.tex special-cases k=1 (so 2k-1=1) and simply uses the
        # constant α1 instead of the generic Q_1 gadget.
        if k == 1:
            S3 = builder.const(alpha[1])
            Hs3 = list(Hs2)
        else:
            deg3 = 2 * k - 1
            S3, Hs3, _ = _paper_Q_for_odd_degree_with_powers(builder, deg=deg3, alpha=alpha[1 : 2 * k], Hs=Hs2)

        # Preserve any higher “known powers” produced by the recursive S1 call,
        # and extend with any additional byproducts from S3.
        if len(Hs) > len(Hs2):
            Hs2 = list(Hs2) + list(Hs[len(Hs2) :])
        if len(Hs3) > len(Hs2):
            Hs2 = list(Hs2) + list(Hs3[len(Hs2) :])

        T1 = _paper_square_diff(builder, S2, S1_1).add(S3, field)
        T2 = _paper_square_diff(builder, S2.add_const(alpha[4 * k + 1], field), S1_2).add_const(alpha[0], field)
        # Expose the “known powers” computed while building S2; higher-level calls
        # may need H8/H16/... (e.g. when a later Q-construction has v2(deg+1) >= 3).
        return T1, T2, Hs2

    if (n % 8) == 7:
        # n = 8k+7 (n in {7,15,31} handled above)
        k = (n - 7) // 8
        sub_n = 2 * k + 1
        S1_1, S1_2, Hs = _paper_splittable_pair(builder, sub_n, alpha[: 2 * k + 1])
        if len(Hs) < 2:
            raise ValueError("internal error: expected H2 in splittable_pair output for 8k+7 case")
        H2 = Hs[1]

        def build_Q(
            deg: int, params: List[Number], Hs_in: List[AffineForm]
        ) -> Tuple[AffineForm, List[AffineForm]]:
            """
            Build the Q_deg polynomial needed by the `8k+7` induction.

            We prefer the paper's “known powers” Q construction whenever the required
            known powers are already available from earlier steps (either from the
            recursive splittable-pair call or produced as byproducts of prior Q calls).

            If the required powers are *not* available, we must not synthesize them
            with extra squarings (that would exceed the n/2+1 multiplication budget).
            In that case we fall back to the `\\bar Q` gadget family, which is designed
            to work using only (H2,H4) as auxiliary inputs.
            """

            l = _v2_positive(deg + 1)
            odd = (deg + 1) >> l
            kk = (odd - 1) // 2
            need = l + 1 if kk > 0 else l

            # If we have enough known powers, use the paper's `Q_deg` construction.
            if len(Hs_in) >= need:
                q, Hs_out, _ = _paper_Q_for_odd_degree_with_powers(builder, deg=deg, alpha=params, Hs=Hs_in)
                return q, Hs_out

            # Otherwise, fall back to the “good polynomial” gadget family \\bar{Q}_deg
            # which is designed to work with only (H2,H4) as auxiliary inputs.
            q, Hs_out = _paper_barQ_odd_with_H2_H4_with_powers(builder, deg=deg, alpha=params, Hs_in=Hs_in)
            return q, Hs_out

        # S2 = Q_{2k+1}[…], and keep any newly produced known powers.
        S2, Hs = build_Q(sub_n, alpha[2 * k + 2 : 4 * k + 3], Hs)
        if len(Hs) < 2:
            raise ValueError("internal error: expected H2 to remain available after Q_{2k+1}")
        H2 = Hs[1]

        # S3 = Q_{4k+3}[…], which may require more known powers than S1 produced.
        S3, Hs = build_Q(4 * k + 3, alpha[4 * k + 4 : 8 * k + 7], Hs)

        T1 = _paper_square_diff(builder, S3, S2).add(S1_1, field)

        S2_shift = S2.add_const(alpha[2 * k + 1], field)
        S3_shift = S3.add_const(alpha[4 * k + 3], field)
        T2 = _paper_square_diff(builder, S3_shift, S2_shift).add(S1_2, field)
        return T1, T2, Hs

    raise ValueError(f"internal error: no splittable case matched for odd n={n}")

def _v2_positive(n: int) -> int:
    """2-adic valuation v2(n) for n>0: largest e such that 2^e | n."""

    if n <= 0:
        raise ValueError("v2_positive requires n > 0")
    e = 0
    while (n & 1) == 0:
        n >>= 1
        e += 1
    return e


def _paper_QO(
    builder: ChainBuilder, deg: int, alpha: List[Number], Hs: List[AffineForm]
) -> AffineForm:
    """Peeled monic family for any odd degree, given the tower up to
    `H_{2^{floor(log2 deg)}}`:

        QO(d) = (H_h + U) * W + B,   h = 2^{floor(log2 d)},
        U = QO(2h-d) inside the factor, W = B = QO(d-h),

    with Mersenne degrees delegating to the (peeled) known-powers gadget.
    Exactly (d-1)/2 multiplications; parameter layout [U..., W..., B...].
    """

    field = builder.field
    if deg < 1 or deg % 2 == 0:
        raise ValueError("QO requires odd deg >= 1")
    if len(alpha) != deg:
        raise ValueError(f"QO(deg={deg}) needs {deg} params, got {len(alpha)}")
    if deg == 1:
        return builder.x.add_const(field.coerce(alpha[0]), field)
    t = deg.bit_length()
    if deg == (1 << t) - 1:
        return _paper_Q_known_powers(builder, t, alpha, Hs[:t])
    h = 1 << (t - 1)
    w = deg - h
    ud = 2 * h - deg
    U = _paper_QO(builder, ud, alpha[:ud], Hs)
    W = _paper_QO(builder, w, alpha[ud : ud + w], Hs)
    B = _paper_QO(builder, w, alpha[ud + w :], Hs)
    return builder.mark_value(builder.mul(Hs[t - 1].add(U, field), W).add(B, field))


def _poly_QO(*, deg: int, alpha: List[Number], Hs: List[Poly], field: Field) -> Poly:
    """Coefficient-level twin of `_paper_QO`."""

    if deg == 1:
        return _poly_add_const(Hs[0], field.coerce(alpha[0]), field)
    t = deg.bit_length()
    if deg == (1 << t) - 1:
        return _poly_paper_Q_known_powers(k=t, alpha=alpha, Hs=Hs[:t], field=field)
    h = 1 << (t - 1)
    w = deg - h
    ud = 2 * h - deg
    U = _poly_QO(deg=ud, alpha=alpha[:ud], Hs=Hs, field=field)
    W = _poly_QO(deg=w, alpha=alpha[ud : ud + w], Hs=Hs, field=field)
    B = _poly_QO(deg=w, alpha=alpha[ud + w :], Hs=Hs, field=field)
    return _poly_add(_poly_mul(_poly_add(Hs[t - 1], U, field), W, field), B, field)


def _paper_Q_for_odd_degree_with_powers(
    builder: ChainBuilder,
    deg: int,
    alpha: List[Number],
    Hs: List[AffineForm],
) -> Tuple[AffineForm, List[AffineForm], AffineForm]:
    """
    Dispatch helper: for any odd `deg >= 1`, write
        deg = 2^l * (2k+1) - 1
    where `l = v2(deg+1) >= 1`, and call the known-powers construction
        Q_{2^{l+1}k + (2^l - 1)} = Q_deg.

    Returns:
        (Q_deg, Hs_out, tilde_out)
    """

    if deg < 1 or (deg % 2) == 0:
        raise ValueError("Q_for_odd_degree requires odd deg >= 1")
    l = _v2_positive(deg + 1)
    odd = (deg + 1) >> l  # == 2k+1
    if (odd % 2) == 0:
        raise ValueError("internal error: expected odd factor (deg+1)/2^l to be odd")
    k = (odd - 1) // 2
    if PEELED_Q and deg >= 3 and len(Hs) >= deg.bit_length():
        return _paper_QO(builder, deg, alpha, Hs), list(Hs), Hs[0]
    return _paper_Q_2lp1k_minus_1_with_powers(builder, k=k, l=l, alpha=alpha, Hs=Hs)


def _paper_A_fill(
    builder: ChainBuilder,
    l: int,
    alpha: List[Number],
    beta: List[Number],
    S1_2l: AffineForm,
    S2_2l: AffineForm,
    Hs: List[AffineForm],
) -> AffineForm:
    """
    Fill construction A_{2^l} from sections/constructions.tex (Algorithm `alg:constr-fill`).

    Inputs:
      - l >= 1
      - alpha: [α0..α_{2^{l+1}-3}] (length 2^{l+1}-2)
      - beta:  [β0..β_{2^l}]      (length 2^l+1)
      - S1_2l, S2_2l: the compatible pair components at scale 2^l
      - Hs: list of known powers, with Hs[i] = H_{2^i} and Hs[0] = x
            (so len(Hs) >= l+1)

    Output:
      - A_{2^l} = (x + β0) A^{(1)}_{2^l} + A^{(2)}_{2^l}
    """

    field = builder.field
    if l < 0:
        raise ValueError("A_fill requires l >= 0")
    if l > 0 and len(Hs) <= l:
        raise ValueError(f"A_fill requires Hs up to index {l} (H_{{2^{l}}})")

    need_alpha = (1 << (l + 1)) - 2
    need_beta = (1 << l) + 1
    if len(alpha) != need_alpha:
        raise ValueError(f"A_fill l={l} needs {need_alpha} alpha params, got {len(alpha)}")
    if len(beta) != need_beta:
        raise ValueError(f"A_fill l={l} needs {need_beta} beta params, got {len(beta)}")

    # Coerce parameters once.
    alpha = [field.coerce(a) for a in alpha]
    beta = [field.coerce(b) for b in beta]

    def A1(l_: int, S1: AffineForm) -> AffineForm:
        if l_ == 0:
            return S1
        if l_ == 1:
            # A^{(1)}_2 = (H2 + β1) S1 + α1
            t = builder.mul(Hs[1].add_const(beta[1], field), S1)
            return t.add_const(alpha[1], field)

        if l_ == 2:
            # S^{(1)}_2 = (H4 + β3) S^{(1)}_4 + Q_3[α3,α4,α5](x,H2)
            q3 = _paper_q3(builder, alpha[3], alpha[4], alpha[5], Hs[1])
            t = builder.mul(Hs[2].add_const(beta[3], field), S1)
            S1_2 = t.add(q3, field)
            # A^{(1)}_4 = A^{(1)}_2[α0,α1,β2,β1](S^{(1)}_2,(x,H2))
            t2 = builder.mul(Hs[1].add_const(beta[1], field), S1_2)
            return t2.add_const(alpha[1], field)

        # l_ >= 3:
        # S^{(1)}_{2^{l_-1}} = (H_{2^{l_}} + Q_{2^{l_-1}-1}[β_{2^{l_}-1}..β_{2^{l_-1}+1}]) S^{(1)}_{2^{l_}}
        #                  + Q_{2^{l_}-1}[α_{2^{l_}-1}..α_{2^{l_+1}-3}]
        k_small = l_ - 1  # Q_{2^{k_small}-1}
        if k_small < 2:
            raise ValueError("internal error: expected k_small >= 2 for l_>=3")

        # sections/constructions.tex writes this Q polynomial as
        #   Q_{2^{l_-1}-1}[β_{2^{l_}-1}, ..., β_{2^{l_-1}+1}],
        # i.e. parameters in *descending* β-index order.
        q_small_params = list(reversed(beta[(1 << (l_ - 1)) + 1 : (1 << l_)]))
        q_small = _paper_Q_known_powers(builder, k_small, q_small_params, Hs[: l_ - 1])

        factor = Hs[l_].add(q_small, field)
        t = builder.mul(factor, S1)

        q_big_params = alpha[(1 << l_) - 1 : (1 << (l_ + 1)) - 2]
        q_big = _paper_Q_known_powers(builder, l_, q_big_params, Hs[:l_])
        S1_prev = t.add(q_big, field)
        return A1(l_ - 1, S1_prev)

    def A2(l_: int, S2: AffineForm) -> AffineForm:
        if l_ == 0:
            return S2
        if l_ == 1:
            # A^{(2)}_2 = (H2 + β2) S2 + α0
            t = builder.mul(Hs[1].add_const(beta[2], field), S2)
            return t.add_const(alpha[0], field)

        if l_ == 2:
            # S^{(2)}_2 = (H4 + β4) S^{(2)}_4 + α2
            t = builder.mul(Hs[2].add_const(beta[4], field), S2)
            S2_2 = t.add_const(alpha[2], field)
            # A^{(2)}_4 = A^{(2)}_2[α0,α1,β2,β1](S^{(2)}_2,(x,H2))
            t2 = builder.mul(Hs[1].add_const(beta[2], field), S2_2)
            return t2.add_const(alpha[0], field)

        # l_ >= 3:
        # S^{(2)}_{2^{l_-1}} = (H_{2^{l_}} + β_{2^{l_}}) S^{(2)}_{2^{l_}} + α_{2^{l_}-2}
        t = builder.mul(Hs[l_].add_const(beta[1 << l_], field), S2)
        S2_prev = t.add_const(alpha[(1 << l_) - 2], field)
        return A2(l_ - 1, S2_prev)

    A1_out = A1(l, S1_2l)
    A2_out = A2(l, S2_2l)

    if l == 0:
        # Base (not explicitly spelled out in sections/constructions.tex, but needed for the l=1
        # instance of the “4k+1 using known powers” construction):
        #
        #   A_1 = (x + β0) * S1 + S2 + β1
        #
        # This matches the “(x+α)-extraction” pattern while keeping β1 as an
        # independent additive parameter.
        t = builder.mul(builder.x.add_const(beta[0], field), A1_out)
        return t.add(A2_out, field).add_const(beta[1], field)

    out = builder.mul(builder.x.add_const(beta[0], field), A1_out).add(A2_out, field)
    return out


def _paper_Q_known_powers(
    builder: ChainBuilder,
    k: int,
    alpha: List[Number],
    Hs: List[AffineForm],
) -> AffineForm:
    return builder.mark_value(_paper_Q_known_powers_impl(builder, k, alpha, Hs))


def _paper_Q_known_powers_impl(
    builder: ChainBuilder,
    k: int,
    alpha: List[Number],
    Hs: List[AffineForm],
) -> AffineForm:
    """
    Known-powers construction Q_{2^k-1} from sections/constructions.tex (Algorithm `alg:constr-known-2n-1`).

    Inputs:
      - k >= 2
      - alpha: [α0..α_{2^k-2}] (length 2^k-1)
      - Hs: list of known powers with Hs[i]=H_{2^i}, Hs[0]=x, and len(Hs) >= k

    Output:
      - Q_{2^k-1}(x, H2, ..., H_{2^{k-1}})
    """

    field = builder.field
    if k < 0:
        raise ValueError("Q_known_powers requires k >= 0")
    need = 1 if k == 0 else (1 << k) - 1
    if len(alpha) != need:
        raise ValueError(f"Q_known_powers k={k} needs {need} alpha params, got {len(alpha)}")
    if k >= 1 and len(Hs) <= k - 1:
        raise ValueError(f"Q_known_powers k={k} needs Hs up to index {k-1} (H_{{2^{k-1}}})")

    alpha = [field.coerce(a) for a in alpha]

    if PEELED_Q and k >= 3:
        m = (1 << (k - 1)) - 1
        gamma = alpha[0]
        W = _paper_Q_known_powers(builder, k - 1, alpha[1 : 1 + m], Hs[: k - 1])
        B = _paper_Q_known_powers(builder, k - 1, alpha[1 + m :], Hs[: k - 1])
        return builder.mul(Hs[k - 1].add_const(gamma, field), W).add(B, field)

    if k == 0:
        # Q_0[α0] is just a constant.
        return AffineForm.const_only(alpha[0])

    if k == 1:
        # Q_1[α0](x) = x + α0
        return builder.x.add_const(alpha[0], field)

    if k == 2:
        # Q_3[α0,α1,α2](x,H2)
        return _paper_q3(builder, alpha[0], alpha[1], alpha[2], Hs[1])

    if k == 3:
        # S^{(1)}_2 = H4 + α3
        # S^{(2)}_2 = H4 + α2
        # Q_7[α0..α6](x,H2,H4) = A_2[α0,α1,β2=α4,β1=α5,β0=α6](S1,S2,(x,H2))
        S1 = Hs[2].add_const(alpha[3], field)
        S2 = Hs[2].add_const(alpha[2], field)
        a_alpha = [alpha[0], alpha[1]]  # α0..α1
        beta_block = [alpha[4], alpha[5], alpha[6]]  # corresponds to β2,β1,β0 in that order
        beta = [field.zero() for _ in range(3)]  # β0..β2
        # Map alpha[4+i] -> β_{2-i}.
        for i, v in enumerate(beta_block):
            beta[2 - i] = v
        return _paper_A_fill(builder, 1, a_alpha, beta, S1, S2, Hs[:2])

    # k >= 4:
    # S^{(1)}_{2^{k-2}} = H_{2^{k-1}} + Q_{2^{k-2}-1}[α_{2^{k-1}-1}..α_{2^{k-1}+2^{k-2}-3}]
    # S^{(2)}_{2^{k-2}} = H_{2^{k-1}} + α_{2^{k-1}-2}
    # Q_{2^k-1} = A_{2^{k-2}}[α0..α_{2^{k-1}-3}, β_{2^{k-2}}..β0](S1,S2,(x,H2..H_{2^{k-2}}))
    sub_k = k - 2
    sub_start = (1 << (k - 1)) - 1
    sub_end = (1 << (k - 1)) + (1 << (k - 2)) - 2
    q_sub_params = alpha[sub_start:sub_end]
    q_sub = _paper_Q_known_powers(builder, sub_k, q_sub_params, Hs[: k - 2])

    S1 = Hs[k - 1].add(q_sub, field)
    S2 = Hs[k - 1].add_const(alpha[(1 << (k - 1)) - 2], field)

    a_alpha = alpha[: (1 << (k - 1)) - 2]  # α0..α_{2^{k-1}-3}

    beta_block_start = (1 << (k - 1)) + (1 << (k - 2)) - 2
    beta_block = alpha[beta_block_start:]
    l = k - 2
    need_beta = (1 << l) + 1
    if len(beta_block) != need_beta:
        raise ValueError(
            f"internal error: expected {need_beta} beta-block params for k={k}, got {len(beta_block)}"
        )
    beta = [field.zero() for _ in range(need_beta)]  # β0..β_{2^l}
    for i, v in enumerate(beta_block):
        beta[(1 << l) - i] = v

    return _paper_A_fill(builder, l, a_alpha, beta, S1, S2, Hs[: l + 1])


def _trim_trailing_zeros(coeffs: List[Number], field: Field) -> List[Number]:
    if not coeffs:
        return []
    out = [field.coerce(c) for c in coeffs]
    while len(out) > 1 and field.is_zero(out[-1]):
        out.pop()
    return out


# =============================================================================
# Coefficient-level polynomial helpers (used for coefficient → α decoding)
# =============================================================================

Poly = List[Number]  # dense coefficients, ascending by degree


def _poly_trim(p: Poly, field: Field) -> Poly:
    if not p:
        return [field.zero()]
    out = [field.coerce(c) for c in p]
    while len(out) > 1 and field.is_zero(out[-1]):
        out.pop()
    return out


def _poly_degree(p: Poly) -> int:
    return len(p) - 1


def _poly_coeff(p: Poly, i: int, field: Field) -> Number:
    if i < 0:
        return field.zero()
    return p[i] if i < len(p) else field.zero()


def _poly_add(p: Poly, q: Poly, field: Field) -> Poly:
    n = max(len(p), len(q))
    out = [field.zero()] * n
    for i in range(n):
        out[i] = field.add(_poly_coeff(p, i, field), _poly_coeff(q, i, field))
    return _poly_trim(out, field)


def _poly_sub(p: Poly, q: Poly, field: Field) -> Poly:
    n = max(len(p), len(q))
    out = [field.zero()] * n
    for i in range(n):
        out[i] = field.sub(_poly_coeff(p, i, field), _poly_coeff(q, i, field))
    return _poly_trim(out, field)


def _poly_add_const(p: Poly, c: Number, field: Field) -> Poly:
    out = list(p)
    if not out:
        out = [field.zero()]
    out[0] = field.add(field.coerce(out[0]), field.coerce(c))
    return _poly_trim(out, field)


def _poly_shift_xk(p: Poly, k: int, field: Field) -> Poly:
    if k < 0:
        raise ValueError("shift must be >= 0")
    if k == 0:
        return list(p)
    return [field.zero()] * k + list(p)


def _poly_mul(p: Poly, q: Poly, field: Field) -> Poly:
    p = _poly_trim(p, field)
    q = _poly_trim(q, field)
    if p == [field.zero()] or q == [field.zero()]:
        return [field.zero()]
    out = [field.zero()] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if field.is_zero(a):
            continue
        for j, b in enumerate(q):
            if field.is_zero(b):
                continue
            out[i + j] = field.add(out[i + j], field.mul(a, b))
    return _poly_trim(out, field)


def _poly_mul_trunc(p: Poly, q: Poly, *, max_deg: int, field: Field) -> Poly:
    """
    Multiply polynomials and truncate to degrees <= max_deg.

    This is used by coefficient decoders that only need a low-degree (or high-degree)
    window, to avoid O(n^2) work on large degrees.
    """

    if max_deg < 0:
        return [field.zero()]
    p = _poly_trim(p, field)
    q = _poly_trim(q, field)
    if p == [field.zero()] or q == [field.zero()]:
        return [field.zero()]
    out = [field.zero()] * (max_deg + 1)
    for i, a in enumerate(p):
        if i > max_deg or field.is_zero(a):
            continue
        max_j = min(max_deg - i, len(q) - 1)
        for j in range(0, max_j + 1):
            b = q[j]
            if field.is_zero(b):
                continue
            out[i + j] = field.add(out[i + j], field.mul(a, b))
    return _poly_trim(out, field)


def _poly_square(p: Poly, field: Field) -> Poly:
    p = _poly_trim(p, field)
    if p == [field.zero()]:
        return [field.zero()]
    n = len(p)
    out = [field.zero()] * (2 * n - 1)
    for i in range(n):
        a = p[i]
        if field.is_zero(a):
            continue
        # Diagonal term.
        out[2 * i] = field.add(out[2 * i], field.mul(a, a))
        # Off-diagonal terms counted twice.
        for j in range(i + 1, n):
            b = p[j]
            if field.is_zero(b):
                continue
            prod = field.mul(a, b)
            prod2 = field.add(prod, prod)
            out[i + j] = field.add(out[i + j], prod2)
    return _poly_trim(out, field)


def _poly_divmod_monic(dividend: Poly, divisor: Poly, field: Field) -> Tuple[Poly, Poly]:
    """
    Polynomial long division by a monic divisor (Lemma `lem:monic-division`).

    Returns (quotient, remainder) with:
      dividend = quotient*divisor + remainder,  deg(remainder) < deg(divisor).
    """

    dividend = _poly_trim(dividend, field)
    divisor = _poly_trim(divisor, field)
    deg_divisor = _poly_degree(divisor)
    if deg_divisor < 1:
        raise ValueError("divisor degree must be >= 1")
    if _poly_coeff(divisor, deg_divisor, field) != field.one():
        raise ValueError("divisor must be monic")

    deg_dividend = _poly_degree(dividend)
    if deg_dividend < deg_divisor:
        return [field.zero()], list(dividend)

    rem = list(dividend)
    q_deg = deg_dividend - deg_divisor
    quot: Poly = [field.zero()] * (q_deg + 1)

    for t in range(q_deg, -1, -1):
        coef = _poly_coeff(rem, deg_divisor + t, field)
        quot[t] = coef
        if field.is_zero(coef):
            continue
        # rem -= coef * x^t * divisor
        for j in range(deg_divisor + 1):
            idx = j + t
            rem[idx] = field.sub(rem[idx], field.mul(coef, divisor[j]))

    rem = rem[:deg_divisor] if deg_divisor > 0 else [field.zero()]
    return _poly_trim(quot, field), _poly_trim(rem, field)


def _series_mul_trunc(a: List[Number], b: List[Number], *, max_deg: int, field: Field) -> List[Number]:
    """
    Multiply two power series (coefficient lists) and truncate to degree `max_deg`.

    Lists are in increasing degree order: a[i] is z^i coefficient.
    """

    out = [field.zero()] * (max_deg + 1)
    for i, ai in enumerate(a):
        if field.is_zero(ai) or i > max_deg:
            continue
        max_j = min(max_deg - i, len(b) - 1)
        for j in range(0, max_j + 1):
            bj = b[j]
            if field.is_zero(bj):
                continue
            out[i + j] = field.add(out[i + j], field.mul(ai, bj))
    return out


def _series_pow_trunc(base: List[Number], exponent: int, *, max_deg: int, field: Field) -> List[Number]:
    """
    Raise a power series `base` to `exponent`, truncated to degree `max_deg`.

    The series is in increasing degree order. This routine is used for
    extracting *top coefficients* of polynomial powers via reversal.
    """

    if exponent < 0:
        raise ValueError("exponent must be >= 0")
    if exponent == 0:
        out = [field.zero()] * (max_deg + 1)
        out[0] = field.one()
        return out

    result = [field.zero()] * (max_deg + 1)
    result[0] = field.one()
    power = list(base[: max_deg + 1]) + [field.zero()] * max(0, (max_deg + 1) - len(base))

    e = exponent
    while e:
        if e & 1:
            result = _series_mul_trunc(result, power, max_deg=max_deg, field=field)
        e >>= 1
        if e:
            power = _series_mul_trunc(power, power, max_deg=max_deg, field=field)
    return result


def _poly_top_coeffs_of_power(
    base: Poly,
    exponent: int,
    *,
    want: int,
    field: Field,
) -> List[Number]:
    """
    Return the top `want` coefficients of base(x)^exponent as a list in descending degree order.

    For monic `base` of degree d, base^e has degree e*d. We return
        [x^{ed}]..[x^{ed-(want-1)}].

    This runs in roughly O(want^2 log exponent), independent of the full degree ed.
    """

    if want < 1:
        raise ValueError("want must be >= 1")
    if exponent < 0:
        raise ValueError("exponent must be >= 0")
    base = _poly_trim(base, field)
    d = _poly_degree(base)
    if exponent == 0:
        # 1
        out = [field.zero()] * want
        out[0] = field.one()
        return out
    if _poly_coeff(base, d, field) != field.one():
        raise ValueError("base must be monic for top-coeff extraction")

    # Reversed series: A(z) = z^d * base(1/z) = 1 + a1 z + ... + a_{d} z^d.
    max_deg = want - 1
    a = [field.zero()] * (max_deg + 1)
    a[0] = field.one()
    for s in range(1, max_deg + 1):
        a[s] = _poly_coeff(base, d - s, field)

    b = _series_pow_trunc(a, exponent, max_deg=max_deg, field=field)

    # Map back: [z^s]A(z)^e equals [x^{ed-s}] base(x)^e.
    return [field.coerce(b[s]) for s in range(0, want)]


def _poly_pow(p: Poly, e: int, field: Field) -> Poly:
    if e < 0:
        raise ValueError("exponent must be >= 0")
    if e == 0:
        return [field.one()]
    p = _poly_trim(p, field)
    out: Poly = [field.one()]
    base: Poly = list(p)
    exp = e
    while exp > 0:
        if exp & 1:
            out = _poly_mul(out, base, field)
        exp >>= 1
        if exp:
            base = _poly_square(base, field)
    return _poly_trim(out, field)


def _poly_scale_int(p: Poly, k: int, field: Field) -> Poly:
    """
    Multiply a polynomial by an integer scalar k, interpreted in `field`.
    """

    if k == 0:
        return [field.zero()]
    if k == 1:
        return _poly_trim(p, field)
    if k == -1:
        return _poly_trim([field.neg(field.coerce(c)) for c in p], field)
    kk = field.coerce(k)
    return _poly_trim([field.mul(field.coerce(c), kk) for c in p], field)


def _poly_scale_const(p: Poly, lam: Number, field: Field) -> Poly:
    """
    Multiply a polynomial by a field scalar `lam`.
    """

    lam = field.coerce(lam)
    if field.is_zero(lam):
        return [field.zero()]
    if lam == field.one():
        return _poly_trim(p, field)
    return _poly_trim([field.mul(field.coerce(c), lam) for c in p], field)

def _monic_sqrt_from_high_square_coeffs(square: Poly, root_deg: int, field: Field) -> Poly:
    """
    Recover monic S of degree `root_deg` from coefficients of S^2 in degrees >= root_deg.

    Implements the descending-coefficient induction from `sections/constructions.tex`,
    Lemma `lem:monic-from-power` specialized to m=2.
    """

    if root_deg < 1:
        raise ValueError("root_deg must be >= 1")
    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("monic square root requires char(F) != 2")

    square = _poly_trim(square, field)
    if _poly_degree(square) < 2 * root_deg:
        raise ValueError("square polynomial degree too small for requested root_deg")
    if square[2 * root_deg] != field.one():
        raise ValueError("square polynomial must be monic at degree 2*root_deg")

    inv2 = field.inv(two)
    s = [field.zero()] * (root_deg + 1)
    s[root_deg] = field.one()

    # For t=1..root_deg, solve coefficient at x^{2d - t}.
    for t in range(1, root_deg + 1):
        power = 2 * root_deg - t
        target = square[power]

        known = field.zero()
        for j in range(1, t):
            a = s[root_deg - j]
            b = s[root_deg - (t - j)]
            known = field.add(known, field.mul(a, b))

        s_dt = field.mul(field.sub(target, known), inv2)
        s[root_deg - t] = s_dt

    return _poly_trim(s, field)


def _monic_from_power_with_boundary(
    *,
    W: Poly,
    root_deg: int,
    m: int,
    boundary_error_coeff: Number,
    field: Field,
) -> Poly:
    """
    Coefficient-level version of `sections/constructions.tex`, Lemma `lem:monic-from-power-boundary`.

    Recover monic P of degree `root_deg` from
        W = P^m + E
    under the assumptions:
      - m > 1 is invertible in the field
      - deg(E) <= root_deg*m - root_deg
      - `boundary_error_coeff` equals coeff(E, root_deg*m - root_deg)

    This implementation follows the paper’s descending-coefficient induction, but
    computes the needed "previous-only" coefficients of the reversed series powers
    via a degree-by-degree dynamic program. It divides only by `m` (not by other
    integers), matching the lemma’s assumptions.
    """

    if root_deg < 1:
        raise ValueError("root_deg must be >= 1")
    if m <= 1:
        raise ValueError("m must be > 1")

    m_field = field.coerce(m)
    if field.is_zero(m_field):
        raise ValueError("m must be invertible in the field")
    inv_m = field.inv(m_field)

    W = _poly_trim(W, field)
    nm = root_deg * m
    if _poly_degree(W) < nm:
        raise ValueError("W has degree smaller than root_deg*m")
    if _poly_coeff(W, nm, field) != field.one():
        raise ValueError("W must be monic at degree root_deg*m")

    # Extract the top `root_deg+1` coefficients of P^m from W, correcting the
    # boundary one by subtracting coeff(E, nm-root_deg).
    f: List[Number] = [field.zero()] * (root_deg + 1)  # f[s] = [t^s]Q^m
    for s in range(0, root_deg):
        f[s] = _poly_coeff(W, nm - s, field)
    f[root_deg] = field.sub(_poly_coeff(W, nm - root_deg, field), field.coerce(boundary_error_coeff))

    # Work with reversed series Q(t) = t^root_deg * P(1/t) = 1 + q1 t + ... + q_root_deg t^root_deg.
    q: List[Number] = [field.zero()] * (root_deg + 1)
    q[0] = field.one()

    # dp[r][i] = [t^i] (Q(t))^r, for r=0..m, i=0..root_deg.
    # We build dp column-by-column in i. For each i, we first compute dp_zero
    # assuming q[i]=0, then solve q[i], then update dp[*][i] using the fact that
    # q[i] can only appear linearly in [t^i] (it cannot pair with any positive
    # degree term without exceeding total degree i).
    dp: List[List[Number]] = [[field.zero()] * (root_deg + 1) for _ in range(m + 1)]
    for r in range(m + 1):
        dp[r][0] = field.one()

    for i in range(1, root_deg + 1):
        # Compute dp_zero[r][i] for r=1..m with q[i]=0.
        for r in range(1, m + 1):
            acc = field.zero()
            # dp[r][i] = sum_{j=0..i} q[j] * dp[r-1][i-j]. With q[i]=0, sum to i-1.
            for j in range(0, i):
                acc = field.add(acc, field.mul(q[j], dp[r - 1][i - j]))
            dp[r][i] = acc

        poly = dp[m][i]  # coefficient from previously-decoded q[1..i-1]
        q_i = field.mul(field.sub(f[i], poly), inv_m)
        q[i] = q_i

        # Update dp[r][i] = dp_zero[r][i] + r*q_i.
        for r in range(1, m + 1):
            dp[r][i] = field.add(dp[r][i], field.mul(field.coerce(r), q_i))

    # Convert Q(t) coefficients back to P(x) coefficients.
    P: Poly = [field.zero()] * (root_deg + 1)
    P[root_deg] = field.one()
    for j in range(0, root_deg):
        P[j] = q[root_deg - j]
    return _poly_trim(P, field)


def _monic_from_power(
    *,
    power: Poly,
    root_deg: int,
    m: int,
    field: Field,
) -> Poly:
    """
    Coefficient-level version of `sections/constructions.tex`, Lemma `lem:monic-from-power`.

    Recover monic P of degree `root_deg` from P^m, assuming m is invertible.
    """

    return _monic_from_power_with_boundary(
        W=power, root_deg=root_deg, m=m, boundary_error_coeff=field.zero(), field=field
    )


def _decode_square_gadget(
    *,
    G: Poly,
    field: Field,
    boundary_error_coeff_deg_d: Optional[Number] = None,
) -> Tuple[Poly, Number]:
    """
    Decode the "square gadget" from `sections/constructions.tex`, Lemma `lem:square-gadget`.

    Given a polynomial of the form
        G = x*S^2 + (S + δ)^2 + E
    where S is monic of degree d and deg(E) <= d,
    recover (S, δ) assuming:
      - char(F) != 2,
      - and `boundary_error_coeff_deg_d` equals coeff(E, d) (defaults to 0).

    This matches how the lemma is used in the induction-step decoders, where
    the additive error term may have degree exactly d but its degree-d
    coefficient is known/derivable from surrounding structure.
    """

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("square gadget decoding requires char(F) != 2")
    inv2 = field.inv(two)

    G = _poly_trim(G, field)
    degG = _poly_degree(G)
    if degG < 3 or (degG % 2) == 0:
        raise ValueError("square gadget expects odd degree >= 3")
    if _poly_coeff(G, degG, field) != field.one():
        raise ValueError("square gadget polynomial must be monic")

    d = (degG - 1) // 2
    if boundary_error_coeff_deg_d is None:
        boundary_error_coeff_deg_d = field.zero()

    # Recover the coefficients of A = S^2 in degrees [d..2d] from the identities
    #   [x^i]G = A_{i-1} + A_i  for i=d+1..2d+1,
    # which are unaffected by the low-degree error term E.
    A_high: Dict[int, Number] = {2 * d: field.one()}
    for i in range(2 * d + 1, d, -1):  # i=2d+1 .. d+1
        A_i = A_high.get(i, field.zero())
        A_im1 = field.sub(_poly_coeff(G, i, field), A_i)
        A_high[i - 1] = A_im1

    A_partial: Poly = [field.zero()] * (2 * d + 1)
    for j in range(d, 2 * d + 1):
        A_partial[j] = A_high.get(j, field.zero())
    # Ensure monic at top.
    A_partial[2 * d] = field.one()

    S = _monic_sqrt_from_high_square_coeffs(A_partial, root_deg=d, field=field)
    S_sq = _poly_square(S, field)

    # δ from the boundary coefficient at degree d:
    #   (G - x*S^2 - S^2)[d] = 2δ + E[d].
    xS_sq = _poly_shift_xk(S_sq, 1, field)
    D = _poly_sub(_poly_sub(G, xS_sq, field), S_sq, field)
    coeff_D_d = _poly_coeff(D, d, field)
    delta = field.mul(field.sub(coeff_D_d, field.coerce(boundary_error_coeff_deg_d)), inv2)

    return S, delta


def _decode_square_minus_low(
    *,
    E: Poly,
    S_deg: int,
    T_deg_bound: int,
    field: Field,
) -> Tuple[Poly, Poly]:
    """
    Decode (S,T) from a relation
        E = S^2 - T
    where S is monic of degree S_deg and deg(T) <= T_deg_bound < S_deg.

    This is the coefficient-level version of `tools/impl/splittable_decode.py:decode_square_minus_low`.
    """

    if S_deg < 1:
        raise ValueError("S_deg must be >= 1")
    if T_deg_bound >= S_deg:
        raise ValueError("T_deg_bound must be < S_deg")
    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("square decoding requires char(F) != 2")

    E = _poly_trim(E, field)
    if _poly_degree(E) > 2 * S_deg:
        raise ValueError("E has degree too large for the stated S_deg")

    # Extract S^2 coefficients for degrees [S_deg..2*S_deg] (unaffected by T).
    S2_high: Poly = [field.zero()] * (2 * S_deg + 1)
    for d in range(S_deg, 2 * S_deg + 1):
        S2_high[d] = _poly_coeff(E, d, field)
    # Ensure monic at the top.
    S2_high[2 * S_deg] = field.one()

    S = _monic_sqrt_from_high_square_coeffs(S2_high, root_deg=S_deg, field=field)
    S2 = _poly_square(S, field)
    T = _poly_sub(S2, E, field)
    if _poly_degree(T) > T_deg_bound:
        raise ValueError("decoded T exceeds declared degree bound; assumptions violated")
    return _poly_trim(S, field), _poly_trim(T, field)


def _decode_square_difference(
    *,
    H: Poly,
    H_next: Poly,
    S_deg: int,
    T_deg_bound: int,
    field: Field,
) -> Tuple[Poly, Poly]:
    """
    Decode (S,T) from:
        H_next = (H + S)(H - S) + T = H^2 - S^2 + T
    where:
      - H is monic of degree D,
      - S is monic of degree S_deg = D/2,
      - deg(T) <= T_deg_bound < S_deg.

    Returns:
      (S, T).

    This is the coefficient-level version of
    `tools/impl/splittable_decode.py:decode_square_difference`.
    """

    if S_deg < 1:
        raise ValueError("S_deg must be >= 1")
    if T_deg_bound >= S_deg:
        raise ValueError("T_deg_bound must be < S_deg")
    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("square-difference decoding requires char(F) != 2")

    H = _poly_trim(H, field)
    H_next = _poly_trim(H_next, field)
    deg_H = _poly_degree(H)
    if _poly_coeff(H, deg_H, field) != field.one():
        raise ValueError("H must be monic")
    if deg_H != 2 * S_deg:
        raise ValueError("expected deg(H) == 2*S_deg")
    if _poly_degree(H_next) != 2 * deg_H or _poly_coeff(H_next, 2 * deg_H, field) != field.one():
        raise ValueError("expected monic H_next of degree 2*deg(H)")

    # E = H^2 - H_next = S^2 - T.
    E = _poly_sub(_poly_square(H, field), H_next, field)
    return _decode_square_minus_low(E=E, S_deg=S_deg, T_deg_bound=T_deg_bound, field=field)


def _decode_T_odd_step_powers(
    *,
    H_2l: Poly,
    H_2l_plus_1: Poly,
    field: Field,
) -> Tuple[Poly, Poly, Poly, Poly]:
    """
    Decode the l>=3 "odd-k" power-extension gadget used in `_paper_T`:

      H' := H_{2^l} + S1_1
      H_{2^{l+1}} = (H')^2 - (S1_2)^2 + S1_3

    where:
      - deg(H_{2^l}) is a power of two,
      - S1_1 is monic of degree 2^{l-1},
      - S1_2 is monic of degree 2^{l-2},
      - deg(S1_3) < 2^{l-2}.

    Returns:
      (H_prime, S1_1, S1_2, S1_3)
    """

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("odd-step decoding requires char(F) != 2")

    H_2l = _poly_trim(H_2l, field)
    H_2l_plus_1 = _poly_trim(H_2l_plus_1, field)
    deg_H = _poly_degree(H_2l)
    if deg_H <= 0 or (deg_H & (deg_H - 1)) != 0:
        raise ValueError("expected deg(H_2l) to be a positive power of two")
    if _poly_coeff(H_2l, deg_H, field) != field.one():
        raise ValueError("expected H_2l to be monic")
    if _poly_degree(H_2l_plus_1) != 2 * deg_H or _poly_coeff(H_2l_plus_1, 2 * deg_H, field) != field.one():
        raise ValueError("expected H_2l_plus_1 to be monic of degree 2*deg(H_2l)")

    # Recover H' from the fact that H_{2^{l+1}} matches (H')^2 in degrees >= deg_H.
    Hprime_sq_high: Poly = [field.zero()] * (2 * deg_H + 1)
    for d in range(deg_H, 2 * deg_H + 1):
        Hprime_sq_high[d] = _poly_coeff(H_2l_plus_1, d, field)
    Hprime_sq_high[2 * deg_H] = field.one()

    H_prime = _monic_sqrt_from_high_square_coeffs(Hprime_sq_high, root_deg=deg_H, field=field)
    S1_1 = _poly_sub(H_prime, H_2l, field)

    # Now isolate F = (S1_2)^2 - S1_3.
    F = _poly_sub(_poly_square(H_prime, field), H_2l_plus_1, field)
    S1_2_deg = deg_H // 4
    S1_2, S1_3 = _decode_square_minus_low(E=F, S_deg=S1_2_deg, T_deg_bound=S1_2_deg - 1, field=field)
    return _poly_trim(H_prime, field), _poly_trim(S1_1, field), _poly_trim(S1_2, field), _poly_trim(S1_3, field)


def _monic_quadratic_power_top_coeffs(*, H2: Poly, m: int, field: Field) -> Tuple[Number, Number]:
    """
    Return the top two non-leading coefficients of (H2(x))^m for monic quadratic
    H2(x)=x^2 + b x + c:
      - coeff at x^{2m-1} = m*b
      - coeff at x^{2m-2} = m*c + binom(m,2)*b^2
    """

    if m < 1:
        raise ValueError("m must be >= 1")
    H2 = _poly_trim(H2, field)
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("expected monic degree-2 H2")

    b = _poly_coeff(H2, 1, field)
    c = _poly_coeff(H2, 0, field)
    mb = _field_mul_int(field, b, m)
    # binom(m,2) * b^2
    choose2 = (m * (m - 1)) // 2
    term_b2 = _field_mul_int(field, field.mul(b, b), choose2)
    mc = _field_mul_int(field, c, m)
    return mb, field.add(mc, term_b2)


def _decode_T_even_step_powers(
    *,
    l: int,
    H_2l: Poly,
    H_2l_minus_1: Poly,
    Hs_for_Q: List[Poly],
    H_tilde_2l: Poly,
    H_2l_plus_1: Poly,
    H_tilde_2l_plus_1: Poly,
    field: Field,
) -> Tuple[Poly, Poly, Poly, Poly, List[Number], List[Number], Number, Number]:
    """
    Decode the even-k power-extension step used inside `_paper_T` for l>=2:

      H_next        = (H_2l + S1_1)(H_2l - S1_1) + S1_2
      H_tilde_next  = (H_tilde_2l + S2_1)(H_tilde_2l - S2_1) + S2_2

    where:
      - deg(H_2l) is a power of two D=2^l (l>=2),
      - S1_1 = H_{2^{l-1}} + Q_hi, with Q_hi = Q_{2^{l-1}-1} on `Hs_for_Q`,
      - S1_2 = Q_lo, with Q_lo = Q_{2^{l-1}-1} on `Hs_for_Q`,
      - S2_1 = H_{2^{l-1}} + δ  (δ scalar),
      - S2_2 is a scalar.

    Returns:
      (S1_1, S1_2, S2_1, S2_2, q_hi_params, q_lo_params, s2_1_shift, s2_2_scalar)
    """

    if l < 2:
        raise ValueError("even-step power decoder expects l>=2")
    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("even-step decoding requires char(F) != 2")

    H_2l = _poly_trim(H_2l, field)
    H_2l_minus_1 = _poly_trim(H_2l_minus_1, field)
    H_tilde_2l = _poly_trim(H_tilde_2l, field)
    H_2l_plus_1 = _poly_trim(H_2l_plus_1, field)
    H_tilde_2l_plus_1 = _poly_trim(H_tilde_2l_plus_1, field)

    deg_H = _poly_degree(H_2l)
    if deg_H != (1 << l) or _poly_coeff(H_2l, deg_H, field) != field.one():
        raise ValueError("expected monic H_{2^l} with degree 2^l")
    if _poly_degree(H_2l_minus_1) != (1 << (l - 1)) or _poly_coeff(H_2l_minus_1, 1 << (l - 1), field) != field.one():
        raise ValueError("expected monic H_{2^{l-1}}")

    S_deg = deg_H // 2
    S1_1, S1_2 = _decode_square_difference(H=H_2l, H_next=H_2l_plus_1, S_deg=S_deg, T_deg_bound=S_deg - 1, field=field)
    S2_1, S2_2 = _decode_square_difference(
        H=H_tilde_2l, H_next=H_tilde_2l_plus_1, S_deg=S_deg, T_deg_bound=S_deg - 1, field=field
    )

    Q_hi = _poly_sub(S1_1, H_2l_minus_1, field)
    Q_lo = _poly_trim(S1_2, field)

    k_q = l - 1
    q_hi_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=Q_hi, k=k_q, Hs=Hs_for_Q, field=field)
    q_lo_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=Q_lo, k=k_q, Hs=Hs_for_Q, field=field)

    # S2_1 shift is scalar.
    s2_1_shift_poly = _poly_sub(S2_1, H_2l_minus_1, field)
    if _poly_degree(s2_1_shift_poly) > 0:
        raise ValueError("expected S2_1 - H_{2^{l-1}} to be scalar")
    if _poly_degree(S2_2) > 0:
        raise ValueError("expected S2_2 to be scalar")
    s2_1_shift = _poly_coeff(s2_1_shift_poly, 0, field)
    s2_2_scalar = _poly_coeff(S2_2, 0, field)

    return (
        _poly_trim(S1_1, field),
        _poly_trim(S1_2, field),
        _poly_trim(S2_1, field),
        _poly_trim(S2_2, field),
        q_hi_params,
        q_lo_params,
        s2_1_shift,
        s2_2_scalar,
    )


def _decode_H4_from_H2_square_diff(
    *,
    H2: Poly,
    H4: Poly,
    field: Field,
) -> Tuple[Number, Number]:
    """
    Decode the l=1 even-step square-difference gadget parameters (a0,a1) from:

      H4 = (H2 + (x + a1))(H2 - (x + a1)) + a0
         = H2^2 - (x + a1)^2 + a0

    Assumes char(F) != 2.
    """

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("H4 square-difference decoding requires char(F) != 2")
    inv2 = field.inv(two)

    H2 = _poly_trim(H2, field)
    H4 = _poly_trim(H4, field)
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("expected monic degree-2 H2")
    if _poly_degree(H4) != 4 or _poly_coeff(H4, 4, field) != field.one():
        raise ValueError("expected monic degree-4 H4")

    # D := H2^2 - H4 = (x+a1)^2 - a0.
    D = _poly_sub(_poly_square(H2, field), H4, field)
    # [x^1]D = 2*a1.
    a1 = field.mul(_poly_coeff(D, 1, field), inv2)
    # [x^0]D = a1^2 - a0.
    a0 = field.sub(field.mul(a1, a1), _poly_coeff(D, 0, field))
    return a0, a1


def _recover_monic_factor_high_coeffs_from_product(
    *,
    product: Poly,
    known_factor: Poly,
    factor_deg: int,
    min_deg: int,
    field: Field,
) -> Dict[int, Number]:
    """
    Coefficient-level version of `sections/constructions.tex`, Lemma `lem:peel-monic-factor`.

    Recover coefficients of a monic polynomial U of degree `factor_deg` from the *high*
    coefficients of the product P = U * known_factor, where `known_factor` is monic.

    Returns:
        dict mapping degrees -> coeff(U, degree) for degrees in [min_deg..factor_deg]
        (inclusive), always including degree `factor_deg` with coefficient 1.
    """

    if min_deg > factor_deg:
        raise ValueError("min_deg must be <= factor_deg")
    known_factor = _poly_trim(known_factor, field)
    product = _poly_trim(product, field)

    degH = _poly_degree(known_factor)
    if _poly_coeff(known_factor, degH, field) != field.one():
        raise ValueError("known_factor must be monic")

    U: Dict[int, Number] = {factor_deg: field.one()}
    for u_deg in range(factor_deg - 1, min_deg - 1, -1):
        p_deg = degH + u_deg
        target = _poly_coeff(product, p_deg, field)
        known_sum = field.zero()

        # P_{degH+u_deg} = U_{u_deg} + sum_{j=1..t} U_{u_deg+j} * H_{degH-j}
        for j in range(1, (factor_deg - u_deg) + 1):
            known_sum = field.add(
                known_sum,
                field.mul(U[u_deg + j], _poly_coeff(known_factor, degH - j, field)),
            )

        U[u_deg] = field.sub(target, known_sum)

    return U


def _scalar_shift_from_square_boundary(
    *,
    coeff_P_at_boundary: Number,
    H: Poly,
    M: Poly,
    lam: Number,
    field: Field,
) -> Number:
    """
    Extract the scalar shift δ from Lemma `lem:scalar-shift-square`.

    Given:
      - H monic degree d
      - M monic degree e
      - λ != 0
      - coeff(P, d+e) where P = λ (H+δ)^2 M + E and deg(E) <= d+e-1

    Return:
      δ
    """

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("scalar-shift-square requires char(F) != 2")
    if field.is_zero(lam):
        raise ValueError("lam must be nonzero")

    H = _poly_trim(H, field)
    M = _poly_trim(M, field)
    d = _poly_degree(H)
    e = _poly_degree(M)
    if _poly_coeff(H, d, field) != field.one():
        raise ValueError("H must be monic")
    if _poly_coeff(M, e, field) != field.one():
        raise ValueError("M must be monic")

    # Compute coeff(H^2 * M, d+e).
    H_sq = _poly_square(H, field)
    boundary_deg = d + e
    coeff_H2M = field.zero()
    # coeff(H^2 M, boundary) = sum_i H_sq[i] * M[boundary-i]
    for i in range(max(0, boundary_deg - e), min(boundary_deg, _poly_degree(H_sq)) + 1):
        coeff_H2M = field.add(
            coeff_H2M, field.mul(_poly_coeff(H_sq, i, field), _poly_coeff(M, boundary_deg - i, field))
        )

    num = field.sub(coeff_P_at_boundary, field.mul(lam, coeff_H2M))
    den = field.mul(two, lam)
    return field.div(num, den)



def _field_rand(field: Field, rng: random.Random) -> Number:
    """Random field element for probing (small integers in the rational case)."""

    if field.modulus is not None:
        return field.coerce(rng.randrange(field.modulus))
    return field.coerce(rng.randrange(-9, 10))


def _field_gauss_solve(M: List[List[Number]], rhs: List[Number], field: Field) -> Optional[List[Number]]:
    """
    Solve M x = rhs over `field` (M is r x c with r >= c).  Returns x, or None
    if M does not have full column rank.  Small dense elimination; the systems
    here have at most a handful of unknowns (the paper's 2x2 / 3x3 blocks).
    """

    rows = [list(row) + [rhs_i] for row, rhs_i in zip(M, rhs)]
    ncols = len(M[0]) if M else 0
    piv_rows: List[List[Number]] = []
    for col in range(ncols):
        piv = None
        for r in rows:
            if not field.is_zero(r[col]):
                piv = r
                break
        if piv is None:
            return None
        rows.remove(piv)
        inv = field.inv(piv[col])
        piv = [field.mul(v, inv) for v in piv]
        for r in rows:
            f = r[col]
            if not field.is_zero(f):
                for j in range(col, ncols + 1):
                    r[j] = field.sub(r[j], field.mul(f, piv[j]))
        piv_rows.append(piv)
    # Back-substitute.
    x = [field.zero()] * ncols
    for col in range(ncols - 1, -1, -1):
        r = piv_rows[col]
        acc = r[ncols]
        for j in range(col + 1, ncols):
            acc = field.sub(acc, field.mul(r[j], x[j]))
        x[col] = acc
    return x


def _decode_by_descending_pivots(
    *,
    target: Poly,
    encode_fn,
    nparams: int,
    field: Field,
    rows: Optional[Iterable[int]] = None,
    seed: int = 0,
    what: str = "map",
) -> List[Number]:
    """
    Generic structural decoder for the paper's "descending affine pivot" maps.

    The paper's decoding lemmas (e.g. `lem:Q-unitriangular`, the pivot tables in
    `lem:4k+1-splittable` / `lem:Rk2l`, and the small linear blocks in
    `lem:barQ15` / `lem:septic-base`) all have the same shape: processing the
    coefficients of the output polynomial from high to low degree, each new
    coefficient exposes one fresh parameter affinely with a constant slope --
    or, occasionally, a small group of parameters that a constant affine system
    over a few otherwise-unused coefficient rows determines (the 2x2/3x3
    blocks).  This routine realizes that procedure numerically for an arbitrary
    encoder `encode_fn: params -> Poly`:

      1. probe the encoder at two random points to find, for every parameter,
         the set of coefficient rows it touches and its (constant) slopes;
      2. eliminate parameters from the highest pivot row downwards, solving
         collided pivot rows as small affine blocks over rows not touched by
         any other unresolved parameter;
      3. verify the result by re-encoding (raise `ValueError` on failure).

    `rows`, if given, restricts the usable coefficient window (used when only a
    window of the target polynomial is known, cf. the square-gadget steps).
    """

    rng = random.Random(0xC0FFEE ^ seed ^ (nparams << 8))
    allowed = None if rows is None else set(rows)

    bases = [[_field_rand(field, rng) for _ in range(nparams)] for _ in range(2)]
    enc_bases = [encode_fn(b) for b in bases]

    # diffs[i][t]: row -> slope of parameter i probed at base t.
    diffs: List[List[Dict[int, Number]]] = []
    support: List[set] = []
    for i in range(nparams):
        per_base: List[Dict[int, Number]] = []
        sup: set = set()
        for t in range(2):
            b2 = list(bases[t])
            b2[i] = field.add(b2[i], field.one())
            d = _poly_sub(encode_fn(b2), enc_bases[t], field)
            entries: Dict[int, Number] = {}
            for deg in range(len(d)):
                if not field.is_zero(d[deg]):
                    entries[deg] = d[deg]
                    sup.add(deg)
            per_base.append(entries)
        diffs.append(per_base)
        support.append(sup)

    piv_row: List[int] = []
    for i in range(nparams):
        cand = support[i] if allowed is None else (support[i] & allowed)
        if not cand:
            raise ValueError(f"{what}: parameter {i} has no effect on the available coefficient window")
        piv_row.append(max(cand))

    def _diff_vec(a: Poly, b: Poly) -> Dict[int, Number]:
        d = _poly_sub(a, b, field)
        return {i: v for i, v in enumerate(d) if not field.is_zero(v)}

    def _diff_vec(a: Poly, b: Poly) -> Dict[int, Number]:
        d = _poly_sub(a, b, field)
        return {i: v for i, v in enumerate(d) if not field.is_zero(v)}

    recovered: List[Number] = [field.zero()] * nparams
    unresolved = set(range(nparams))
    while unresolved:
        r = max(piv_row[i] for i in unresolved)
        group = sorted(i for i in unresolved if piv_row[i] == r)

        # Slopes are evaluated lazily at the *current* partial point: by the
        # time a pivot block is reached, all higher-pivot parameters are known,
        # so the block acts affinely there with the constant slopes the paper's
        # pivot lemmas provide.
        base_now = encode_fn(recovered)
        cols: Dict[int, Dict[int, Number]] = {}

        def _col(i: int) -> Dict[int, Number]:
            if i not in cols:
                probe = list(recovered)
                probe[i] = field.add(probe[i], field.one())
                cols[i] = _diff_vec(encode_fn(probe), base_now)
            return cols[i]

        # Grow the block downwards (merging lower pivot groups) until enough
        # clean affine equation rows exist -- the numerical analogue of the
        # paper's small linear blocks (e.g. the 2x2 solve in `lem:barQ15`).
        while True:
            others = [i for i in unresolved if i not in group]
            candidates: List[int] = []
            for w in range(r, -1, -1):
                if allowed is not None and w not in allowed:
                    continue
                if any(w in support[j] for j in others):
                    continue
                if all(field.is_zero(_col(i).get(w, field.zero())) for i in group):
                    continue
                candidates.append(w)
                if len(candidates) >= len(group) + 6:
                    break

            # Affineness checks on the candidate rows (cheap when the initial
            # two-point probe already agreed there).
            bad_rows: set = set()
            for i in group:
                needs_check = any(
                    diffs[i][0].get(w, field.zero()) != _col(i).get(w, field.zero())
                    or diffs[i][1].get(w, field.zero()) != _col(i).get(w, field.zero())
                    for w in candidates
                )
                if not needs_check:
                    continue
                probe = list(recovered)
                probe[i] = field.add(probe[i], field.add(field.one(), field.one()))
                d2 = _diff_vec(encode_fn(probe), base_now)
                for w in candidates:
                    s = _col(i).get(w, field.zero())
                    if d2.get(w, field.zero()) != field.add(s, s):
                        bad_rows.add(w)
            if len(group) <= 8:
                for ai in range(len(group)):
                    for bi in range(ai + 1, len(group)):
                        i, j = group[ai], group[bi]
                        probe = list(recovered)
                        probe[i] = field.add(probe[i], field.one())
                        probe[j] = field.add(probe[j], field.one())
                        dij = _diff_vec(encode_fn(probe), base_now)
                        for w in candidates:
                            want = field.add(_col(i).get(w, field.zero()), _col(j).get(w, field.zero()))
                            if dij.get(w, field.zero()) != want:
                                bad_rows.add(w)
            candidates = [w for w in candidates if w not in bad_rows]

            solved = False
            if len(candidates) >= len(group):
                M = [[_col(i).get(w, field.zero()) for i in group] for w in candidates]
                rhs = [
                    field.sub(_poly_coeff(target, w, field), _poly_coeff(base_now, w, field))
                    for w in candidates
                ]
                sol = _field_gauss_solve(M, rhs, field)
                if sol is not None:
                    for i, v in zip(group, sol):
                        recovered[i] = v
                        unresolved.discard(i)
                    solved = True
            if solved:
                break
            if not others:
                raise ValueError(f"{what}: not enough clean rows to solve pivot group at degree {r}")
            r_next = max(piv_row[i] for i in others)
            group = sorted(group + [i for i in others if piv_row[i] == r_next])

    chk = encode_fn(recovered)
    if allowed is None:
        if _poly_trim(chk, field) != _poly_trim(list(target), field):
            raise ValueError(f"{what}: descending-pivot decode failed verification")
    else:
        for w in allowed:
            if _poly_coeff(chk, w, field) != _poly_coeff(target, w, field):
                raise ValueError(f"{what}: descending-pivot decode failed verification (row {w})")
    return recovered


# =============================================================================
# Base decoders for the paper family P_n[α]
# =============================================================================


def _decode_P3_coeffs_to_alpha(coeffs: Poly, field: Field) -> List[Number]:
    coeffs = _poly_trim(coeffs, field)
    if len(coeffs) != 4 or coeffs[-1] != field.one():
        raise ValueError("P3 decoder expects monic degree-3 polynomial coeffs [a0..a2,1]")
    a0, a1, a2 = coeffs[0], coeffs[1], coeffs[2]
    alpha2 = field.sub(a2, field.one())
    alpha1 = field.sub(a1, alpha2)
    alpha0 = field.sub(a0, alpha1)
    return [alpha0, alpha1, alpha2]


def _decode_P7_coeffs_to_alpha(coeffs: Poly, field: Field) -> List[Number]:
    coeffs = _poly_trim(coeffs, field)
    if len(coeffs) != 8 or coeffs[-1] != field.one():
        raise ValueError("P7 decoder expects monic degree-7 polynomial coeffs [a0..a6,1]")

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("P7 decoding for char(F)=2 is not implemented")
    inv2 = field.inv(two)

    c0, c1, c2, c3, c4, c5, c6 = coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4], coeffs[5], coeffs[6]

    z2 = field.mul(c6, inv2)
    z2_sq = field.mul(z2, z2)

    z1 = field.mul(field.sub(field.sub(c5, z2_sq), field.one()), inv2)
    z1_sq = field.mul(z1, z1)

    v4 = field.sub(c4, field.one())
    two_z2z1 = field.add(field.mul(z2, z1), field.mul(z2, z1))
    RHS1 = field.sub(field.sub(field.sub(v4, two_z2z1), z2), field.zero())

    v3 = field.sub(c3, z2)
    alpha1 = field.sub(field.sub(field.sub(v3, field.mul(z2, RHS1)), z1_sq), z1)

    v2 = field.sub(field.sub(c2, z1), field.one())
    W1 = field.sub(field.sub(v2, field.mul(z2, alpha1)), field.mul(z1, RHS1))

    # alpha6 = c1 - (z1+1)*alpha1 - W1*(RHS1 + 1 - W1)
    z1_plus_1 = field.add(z1, field.one())
    term1 = field.mul(z1_plus_1, alpha1)
    term2 = field.mul(W1, field.sub(field.add(RHS1, field.one()), W1))
    alpha6 = field.sub(field.sub(c1, term1), term2)

    alpha4 = field.sub(field.sub(z2, field.one()), alpha6)
    alpha5 = field.sub(z1, field.mul(alpha4, field.add(field.one(), alpha6)))
    z0 = field.mul(alpha4, alpha5)
    alpha3 = field.sub(W1, z0)
    alpha2 = field.sub(field.sub(RHS1, field.add(z0, z0)), alpha3)
    alpha0 = field.sub(c0, field.mul(field.add(z0, alpha2), alpha1))

    return [alpha0, alpha1, alpha2, alpha3, alpha4, alpha5, alpha6]


def _decode_P5_coeffs_to_alpha(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode the paper base construction for `P_5[α0..α4]` implemented by `_paper_P5`:

      P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0

    This decoder is solver-free and works in any characteristic.
    """

    coeffs = _poly_trim(coeffs, field)
    if len(coeffs) != 6 or coeffs[-1] != field.one():
        raise ValueError("P5 decoder expects monic degree-5 polynomial coeffs [a0..a4,1]")

    a0, a1, a2, a3, a4 = coeffs[0], coeffs[1], coeffs[2], coeffs[3], coeffs[4]

    alpha2 = field.sub(a4, field.one())
    alpha2_sq = field.mul(alpha2, alpha2)
    alpha4 = field.add(field.sub(a2, field.mul(alpha2, a3)), alpha2_sq)
    alpha3 = field.sub(field.sub(a3, alpha2), alpha4)
    alpha4_sq = field.mul(alpha4, alpha4)
    alpha1 = field.add(field.sub(a1, field.mul(alpha4, a3)), alpha4_sq)
    alpha0 = field.add(field.sub(a0, field.mul(alpha2, a1)), field.mul(alpha2_sq, alpha4))
    return [alpha0, alpha1, alpha2, alpha3, alpha4]


def _decode_P9_coeffs_to_alpha(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode `P_9[α0..α8]`.

    This is the `4k+1` splittable family with k=2.
    """
    return _decode_P_4k_plus_1_coeffs_to_alpha(coeffs, field)


def _decode_P_coeffs_to_paper_params_peeling_fallback(coeffs: Poly, field: Field) -> List[Number]:
    """
    Generic (probing-based) coeff→α decoder for odd n.

    This exists only for validation / development until the paper-faithful
    structural decoders are implemented for all splittable families.
    """

    coeffs = _poly_trim(coeffs, field)
    if len(coeffs) <= 1:
        raise ValueError("polynomial must have positive degree for paper decoding")
    if coeffs[-1] != field.one():
        raise ValueError("paper decoding requires a monic polynomial (leading coefficient 1)")

    n = len(coeffs) - 1
    if (n % 2) == 0:
        raise ValueError("peeling fallback only applies to odd n")

    if field.modulus is None:
        raise NotImplementedError(
            "generic coeff→α peeling decoder requires a prime field modulus; "
            f"odd n={n} not implemented for rationals"
        )

    p = int(field.modulus)
    if p <= 2:
        raise NotImplementedError("generic peeling decoder expects an odd prime field")

    target = _poly_trim(coeffs, field)
    if _poly_degree(target) != n or _poly_coeff(target, n, field) != field.one():
        raise ValueError("internal error: expected monic target polynomial")

    alpha: List[Number] = [field.zero()] * n
    remaining = set(range(n))

    one = field.one()
    two = field.add(one, one)

    def encode(params: List[Number]) -> Poly:
        return _poly_trim(_poly_paper_P_from_params(params=params, field=field), field)

    def _try_solve_remaining_linearly(
        *, alpha_vec: List[Number], cur_poly: Poly, remaining_set: set[int]
    ) -> bool:
        if not remaining_set:
            return True
        unknowns = sorted(remaining_set)
        m = len(unknowns)

        r = [field.sub(_poly_coeff(target, d, field), _poly_coeff(cur_poly, d, field)) for d in range(n + 1)]

        cols: List[List[Number]] = []
        for idx in unknowns:
            trial = list(alpha_vec)
            trial[idx] = one
            pj = encode(trial)
            cols.append(
                [field.sub(_poly_coeff(pj, d, field), _poly_coeff(cur_poly, d, field)) for d in range(n + 1)]
            )

        mat: List[List[Number]] = []
        for row in range(n + 1):
            mat.append([cols[col][row] for col in range(m)] + [r[row]])

        row = 0
        pivots: List[Tuple[int, int]] = []
        for col in range(m):
            pivot = None
            for rr in range(row, n + 1):
                if not field.is_zero(mat[rr][col]):
                    pivot = rr
                    break
            if pivot is None:
                continue
            if pivot != row:
                mat[row], mat[pivot] = mat[pivot], mat[row]
            piv = mat[row][col]
            inv_piv = field.inv(piv)
            for cc in range(col, m + 1):
                mat[row][cc] = field.mul(mat[row][cc], inv_piv)
            for rr in range(n + 1):
                if rr == row:
                    continue
                factor = mat[rr][col]
                if field.is_zero(factor):
                    continue
                for cc in range(col, m + 1):
                    mat[rr][cc] = field.sub(mat[rr][cc], field.mul(factor, mat[row][cc]))
            pivots.append((row, col))
            row += 1
            if row == n + 1:
                break

        if len(pivots) != m:
            return False
        sol = [field.zero()] * m
        for rr, cc in pivots:
            sol[cc] = mat[rr][m]
        for idx, v in zip(unknowns, sol):
            alpha_vec[idx] = v
        return encode(alpha_vec) == target

    raise NotImplementedError(
        "probing/peeling fallback decoder is intentionally disabled; "
        "implement the paper-faithful splittable-family coefficient decoders instead"
    )


def _decode_P_4k_plus_1_coeffs_to_alpha(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode `P_{4k+1}[α0..α_{4k}]` (the main `4k+1` splittable family) for any `k>=2`.

    Paper structure (sections/constructions.tex, “4k+1 is splittable”):
      - H2 = (x + α_{4k})x + α_{4k-1} = x^2 + u*x + v, with (u,v) at the *end*.
      - \\tilde H2 = H2 + α_{4k-2}.
      - The first `4k-2` parameters are exactly the internal `T_{2k,2}` block.
      - P = x*T^{(1)}_{2k,2} + T^{(2)}_{2k,2}.

    Decoder outline:
      1) Recover (u,v,\\tilde shift) from the top three coefficients (independent of the T-block).
      2) Form the remainder polynomial P_R = P - (x*H2^{2k} + \\tilde H2^{2k}).
      3) Decode the T-block via `_decode_R_k(k=2k,l=1,...)`.
    """

    coeffs = _poly_trim(coeffs, field)
    if _poly_degree(coeffs) < 0 or _poly_coeff(coeffs, _poly_degree(coeffs), field) != field.one():
        raise ValueError("P_{4k+1} decoder expects a monic polynomial")

    n = _poly_degree(coeffs)
    if n < 9 or (n % 4) != 1:
        raise ValueError(f"expected n=4k+1 with k>=2, got n={n}")
    k = (n - 1) // 4

    two_k = field.coerce(2 * k)
    if field.is_zero(two_k):
        raise NotImplementedError("4k+1 decoding requires (2k) invertible in the field")
    inv_two_k = field.inv(two_k)

    c_n_minus_1 = _poly_coeff(coeffs, n - 1, field)
    c_n_minus_2 = _poly_coeff(coeffs, n - 2, field)
    c_n_minus_3 = _poly_coeff(coeffs, n - 3, field)

    # u from: [x^{4k}]P = 2k*u + 1.
    u = field.mul(field.sub(c_n_minus_1, field.one()), inv_two_k)

    # v from: [x^{4k-1}]P = C(2k,2)u^2 + 2k*v + 2k*u - k.
    u2 = field.mul(u, u)
    choose2 = math.comb(2 * k, 2)
    term_choose2_u2 = _field_mul_int(field, u2, choose2)
    num_v = field.add(
        field.sub(field.sub(c_n_minus_2, term_choose2_u2), _field_mul_int(field, u, 2 * k)),
        field.coerce(k),
    )
    v = field.mul(num_v, inv_two_k)

    # Remaining outer pivots (paper `lem:4k+1-splittable` pivot table):
    #   coeff 4k-2 -> a   (= alpha_{4k-3}, slope -2k)
    #   coeff 4k-3 -> e   (= alpha_{4k-4}, slope  k)
    #   coeff 4k-4 -> rho (= alpha_{4k-2}, slope  k)
    # The parameter-free boundary contributions of the remainder pair
    # (`lem:Rk2l-top-boundary`) are captured by synthetically re-encoding the
    # partial parameter vector, so each pivot is an exact affine solve.
    partial: List[Number] = [field.zero()] * (n)
    partial[n - 1] = u
    partial[n - 2] = v

    for idx, row in ((n - 4, n - 3), (n - 5, n - 4), (n - 3, n - 5)):
        base_enc = _poly_paper_P_from_params(params=partial, field=field)
        probe = list(partial)
        probe[idx] = field.add(probe[idx], field.one())
        probe_enc = _poly_paper_P_from_params(params=probe, field=field)
        slope = field.sub(_poly_coeff(probe_enc, row, field), _poly_coeff(base_enc, row, field))
        if field.is_zero(slope):
            raise ValueError("P_{4k+1} decoder: zero pivot slope (field not admissible?)")
        partial[idx] = field.div(
            field.sub(_poly_coeff(coeffs, row, field), _poly_coeff(base_enc, row, field)), slope
        )
    tilde_shift = partial[n - 3]

    x = [field.zero(), field.one()]
    H2 = [field.coerce(v), field.coerce(u), field.one()]
    tilde_H2 = _poly_add_const(H2, tilde_shift, field)

    H_pow = _poly_pow(H2, 2 * k, field)
    Ht_pow = _poly_pow(_poly_trim(tilde_H2, field), 2 * k, field)
    known = _poly_add(_poly_shift_xk(H_pow, 1, field), Ht_pow, field)
    P_R = _poly_sub(coeffs, known, field)

    t_params, _Hs_out, _tilde_out = _decode_R_k(
        k=2 * k, l=1, P_R=P_R, Hs=[x, H2], tilde_H_2l=tilde_H2, field=field
    )
    if len(t_params) != n - 3:
        raise ValueError("internal error: T_{2k,2} parameter block length mismatch")

    alpha = list(t_params) + [tilde_shift, v, u]

    chk = _poly_trim(_poly_paper_P_from_params(params=alpha, field=field), field)
    if chk != coeffs:
        raise RuntimeError("4k+1 decoder produced parameters that do not reproduce the input polynomial")
    return alpha


def _decode_Q5_coeffs_to_alpha_given_H2(Q5: Poly, H2: Poly, field: Field) -> List[Number]:
    """
    Decode the `Q_5[α0..α4](x,H2)` instance that arises as the k=1, l=1 case of
    `_paper_Q_2lp1k_minus_1_with_powers` (Lemma `lem:Q4k+1-from-H2` with k=1),
    by the lemma's descending affine pivots (via `_decode_by_descending_pivots`).
    """

    Q5 = _poly_trim(Q5, field)
    H2 = _poly_trim(H2, field)
    if _poly_degree(Q5) != 5 or _poly_coeff(Q5, 5, field) != field.one():
        raise ValueError("Q5 decoder expects a monic degree-5 polynomial")
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("Q5 decoder expects monic degree-2 H2")

    x = [field.zero(), field.one()]

    def _enc(a: List[Number]) -> Poly:
        out, _hs, _tilde = _poly_paper_Q_2lp1k_minus_1_with_powers(k=1, l=1, alpha=list(a), Hs=[x, H2], field=field)
        return out

    return _decode_by_descending_pivots(target=Q5, encode_fn=_enc, nparams=5, field=field, what="Q5-given-H2")


def _decode_Q3_coeffs_to_alpha_given_H2(Q3: Poly, H2: Poly, field: Field) -> List[Number]:
    """
    Decode `Q_3[α0,α1,α2](x,H2) = (x+α2)(H2+α1) + α0` given monic quadratic H2.

    This matches the direct algebra in sections/constructions.tex.
    """

    Q3 = _poly_trim(Q3, field)
    H2 = _poly_trim(H2, field)
    if _poly_degree(Q3) != 3 or _poly_coeff(Q3, 3, field) != field.one():
        raise ValueError("Q3 decoder expects monic degree-3 polynomial")
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("Q3 decoder expects monic degree-2 H2")

    h1 = _poly_coeff(H2, 1, field)
    h0 = _poly_coeff(H2, 0, field)

    alpha2 = field.sub(_poly_coeff(Q3, 2, field), h1)
    alpha1 = field.sub(_poly_coeff(Q3, 1, field), field.add(h0, field.mul(alpha2, h1)))
    alpha0 = field.sub(_poly_coeff(Q3, 0, field), field.mul(alpha2, field.add(h0, alpha1)))
    return [alpha0, alpha1, alpha2]


def _decode_Q7_coeffs_to_alpha_given_H2_H4(Q7: Poly, H2: Poly, H4: Poly, field: Field) -> List[Number]:
    """
    Decode `Q_7[α0..α6](x,H2,H4)` given monic (H2,H4).

    In paper notation:
      S1 = H4 + α3
      S2 = H4 + α2
      Q7 = A_2[α0,α1, β2=α4, β1=α5, β0=α6](S1,S2,(x,H2))

    This is a solver-free coefficient decoder; it mirrors `tools/impl/q_decode.py:decode_Q7`.
    """

    Q7 = _poly_trim(Q7, field)
    H2 = _poly_trim(H2, field)
    H4 = _poly_trim(H4, field)
    if _poly_degree(Q7) != 7 or _poly_coeff(Q7, 7, field) != field.one():
        raise ValueError("Q7 decoder expects monic degree-7 polynomial")
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("Q7 decoder expects monic degree-2 H2")
    if _poly_degree(H4) != 4 or _poly_coeff(H4, 4, field) != field.one():
        raise ValueError("Q7 decoder expects monic degree-4 H4")

    h2_1 = _poly_coeff(H2, 1, field)
    h2_0 = _poly_coeff(H2, 0, field)

    h4_3 = _poly_coeff(H4, 3, field)
    h4_2 = _poly_coeff(H4, 2, field)
    h4_1 = _poly_coeff(H4, 1, field)
    h4_0 = _poly_coeff(H4, 0, field)

    # In A2 notation, n = deg(S1) = deg(S2) = 4.
    n = 4

    # beta0 (=α6) from [x^{n+2}]Q = beta0 + [x^{n+1}]A1 + [x^{n+2}]A2.
    # Here [x^{n+2}]A2 = 1, and [x^{n+1}]A1 = h2_1 + h4_3 (since alpha3 is constant).
    beta0 = field.sub(field.sub(_poly_coeff(Q7, n + 2, field), field.add(h2_1, h4_3)), field.one())

    # High-degree coefficients of A1 and A2 are independent of alpha2/alpha3 and alpha0/alpha1.
    # Use Q_d = A1_{d-1} + beta0*A1_d + A2_d.
    A1_6 = field.one()
    A2_6 = field.one()
    A2_5 = field.add(h2_1, h4_3)

    A1_5 = field.sub(_poly_coeff(Q7, 6, field), field.add(beta0, A2_6))
    # A1_4 from degree 5 equation: Q5 = A1_4 + beta0*A1_5 + A2_5.
    A1_4 = field.sub(_poly_coeff(Q7, 5, field), field.add(field.mul(beta0, A1_5), A2_5))
    beta1 = field.sub(A1_4, field.add(h2_0, field.add(field.mul(h2_1, h4_3), h4_2)))

    # A1_3 depends only on known H2/H4 and beta1.
    A1_3 = field.add(h4_1, field.add(field.mul(h2_1, h4_2), field.mul(field.add(h2_0, beta1), h4_3)))
    # Degree 4 equation: Q4 = A1_3 + beta0*A1_4 + A2_4.
    A2_4 = field.sub(_poly_coeff(Q7, 4, field), field.add(A1_3, field.mul(beta0, A1_4)))
    beta2 = field.sub(A2_4, field.add(h2_0, field.add(field.mul(h2_1, h4_3), h4_2)))

    # A2_3 depends only on known H2/H4 and beta2.
    A2_3 = field.add(h4_1, field.add(field.mul(h2_1, h4_2), field.mul(field.add(h2_0, beta2), h4_3)))
    # Degree 3 equation: Q3 = A1_2 + beta0*A1_3 + A2_3.
    A1_2 = field.sub(_poly_coeff(Q7, 3, field), field.add(field.mul(beta0, A1_3), A2_3))
    base_A1_2 = field.add(h4_0, field.add(field.mul(h2_1, h4_1), field.mul(field.add(h2_0, beta1), h4_2)))
    alpha3 = field.sub(A1_2, base_A1_2)

    # A1_1 = [x^1]((H2+beta1)*(H4+alpha3)), alpha1 doesn't contribute.
    base_A1_1 = field.add(field.mul(h2_1, h4_0), field.mul(field.add(h2_0, beta1), h4_1))
    A1_1 = field.add(base_A1_1, field.mul(alpha3, h2_1))
    # Degree 2 equation: Q2 = A1_1 + beta0*A1_2 + A2_2.
    A2_2 = field.sub(_poly_coeff(Q7, 2, field), field.add(A1_1, field.mul(beta0, A1_2)))
    base_A2_2 = field.add(h4_0, field.add(field.mul(h2_1, h4_1), field.mul(field.add(h2_0, beta2), h4_2)))
    alpha2 = field.sub(A2_2, base_A2_2)

    # A2_1 = [x^1]((H2+beta2)*(H4+alpha2)), alpha0 doesn't contribute.
    base_A2_1 = field.add(field.mul(h2_1, h4_0), field.mul(field.add(h2_0, beta2), h4_1))
    A2_1 = field.add(base_A2_1, field.mul(alpha2, h2_1))

    # Degree 1 equation: Q1 = A1_0 + beta0*A1_1 + A2_1, where A1_0 includes alpha1.
    A1_0 = field.sub(_poly_coeff(Q7, 1, field), field.add(field.mul(beta0, A1_1), A2_1))
    base_A1_0 = field.mul(field.add(h2_0, beta1), field.add(h4_0, alpha3))
    alpha1 = field.sub(A1_0, base_A1_0)

    # Degree 0 equation: Q0 = beta0*A1_0 + A2_0, where A2_0 includes alpha0.
    A2_0 = field.sub(_poly_coeff(Q7, 0, field), field.mul(beta0, A1_0))
    base_A2_0 = field.mul(field.add(h2_0, beta2), field.add(h4_0, alpha2))
    alpha0 = field.sub(A2_0, base_A2_0)

    # Map (beta0,beta1,beta2) to (α6,α5,α4).
    return [alpha0, alpha1, alpha2, alpha3, beta2, beta1, beta0]


# =============================================================================
# Coefficient-level paper encoders for A_fill / Q_known_powers (for peeling decoders)
# =============================================================================


def _poly_paper_q3(*, alpha0: Number, alpha1: Number, alpha2: Number, H2: Poly, field: Field) -> Poly:
    """
    Coefficient-level encoder for:
      Q_3[α0,α1,α2](x,H2) = (x+α2)(H2+α1) + α0
    """

    x = [field.zero(), field.one()]
    t1 = _poly_add_const(x, alpha2, field)
    t2 = _poly_add_const(H2, alpha1, field)
    return _poly_add(_poly_mul(t1, t2, field), [field.coerce(alpha0)], field)


def _poly_paper_A_fill(
    *,
    l: int,
    alpha: List[Number],
    beta: List[Number],
    S1_2l: Poly,
    S2_2l: Poly,
    Hs: List[Poly],
    field: Field,
) -> Poly:
    """
    Coefficient-level encoder matching `_paper_A_fill` (Algorithm `alg:constr-fill`).
    """

    if l < 0:
        raise ValueError("A_fill requires l >= 0")
    if l > 0 and len(Hs) <= l:
        raise ValueError(f"A_fill requires Hs up to index {l} (H_{{2^{l}}})")

    need_alpha = (1 << (l + 1)) - 2
    need_beta = (1 << l) + 1
    if len(alpha) != need_alpha:
        raise ValueError(f"A_fill l={l} needs {need_alpha} alpha params, got {len(alpha)}")
    if len(beta) != need_beta:
        raise ValueError(f"A_fill l={l} needs {need_beta} beta params, got {len(beta)}")

    alpha = [field.coerce(a) for a in alpha]
    beta = [field.coerce(b) for b in beta]

    x = Hs[0]

    def A1(l_: int, S1: Poly) -> Poly:
        if l_ == 0:
            return _poly_trim(S1, field)
        if l_ == 1:
            # A^{(1)}_2 = (H2 + β1) S1 + α1
            t = _poly_mul(_poly_add_const(Hs[1], beta[1], field), S1, field)
            return _poly_add_const(t, alpha[1], field)
        if l_ == 2:
            # S^{(1)}_2 = (H4 + β3) S^{(1)}_4 + Q_3[α3,α4,α5](x,H2)
            q3 = _poly_paper_q3(alpha0=alpha[3], alpha1=alpha[4], alpha2=alpha[5], H2=Hs[1], field=field)
            t = _poly_mul(_poly_add_const(Hs[2], beta[3], field), S1, field)
            S1_2 = _poly_add(t, q3, field)
            # A^{(1)}_4 = (H2 + β1) S^{(1)}_2 + α1
            t2 = _poly_mul(_poly_add_const(Hs[1], beta[1], field), S1_2, field)
            return _poly_add_const(t2, alpha[1], field)

        # l_ >= 3
        k_small = l_ - 1  # Q_{2^{k_small}-1}
        # Q_{2^{l_-1}-1}[β_{2^{l_}-1}, ..., β_{2^{l_-1}+1}] in descending β-index order.
        q_small_params = list(reversed(beta[(1 << (l_ - 1)) + 1 : (1 << l_)]))
        q_small = _poly_paper_Q_known_powers(k=k_small, alpha=q_small_params, Hs=Hs[: l_ - 1], field=field)

        factor = _poly_add(Hs[l_], q_small, field)
        t = _poly_mul(factor, S1, field)

        q_big_params = alpha[(1 << l_) - 1 : (1 << (l_ + 1)) - 2]
        q_big = _poly_paper_Q_known_powers(k=l_, alpha=q_big_params, Hs=Hs[:l_], field=field)
        S1_prev = _poly_add(t, q_big, field)
        return A1(l_ - 1, S1_prev)

    def A2(l_: int, S2: Poly) -> Poly:
        if l_ == 0:
            return _poly_trim(S2, field)
        if l_ == 1:
            # A^{(2)}_2 = (H2 + β2) S2 + α0
            t = _poly_mul(_poly_add_const(Hs[1], beta[2], field), S2, field)
            return _poly_add_const(t, alpha[0], field)
        if l_ == 2:
            # S^{(2)}_2 = (H4 + β4) S^{(2)}_4 + α2
            t = _poly_mul(_poly_add_const(Hs[2], beta[4], field), S2, field)
            S2_2 = _poly_add_const(t, alpha[2], field)
            # A^{(2)}_4 = (H2 + β2) S^{(2)}_2 + α0
            t2 = _poly_mul(_poly_add_const(Hs[1], beta[2], field), S2_2, field)
            return _poly_add_const(t2, alpha[0], field)

        # l_ >= 3
        t = _poly_mul(_poly_add_const(Hs[l_], beta[1 << l_], field), S2, field)
        S2_prev = _poly_add_const(t, alpha[(1 << l_) - 2], field)
        return A2(l_ - 1, S2_prev)

    A1_out = A1(l, S1_2l)
    A2_out = A2(l, S2_2l)

    if l == 0:
        t = _poly_mul(_poly_add_const(x, beta[0], field), A1_out, field)
        return _poly_add_const(_poly_add(t, A2_out, field), beta[1], field)

    t = _poly_mul(_poly_add_const(x, beta[0], field), A1_out, field)
    return _poly_add(t, A2_out, field)


def _poly_paper_Q_known_powers(*, k: int, alpha: List[Number], Hs: List[Poly], field: Field) -> Poly:
    """
    Coefficient-level encoder matching `_paper_Q_known_powers` (Algorithm `alg:constr-known-2n-1`).
    """

    if k < 0:
        raise ValueError("Q_known_powers requires k >= 0")
    need = 1 if k == 0 else (1 << k) - 1
    if len(alpha) != need:
        raise ValueError(f"Q_known_powers k={k} needs {need} alpha params, got {len(alpha)}")
    if k >= 1 and len(Hs) <= k - 1:
        raise ValueError(f"Q_known_powers k={k} needs Hs up to index {k-1} (H_{{2^{k-1}}})")

    alpha = [field.coerce(a) for a in alpha]

    if PEELED_Q and k >= 3:
        m = (1 << (k - 1)) - 1
        gamma = alpha[0]
        W = _poly_paper_Q_known_powers(k=k - 1, alpha=alpha[1 : 1 + m], Hs=Hs[: k - 1], field=field)
        B = _poly_paper_Q_known_powers(k=k - 1, alpha=alpha[1 + m :], Hs=Hs[: k - 1], field=field)
        t = _poly_mul(_poly_add_const(Hs[k - 1], gamma, field), W, field)
        return _poly_add(t, B, field)

    x = Hs[0]
    if k == 0:
        return [alpha[0]]
    if k == 1:
        return _poly_add_const(x, alpha[0], field)
    if k == 2:
        return _poly_paper_q3(alpha0=alpha[0], alpha1=alpha[1], alpha2=alpha[2], H2=Hs[1], field=field)
    if k == 3:
        # Q_7 via A_2 on (H4+α3, H4+α2) with β2=α4, β1=α5, β0=α6.
        H4 = Hs[2]
        S1 = _poly_add_const(H4, alpha[3], field)
        S2 = _poly_add_const(H4, alpha[2], field)
        a_alpha = [alpha[0], alpha[1]]
        beta = [field.zero(), field.zero(), field.zero()]  # β0..β2
        beta[2] = alpha[4]
        beta[1] = alpha[5]
        beta[0] = alpha[6]
        return _poly_paper_A_fill(l=1, alpha=a_alpha, beta=beta, S1_2l=S1, S2_2l=S2, Hs=Hs[:2], field=field)

    # k >= 4
    sub_k = k - 2
    sub_start = (1 << (k - 1)) - 1
    sub_end = (1 << (k - 1)) + (1 << (k - 2)) - 2
    q_sub_params = alpha[sub_start:sub_end]
    q_sub = _poly_paper_Q_known_powers(k=sub_k, alpha=q_sub_params, Hs=Hs[: k - 2], field=field)

    S1 = _poly_add(Hs[k - 1], q_sub, field)
    S2 = _poly_add_const(Hs[k - 1], alpha[(1 << (k - 1)) - 2], field)

    a_alpha = alpha[: (1 << (k - 1)) - 2]
    beta_block_start = (1 << (k - 1)) + (1 << (k - 2)) - 2
    beta_block = alpha[beta_block_start:]
    l = k - 2
    need_beta = (1 << l) + 1
    if len(beta_block) != need_beta:
        raise ValueError("internal error: beta-block length mismatch")

    beta = [field.zero()] * need_beta  # β0..β_{2^l}
    for i, v in enumerate(beta_block):
        beta[(1 << l) - i] = v
    return _poly_paper_A_fill(l=l, alpha=a_alpha, beta=beta, S1_2l=S1, S2_2l=S2, Hs=Hs[: l + 1], field=field)


def _poly_paper_H2(*, x: Poly, alpha0: Number, alpha1: Number, field: Field) -> Poly:
    """
    Coefficient-level encoder for the quadratic base polynomial:
        H2 = (x + alpha1)*x + alpha0 = x^2 + alpha1*x + alpha0.
    """

    x = _poly_trim(x, field)
    if _poly_degree(x) != 1 or _poly_coeff(x, 1, field) != field.one() or _poly_coeff(x, 0, field) != field.zero():
        raise ValueError("_poly_paper_H2 expects x = [0,1]")
    return [field.coerce(alpha0), field.coerce(alpha1), field.one()]


def _poly_square_diff(*, S1: Poly, S2: Poly, field: Field) -> Poly:
    """Coefficient-level square-difference gadget: S1^2 - S2^2."""

    return _poly_sub(_poly_square(S1, field), _poly_square(S2, field), field)


def _poly_paper_Q_2lp1k_minus_1_with_powers(
    *,
    k: int,
    l: int,
    alpha: List[Number],
    Hs: List[Poly],
    field: Field,
) -> Tuple[Poly, List[Poly], Poly]:
    """
    Coefficient-level encoder matching `_paper_Q_2lp1k_minus_1_with_powers`.

    Returns:
      (Q, Hs_out, tilde_out)
    """

    if k < 0 or l < 1:
        raise ValueError("Q_2lp1k_minus_1 requires k>=0 and l>=1")
    x = _poly_trim(Hs[0], field)
    if _poly_degree(x) != 1 or _poly_coeff(x, 1, field) != field.one() or _poly_coeff(x, 0, field) != field.zero():
        raise ValueError("expected Hs[0]=x")

    deg = (1 << (l + 1)) * k + ((1 << l) - 1)
    if deg == 0:
        if len(alpha) != 1:
            raise ValueError("degree-0 Q requires 1 parameter")
        z = [field.coerce(alpha[0])]
        return z, list(Hs), z
    if len(alpha) != deg:
        raise ValueError(f"Q_2lp1k_minus_1(k={k},l={l}) needs {deg} alpha params, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    if k == 0:
        out = _poly_paper_Q_known_powers(k=l, alpha=alpha, Hs=Hs[:l], field=field)
        return out, list(Hs), x

    if l == 1:
        # Special case: Q_{4k+1}(x,H2) using a shifted quadratic input and (x+β0) extraction.
        if len(Hs) < 2:
            raise ValueError("Q_2lp1k_minus_1(l=1) requires Hs=[x,H2]")
        deg = 4 * k + 1
        if len(alpha) != deg:
            raise ValueError(f"Q_2lp1k_minus_1(k={k},l=1) needs {deg} alpha params, got {len(alpha)}")
        t_params = alpha[: 4 * k - 2]
        tilde_shift = alpha[4 * k - 2]
        hat_shift = alpha[4 * k - 1]
        beta0 = alpha[4 * k]

        H2 = _poly_trim(Hs[1], field)
        H_hat = _poly_add_const(H2, hat_shift, field)
        tilde_H2 = _poly_add_const(H_hat, tilde_shift, field)

        S1, S2, Hs_out, tilde_out = _poly_paper_T(
            k=2 * k, l=1, alpha=t_params, Hs=[x, H_hat], tilde_H_2l=tilde_H2, field=field
        )
        out = _poly_add(_poly_mul(_poly_add_const(x, beta0, field), S1, field), S2, field)
        return _poly_trim(out, field), Hs_out, tilde_out

    block = 1 << l
    a_alpha = alpha[: block - 2]  # α0..α_{2^l-3}
    t_start = block - 2
    shift_idx = (1 << (l + 1)) * k - 2  # α_{2^{l+1}k-2}
    t_params = alpha[t_start:shift_idx]  # α_{2^l-2}..α_{2^{l+1}k-3}
    shift = alpha[shift_idx]

    qhat_start = shift_idx + 1
    qhat_len = (1 << (l - 1)) - 1
    qhat_params = alpha[qhat_start : qhat_start + qhat_len]

    beta_start = qhat_start + qhat_len
    beta_len = (1 << (l - 1)) + 1
    beta_params = alpha[beta_start : beta_start + beta_len]
    if len(beta_params) != beta_len or (beta_start + beta_len) != len(alpha):
        raise ValueError("internal error: beta param count mismatch in Q_2lp1k_minus_1")

    # \hat H_{2^l} = H_{2^l} + Q_{2^{l-1}-1}(...), for l>=2.
    if len(Hs) <= l:
        raise ValueError(f"Q_2lp1k_minus_1(l={l}) requires Hs up to index {l} (H_{{2^{l}}})")
    H_hat = _poly_trim(Hs[l], field)
    if l > 1:
        qhat = _poly_paper_Q_known_powers(k=l - 1, alpha=qhat_params, Hs=Hs[: l - 1], field=field)
        H_hat = _poly_add(H_hat, qhat, field)

    # Run T_{2k,2^l} with H_{2^l} replaced by \hat H_{2^l}.
    Hs_hat = list(Hs)
    if len(Hs_hat) <= l:
        raise ValueError("internal error: Hs_hat too short")
    Hs_hat[l] = H_hat
    need_t = (2 * k - 1) * block
    if len(t_params) != need_t:
        raise ValueError(f"internal error: expected {need_t} T-params, got {len(t_params)}")
    S1, S2, Hs_out, tilde_out = _poly_paper_T(
        k=2 * k, l=l, alpha=t_params, Hs=Hs_hat, tilde_H_2l=_poly_add_const(H_hat, shift, field), field=field
    )

    # Final fill A_{2^{l-1}} on (S1,S2).
    A_l = l - 1
    A_beta = [field.zero() for _ in range((1 << A_l) + 1)]  # β0..β_{2^{l-1}}
    for i, v in enumerate(beta_params):
        A_beta[(1 << A_l) - i] = v

    out = _poly_paper_A_fill(l=A_l, alpha=list(a_alpha), beta=A_beta, S1_2l=S1, S2_2l=S2, Hs=Hs[: A_l + 1], field=field)
    return _poly_trim(out, field), Hs_out, tilde_out


def _poly_paper_Q_for_odd_degree_with_powers(
    *,
    deg: int,
    alpha: List[Number],
    Hs: List[Poly],
    field: Field,
) -> Tuple[Poly, List[Poly], Poly]:
    if deg < 1 or (deg % 2) == 0:
        raise ValueError("Q_for_odd_degree requires odd deg >= 1")
    l = _v2_positive(deg + 1)
    odd = (deg + 1) >> l
    if (odd % 2) == 0:
        raise ValueError("internal error: expected odd factor (deg+1)/2^l to be odd")
    k = (odd - 1) // 2
    if PEELED_Q and deg >= 3 and len(Hs) >= deg.bit_length():
        return _poly_QO(deg=deg, alpha=alpha, Hs=Hs, field=field), list(Hs), Hs[0]
    return _poly_paper_Q_2lp1k_minus_1_with_powers(k=k, l=l, alpha=alpha, Hs=Hs, field=field)


def _poly_paper_P7(*, alpha: List[Number], field: Field) -> Poly:
    """
    Coefficient-level encoder matching `_paper_P7` for characteristic != 2.

      y = x * (x + α6)
      z = (α5 + x + y) * (α4 + x)
      w = (α3 + z) * x
      v = (α2 + x + z) * (α1 + w)
      P7 = α0 + y + w + v
    """

    if len(alpha) != 7:
        raise ValueError(f"P7 needs 7 params, got {len(alpha)}")
    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("_poly_paper_P7 only implements the char!=2 variant")
    alpha = [field.coerce(a) for a in alpha]
    x = [field.zero(), field.one()]

    y = _poly_mul(x, _poly_add_const(x, alpha[6], field), field)
    z = _poly_mul(
        _poly_add_const(_poly_add(_poly_add(x, y, field), [alpha[5]], field), field.zero(), field),
        _poly_add_const(x, alpha[4], field),
        field,
    )
    w = _poly_mul(_poly_add_const(z, alpha[3], field), x, field)
    v = _poly_mul(
        _poly_add_const(_poly_add(x, z, field), alpha[2], field),
        _poly_add_const(w, alpha[1], field),
        field,
    )
    out = _poly_add(_poly_add(_poly_add_const(y, alpha[0], field), w, field), v, field)
    return _poly_trim(out, field)


def _poly_paper_P5(*, alpha: List[Number], field: Field) -> Poly:
    """
    Coefficient-level encoder matching `_paper_P5`:

      P5[α0..α4](x) = (x + α2) * ( (x^2 + α4) * (x^2 + x + α3) + α1 ) + α0
    """

    if len(alpha) != 5:
        raise ValueError(f"P5 needs 5 params, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]
    x = [field.zero(), field.one()]

    x2 = _poly_square(x, field)
    z = _poly_mul(_poly_add_const(x2, alpha[4], field), _poly_add_const(_poly_add(x2, x, field), alpha[3], field), field)
    w = _poly_mul(_poly_add_const(x, alpha[2], field), _poly_add_const(z, alpha[1], field), field)
    out = _poly_add_const(w, alpha[0], field)
    return _poly_trim(out, field)


def _poly_paper_barQ_15(*, alpha: List[Number], H2: Poly, H4: Poly, field: Field) -> Poly:
    """
    Coefficient-level encoder matching `_paper_barQ_15` (special case 31 gadget).
    """

    if len(alpha) != 15:
        raise ValueError(f"barQ_15 needs 15 parameters, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]
    x = [field.zero(), field.one()]

    a_h8, b_h8, c_h8 = alpha[0], alpha[1], alpha[2]
    d_shift = alpha[3]
    a_alpha = alpha[4:10]
    beta = alpha[10:15]

    A = _poly_add_const(x, b_h8, field)
    B = _poly_add_const(_poly_trim(H2, field), c_h8, field)
    H8 = _poly_add_const(
        _poly_mul(_poly_add(_poly_trim(H4, field), A, field), _poly_add(_poly_trim(H4, field), B, field), field),
        a_h8,
        field,
    )
    S1 = H8
    S2 = _poly_add_const(H8, d_shift, field)
    return _poly_paper_A_fill(l=2, alpha=list(a_alpha), beta=list(beta), S1_2l=S1, S2_2l=S2, Hs=[x, H2, H4], field=field)


def _poly_paper_barQ_8k_plus_7_with_powers(
    *,
    k: int,
    alpha: List[Number],
    H2: Poly,
    H4: Poly,
    field: Field,
) -> Tuple[Poly, List[Poly]]:
    """
    Coefficient-level encoder matching `_paper_barQ_8k_plus_7_with_powers`.

    Returns:
      (barQ, Hs_out).
    """

    if k < 2:
        raise ValueError("barQ_{8k+7} requires k>=2")
    deg = 8 * k + 7
    if len(alpha) != deg:
        raise ValueError(f"barQ_{{8k+7}} (k={k}) needs {deg} parameters, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    x = [field.zero(), field.one()]

    a_h8, b_h8, c_h8, d_tilde = alpha[0:4]
    t_len = (k - 1) * 8
    t_params = alpha[4 : 4 + t_len]
    fill = alpha[4 + t_len :]
    a_alpha = fill[:6]
    beta = fill[6:]
    if len(a_alpha) != 6 or len(beta) != 5:
        raise ValueError("internal error: barQ_{8k+7} fill parameter partition mismatch")

    H8 = _poly_add_const(
        _poly_mul(
            _poly_add(_poly_trim(H4, field), _poly_add_const(x, b_h8, field), field),
            _poly_add(_poly_trim(H4, field), _poly_add_const(_poly_trim(H2, field), c_h8, field), field),
            field,
        ),
        a_h8,
        field,
    )
    tilde_H8 = _poly_add_const(H8, d_tilde, field)

    S1, S2, Hs_out, _tilde_out = _poly_paper_T(
        k=k, l=3, alpha=t_params, Hs=[x, H2, H4, H8], tilde_H_2l=tilde_H8, field=field
    )
    out = _poly_paper_A_fill(l=2, alpha=list(a_alpha), beta=list(beta), S1_2l=S1, S2_2l=S2, Hs=[x, H2, H4], field=field)
    return _poly_trim(out, field), list(Hs_out)


def _poly_paper_barQ_odd_with_H2_H4_with_powers(
    *,
    deg: int,
    alpha: List[Number],
    Hs_in: List[Poly],
    field: Field,
) -> Tuple[Poly, List[Poly]]:
    """
    Coefficient-level encoder matching `_paper_barQ_odd_with_H2_H4_with_powers`.
    """

    if deg < 1 or (deg % 2) == 0:
        raise ValueError("barQ requires odd deg >= 1")
    if len(alpha) != deg:
        raise ValueError(f"barQ_{deg} needs {deg} alpha params, got {len(alpha)}")
    if len(Hs_in) < 2:
        raise ValueError("barQ requires Hs_in=[x,H2,...]")
    alpha = [field.coerce(a) for a in alpha]

    l_need = _v2_positive(deg + 1)
    odd = (deg + 1) >> l_need
    kk = (odd - 1) // 2
    need = l_need + 1 if kk > 0 else l_need
    if len(Hs_in) >= need:
        q, Hs_out, _ = _poly_paper_Q_for_odd_degree_with_powers(deg=deg, alpha=alpha, Hs=Hs_in, field=field)
        return _poly_trim(q, field), list(Hs_out)

    if len(Hs_in) < 3:
        raise ValueError("barQ fallback requires H4 (Hs_in[2]) to be available")
    x = _poly_trim(Hs_in[0], field)
    H2 = _poly_trim(Hs_in[1], field)
    H4 = _poly_trim(Hs_in[2], field)

    if deg == 15:
        return _poly_paper_barQ_15(alpha=alpha, H2=H2, H4=H4, field=field), list(Hs_in)

    if (deg % 8) == 7 and deg >= 23:
        k = (deg - 7) // 8
        out, powers_out = _poly_paper_barQ_8k_plus_7_with_powers(k=k, alpha=alpha, H2=H2, H4=H4, field=field)
        Hs_out = list(Hs_in)
        if len(Hs_out) < len(powers_out):
            Hs_out.extend(powers_out[len(Hs_out) :])
        return _poly_trim(out, field), Hs_out

    raise ValueError(
        f"internal error: no barQ fallback case matched for deg={deg} (need={need}, have={len(Hs_in)})"
    )


def _poly_paper_splittable_pair(
    *,
    n: int,
    alpha: List[Number],
    field: Field,
) -> Tuple[Poly, Poly, List[Poly]]:
    """
    Coefficient-level encoder matching `_paper_splittable_pair`.

    Returns:
      (T1, T2, Hs) where Hs[i] is monic degree 2^i, Hs[0]=x.
    """

    if n < 1 or (n % 2) == 0:
        raise ValueError("splittable_pair requires odd n >= 1")
    if n == 7:
        raise ValueError("no splittable pair is used for n=7; use the septic base construction instead")
    if len(alpha) != n:
        raise ValueError(f"splittable_pair({n}) needs {n} params, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    x = [field.zero(), field.one()]

    if n == 1:
        return [field.one()], [alpha[0]], [x]

    if n == 3:
        H2 = _poly_paper_H2(x=x, alpha0=alpha[1], alpha1=alpha[2], field=field)
        return H2, _poly_add_const(H2, alpha[0], field), [x, H2]

    # Special cases.
    if n == 15:
        H2 = _poly_paper_H2(x=x, alpha0=alpha[6], alpha1=alpha[7], field=field)
        x_shift = _poly_add_const(x, alpha[5], field)
        H4 = _poly_add_const(_poly_square_diff(S1=H2, S2=x_shift, field=field), alpha[4], field)

        S1 = _poly_paper_Q_known_powers(k=3, alpha=alpha[8:15], Hs=[x, H2, H4], field=field)
        S2 = _poly_add_const(H2, alpha[3], field)
        T1 = _poly_add_const(_poly_square_diff(S1=S1, S2=S2, field=field), alpha[1], field)

        # Easier: T2_low = square_diff(H4, H2+α2) + α0.
        T2_low = _poly_add_const(_poly_square_diff(S1=H4, S2=_poly_add_const(H2, alpha[2], field), field=field), alpha[0], field)
        T2 = _poly_add(T2_low, T1, field)
        H8 = T2_low
        return _poly_trim(T1, field), _poly_trim(T2, field), [x, H2, H4, H8]

    if n == 27:
        H2 = _poly_paper_H2(x=x, alpha0=alpha[2], alpha1=alpha[3], field=field)
        S1, Hs_out, _ = _poly_paper_Q_2lp1k_minus_1_with_powers(k=3, l=1, alpha=alpha[14:27], Hs=[x, H2], field=field)
        if len(Hs_out) <= 2:
            raise ValueError("internal error: expected H4 byproduct in Q_13")
        H4 = Hs_out[2]
        Hs = [x, H2] + list(Hs_out[2:])

        S2 = _poly_paper_q3(alpha0=alpha[4], alpha1=alpha[5], alpha2=alpha[6], H2=H2, field=field)
        S3 = _poly_paper_Q_known_powers(k=3, alpha=alpha[7:14], Hs=[x, H2, H4], field=field)

        T1 = _poly_add_const(_poly_square_diff(S1=S1, S2=S2, field=field), alpha[1], field)
        T2_low = _poly_add_const(_poly_square_diff(S1=S3, S2=H2, field=field), alpha[0], field)
        T2 = _poly_add(T2_low, T1, field)
        return _poly_trim(T1, field), _poly_trim(T2, field), Hs

    if n == 31:
        H2 = _poly_paper_H2(x=x, alpha0=alpha[6], alpha1=alpha[7], field=field)
        x_shift = _poly_add_const(x, alpha[5], field)
        H4 = _poly_add_const(_poly_square_diff(S1=H2, S2=x_shift, field=field), alpha[4], field)

        S1, _Hs_out = _poly_paper_barQ_odd_with_H2_H4_with_powers(
            deg=15, alpha=alpha[16:31], Hs_in=[x, H2, H4], field=field
        )
        S2 = _poly_paper_Q_known_powers(k=3, alpha=alpha[8:15], Hs=[x, H2, H4], field=field)
        S3 = _poly_paper_q3(alpha0=alpha[1], alpha1=alpha[2], alpha2=alpha[3], H2=H2, field=field)
        T1 = _poly_add(_poly_square_diff(S1=S1, S2=S2, field=field), S3, field)

        T2 = _poly_add_const(
            _poly_square_diff(S1=_poly_add_const(S1, alpha[15], field), S2=H4, field=field),
            alpha[0],
            field,
        )
        return _poly_trim(T1, field), _poly_trim(T2, field), [x, H2, H4]

    # Main families.
    if (n % 4) == 1:
        k = (n - 1) // 4
        t_params = alpha[: n - 3]
        tilde_shift = alpha[n - 3]
        h2_const = alpha[n - 2]
        h2_lin = alpha[n - 1]

        H2 = _poly_paper_H2(x=x, alpha0=h2_const, alpha1=h2_lin, field=field)
        tilde_H2 = _poly_add_const(H2, tilde_shift, field)
        T1, T2, Hs_out, _ = _poly_paper_T(k=2 * k, l=1, alpha=t_params, Hs=[x, H2], tilde_H_2l=tilde_H2, field=field)
        return _poly_trim(T1, field), _poly_trim(T2, field), Hs_out

    if (n % 8) == 3:
        k = (n - 3) // 8
        sub_n = 2 * k + 1
        S1_1, S1_2, Hs = _poly_paper_splittable_pair(n=sub_n, alpha=alpha[2 * k : 4 * k + 1], field=field)
        if len(Hs) < 2:
            raise ValueError("internal error: expected H2 in splittable_pair output")
        H2 = Hs[1]

        S2, Hs2_raw, _ = _poly_paper_Q_2lp1k_minus_1_with_powers(k=k, l=1, alpha=alpha[4 * k + 2 : 8 * k + 3], Hs=[x, H2], field=field)
        if len(Hs2_raw) <= 2:
            raise ValueError("internal error: expected an H4 byproduct in Q_{4k+1}")
        Hs2 = [x, H2] + list(Hs2_raw[2:])

        if k == 1:
            S3 = [alpha[1]]
            Hs3 = list(Hs2)
        else:
            deg3 = 2 * k - 1
            S3, Hs3, _ = _poly_paper_Q_for_odd_degree_with_powers(deg=deg3, alpha=alpha[1 : 2 * k], Hs=Hs2, field=field)

        if len(Hs) > len(Hs2):
            Hs2 = list(Hs2) + list(Hs[len(Hs2) :])
        if len(Hs3) > len(Hs2):
            Hs2 = list(Hs2) + list(Hs3[len(Hs2) :])

        T1 = _poly_add(_poly_square_diff(S1=S2, S2=S1_1, field=field), S3, field)
        T2 = _poly_add_const(
            _poly_square_diff(S1=_poly_add_const(S2, alpha[4 * k + 1], field), S2=S1_2, field=field),
            alpha[0],
            field,
        )
        return _poly_trim(T1, field), _poly_trim(T2, field), Hs2

    if (n % 8) == 7:
        k = (n - 7) // 8
        sub_n = 2 * k + 1
        S1_1, S1_2, Hs = _poly_paper_splittable_pair(n=sub_n, alpha=alpha[: 2 * k + 1], field=field)
        if len(Hs) < 2:
            raise ValueError("internal error: expected H2 in splittable_pair output for 8k+7 case")
        H2 = Hs[1]

        def build_Q(*, deg: int, params: List[Number], Hs_in: List[Poly]) -> Tuple[Poly, List[Poly]]:
            l = _v2_positive(deg + 1)
            odd = (deg + 1) >> l
            kk = (odd - 1) // 2
            need = l + 1 if kk > 0 else l
            if len(Hs_in) >= need:
                q, Hs_out, _ = _poly_paper_Q_for_odd_degree_with_powers(deg=deg, alpha=params, Hs=Hs_in, field=field)
                return _poly_trim(q, field), list(Hs_out)
            q, Hs_out = _poly_paper_barQ_odd_with_H2_H4_with_powers(deg=deg, alpha=params, Hs_in=Hs_in, field=field)
            return _poly_trim(q, field), list(Hs_out)

        # S2 = Q_{2k+1}[...].
        S2, Hs = build_Q(deg=sub_n, params=alpha[2 * k + 2 : 4 * k + 3], Hs_in=Hs)
        if len(Hs) < 3:
            raise ValueError("internal error: expected H4 to remain available after Q_{2k+1}")

        # S3 = Q_{4k+3}[...].
        S3, Hs = build_Q(deg=4 * k + 3, params=alpha[4 * k + 4 : 8 * k + 7], Hs_in=Hs)

        T1 = _poly_add(_poly_square_diff(S1=S3, S2=S2, field=field), S1_1, field)
        S2_shift = _poly_add_const(S2, alpha[2 * k + 1], field)
        S3_shift = _poly_add_const(S3, alpha[4 * k + 3], field)
        T2 = _poly_add(_poly_square_diff(S1=S3_shift, S2=S2_shift, field=field), S1_2, field)
        return _poly_trim(T1, field), _poly_trim(T2, field), Hs

    raise ValueError(f"internal error: no splittable case matched for odd n={n}")


def _poly_paper_P_from_params(*, params: List[Number], field: Field) -> Poly:
    """
    Coefficient-level encoder for the full paper family P_n[α].

    Returns coefficient list [a0..a_{n-1}, 1] for the monic polynomial of degree n.
    """

    if not params:
        raise ValueError("params must be non-empty")
    params = [field.coerce(a) for a in params]
    n = len(params)

    x = [field.zero(), field.one()]
    if n == 1:
        return _poly_add_const(x, params[0], field)
    if n == 5:
        return _poly_paper_P5(alpha=params, field=field)
    if n == 7:
        return _poly_paper_P7(alpha=params, field=field)
    if (n % 2) == 0:
        # P_n = α0 + x*P_{n-1}(α1..)
        q = _poly_paper_P_from_params(params=params[1:], field=field)
        return _poly_add_const(_poly_mul(q, x, field), params[0], field)

    T1, T2, _Hs = _poly_paper_splittable_pair(n=n, alpha=params, field=field)
    return _poly_add(_poly_mul(T1, x, field), T2, field)


def _poly_paper_T(
    *,
    k: int,
    l: int,
    alpha: List[Number],
    Hs: List[Poly],
    tilde_H_2l: Poly,
    field: Field,
) -> Tuple[Poly, Poly, List[Poly], Poly]:
    """
    Coefficient-level encoder matching `_paper_T` (splittable-pair recursion).

    This is intended for coefficient-level decoding routines that need to
    re-materialize tail-only / zero-parameter instances (paper “derivable”
    polynomials) without using probing.

    Currently only supports char(F) != 2.
    """

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("_poly_paper_T is not implemented for char(F)=2")

    if k < 1:
        raise ValueError("T requires k >= 1")
    if l < 1:
        raise ValueError("T requires l >= 1")
    if len(Hs) <= l:
        raise ValueError(f"T(k={k},l={l}) requires Hs up to index {l} (H_{{2^{l}}})")

    block = 1 << l
    need = (k - 1) * block
    if len(alpha) != need:
        raise ValueError(f"T(k={k},l={l}) needs {(k-1)}*2^{l}={need} alpha params, got {len(alpha)}")
    alpha = [field.coerce(a) for a in alpha]

    x = _poly_trim(Hs[0], field)
    tilde_H_2l = _poly_trim(tilde_H_2l, field)

    if k == 1:
        return _poly_trim(Hs[l], field), tilde_H_2l, list(Hs), tilde_H_2l

    # Even k
    if (k % 2) == 0:
        rec_len = (k // 2 - 1) * (2 * block)
        tail = alpha[rec_len:]
        rec_params = alpha[:rec_len]
        if len(tail) != block:
            raise ValueError("internal error: T even tail length mismatch")

        if l == 1:
            a0, a1 = tail[0], tail[1]
            H2 = _poly_trim(Hs[1], field)
            x_plus = _poly_add_const(x, a1, field)
            H4 = _poly_add(_poly_sub(_poly_square(H2, field), _poly_square(x_plus, field), field), [a0], field)
            Ht2 = _poly_trim(tilde_H_2l, field)
            delta = _poly_sub(Ht2, H2, field)
            if len(_poly_trim(delta, field)) > 1:
                raise ValueError("The shared l=1 base requires tilde_H2-H2 to be scalar")
            tilde_H4 = _poly_add(H4, delta, field)

            Hs_next = list(Hs)
            if len(Hs_next) <= 2:
                Hs_next.extend([[field.zero()]] * (3 - len(Hs_next)))
            Hs_next[2] = _poly_trim(H4, field)
            return _poly_paper_T(
                k=k // 2, l=l + 1, alpha=rec_params, Hs=Hs_next, tilde_H_2l=tilde_H4, field=field
            )

        # l >= 2
        half = 1 << (l - 1)
        q_hi = _poly_paper_Q_known_powers(k=l - 1, alpha=tail[half + 1 :], Hs=Hs[: l - 1], field=field)
        q_lo = _poly_paper_Q_known_powers(k=l - 1, alpha=tail[1:half], Hs=Hs[: l - 1], field=field)

        S1_1 = _poly_add(Hs[l - 1], q_hi, field)
        S1_2 = _poly_trim(q_lo, field)
        H_next = _poly_add(_poly_mul(_poly_add(Hs[l], S1_1, field), _poly_sub(Hs[l], S1_1, field), field), S1_2, field)

        S2_1 = _poly_add_const(Hs[l - 1], tail[half], field)
        S2_2 = [tail[0]]
        tilde_next = _poly_add(
            _poly_mul(_poly_add(tilde_H_2l, S2_1, field), _poly_sub(tilde_H_2l, S2_1, field), field),
            S2_2,
            field,
        )

        Hs_next = list(Hs)
        if len(Hs_next) <= l + 1:
            Hs_next.extend([[field.zero()]] * (l + 2 - len(Hs_next)))
        Hs_next[l + 1] = _poly_trim(H_next, field)
        return _poly_paper_T(
            k=k // 2, l=l + 1, alpha=rec_params, Hs=Hs_next, tilde_H_2l=tilde_next, field=field
        )

    # Odd k
    m = (k - 1) // 2
    if l == 2:
        if block != 4:
            raise ValueError("internal error: expected block=4 for l=2")
        head = alpha[:4]
        tail = alpha[-4:]
        mid = alpha[4:-4]

        H2 = _poly_trim(Hs[1], field)
        H4 = _poly_trim(Hs[2], field)

        # Tail parameters follow the shared-product odd base:
        #   tail[0]=α_{4k-8} : shift from H8 to tilde_H8
        #   tail[1]=α_{4k-7} : S1_3
        #   tail[2]=α_{4k-6} : S1_2 shift in (x+α)
        #   tail[3]=α_{4k-5} : shift in S1_1 = H2 + (x+α)
        next_shift, s1_3, s1_2_shift, s1_1_shift = tail[0], tail[1], tail[2], tail[3]

        # First branch:
        #   S1_1 = H2 + (x + s1_1_shift)
        #   S1_2 = x + s1_2_shift
        #   S1_3 = s1_3
        S1_1 = _poly_add(H2, _poly_add_const(x, s1_1_shift, field), field)
        core = _poly_add(H4, S1_1, field)
        S1_2 = _poly_add_const(x, s1_2_shift, field)
        H8 = _poly_add(
            _poly_mul(_poly_add(core, S1_2, field), _poly_sub(core, S1_2, field), field),
            [s1_3],
            field,
        )

        Hs_next = list(Hs)
        if len(Hs_next) <= 3:
            Hs_next.extend([[field.zero()]] * (4 - len(Hs_next)))
        Hs_next[3] = _poly_trim(H8, field)

        rho = _poly_sub(_poly_trim(tilde_H_2l, field), H4, field)
        if len(_poly_trim(rho, field)) > 1:
            raise ValueError("The shared odd l=2 base requires tilde_H4-H4 to be scalar")
        S2_1 = _poly_sub(S1_1, rho, field)
        tilde_H8 = _poly_add(H8, [next_shift], field)

        T1_rec, T2_rec, Hs_out, tilde_out = _poly_paper_T(k=m, l=l + 1, alpha=mid, Hs=Hs_next, tilde_H_2l=tilde_H8, field=field)

        q3 = _poly_paper_Q_known_powers(k=2, alpha=head[1:], Hs=Hs[:2], field=field)
        factor1 = _poly_sub(H4, _poly_scale_int(S1_1, k - 1, field), field)
        T1 = _poly_add(_poly_mul(factor1, T1_rec, field), q3, field)

        factor2 = _poly_sub(_poly_trim(tilde_H_2l, field), _poly_scale_int(S2_1, k - 1, field), field)
        T2 = _poly_add_const(_poly_mul(factor2, T2_rec, field), head[0], field)
        return _poly_trim(T1, field), _poly_trim(T2, field), Hs_out, tilde_out

    if l < 3:
        raise ValueError("T odd case requires l >= 3 (or special l=2)")

    head = alpha[:block]
    tail = alpha[-block:]
    mid = alpha[block:-block]
    half = 1 << (l - 1)
    quarter = 1 << (l - 2)

    q_hi = _poly_paper_Q_known_powers(k=l - 1, alpha=tail[half + 1 :], Hs=Hs[: l - 1], field=field)
    S1_1 = _poly_add(Hs[l - 1], q_hi, field)

    q_mid = _poly_paper_Q_known_powers(k=l - 2, alpha=tail[quarter + 1 : half], Hs=Hs[: l - 2], field=field)
    S1_2 = _poly_add(Hs[l - 2], q_mid, field)

    S1_3 = _poly_paper_Q_known_powers(k=l - 2, alpha=tail[1:quarter], Hs=Hs[: l - 2], field=field)

    base = _poly_add(Hs[l], S1_1, field)
    H_next = _poly_add(_poly_mul(_poly_add(base, S1_2, field), _poly_sub(base, S1_2, field), field), S1_3, field)

    S2_1 = _poly_add_const(Hs[l - 1], tail[half], field)
    S2_2 = _poly_add_const(Hs[l - 2], tail[quarter], field)
    S2_3 = [tail[0]]
    base2 = _poly_add(tilde_H_2l, S2_1, field)
    tilde_next = _poly_add(_poly_mul(_poly_add(base2, S2_2, field), _poly_sub(base2, S2_2, field), field), S2_3, field)

    Hs_next = list(Hs)
    if len(Hs_next) <= l + 1:
        Hs_next.extend([[field.zero()]] * (l + 2 - len(Hs_next)))
    Hs_next[l + 1] = _poly_trim(H_next, field)

    T1_rec, T2_rec, Hs_out, tilde_out = _poly_paper_T(
        k=m, l=l + 1, alpha=mid, Hs=Hs_next, tilde_H_2l=tilde_next, field=field
    )

    q_low = _poly_paper_Q_known_powers(k=l, alpha=head[1:], Hs=Hs[:l], field=field)
    factor1 = _poly_sub(Hs[l], _poly_scale_int(S1_1, k - 1, field), field)
    T1 = _poly_add(_poly_mul(factor1, T1_rec, field), q_low, field)

    factor2 = _poly_sub(tilde_H_2l, _poly_scale_int(S2_1, k - 1, field), field)
    T2 = _poly_add_const(_poly_mul(factor2, T2_rec, field), head[0], field)
    return _poly_trim(T1, field), _poly_trim(T2, field), Hs_out, tilde_out


def _poly_remainder_poly_from_T(
    *,
    k: int,
    l: int,
    alpha: List[Number],
    Hs: List[Poly],
    tilde_H_2l: Poly,
    field: Field,
) -> Poly:
    """
    Compute the proof-remainder polynomial:
        P_R := x (T^{(1)}_{k,2^l} - H_{2^l}^k) + (T^{(2)}_{k,2^l} - \\tilde H_{2^l}^k)
    for the coefficient-level `_poly_paper_T` encoder.
    """

    x = _poly_trim(Hs[0], field)
    H_base = _poly_trim(Hs[l], field)
    T1, T2, _Hs_out, _tilde_out = _poly_paper_T(k=k, l=l, alpha=alpha, Hs=Hs, tilde_H_2l=tilde_H_2l, field=field)

    H_pow = _poly_pow(H_base, k, field)
    Ht_pow = _poly_pow(_poly_trim(tilde_H_2l, field), k, field)
    left = _poly_shift_xk(_poly_sub(T1, H_pow, field), 1, field)
    right = _poly_sub(T2, Ht_pow, field)
    return _poly_add(left, right, field)


def _decode_R_k(
    *,
    k: int,
    l: int,
    P_R: Poly,
    Hs: List[Poly],
    tilde_H_2l: Poly,
    field: Field,
) -> Tuple[List[Number], List[Poly], Poly]:
    """
    Decode the remainder polynomial `P_R = x R^{(1)}_{k,2^l} + R^{(2)}_{k,2^l}`.

    Returns:
      (alpha_block, Hs_out, tilde_out)

    This is a coefficient-level port of the paper-shaped peeling decoders in
    `tools/impl/splittable_decode.py`, but restricted (for now) to the even-k
    branch. Odd-k decoding is not implemented yet.
    """

    if k < 1:
        raise ValueError("k must be >= 1")
    if l < 1:
        raise ValueError("l must be >= 1")
    if len(Hs) <= l:
        raise ValueError("Hs must include H_{2^l} at index l")

    if k == 1:
        return [], list(Hs), _poly_trim(tilde_H_2l, field)
    if (k % 2) != 0:
        return _decode_R_odd_k(k=k, l=l, P_R=P_R, Hs=Hs, tilde_H_2l=tilde_H_2l, field=field)

    return _decode_R_even_k(k=k, l=l, P_R=P_R, Hs=Hs, tilde_H_2l=tilde_H_2l, field=field)


def _decode_R_even_k(
    *,
    k: int,
    l: int,
    P_R: Poly,
    Hs: List[Poly],
    tilde_H_2l: Poly,
    field: Field,
) -> Tuple[List[Number], List[Poly], Poly]:
    """
    Even-k branch of `_decode_R_k` (paper Algorithm `alg:decode-Rk2l` / Lemma R_{k,2^l}).

    Handles both the shared l==1 base (`alg:constr-Tk2l-base`) and l>=2.
    """

    if k < 2 or (k % 2) != 0:
        raise ValueError("decode_R_even_k expects even k>=2")

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("R-decoding requires char(F) != 2")
    inv2 = field.inv(two)

    if l == 1:
        # Shared even-k l==1 base (`alg:constr-Tk2l-base`):
        #   H4 = H2^2 - (x + a1)^2 + a0,   tilde_H4 = H4 + (tilde_H2 - H2).
        # The two tail scalars are descending affine pivots of P_R at degrees
        # 2k-2 and 2k-3; at degree 2k-3 the inner remainder contributes only
        # through its constant leading coefficient (`lem:Rk2l-leading-coeff`),
        # so probing the tail-only remainder encoder yields exact pivot data.
        P_R = _poly_trim(P_R, field)
        H2 = _poly_trim(Hs[1], field)
        tilde_H2 = _poly_trim(tilde_H_2l, field)
        if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
            raise ValueError("expected monic degree-2 H2 for l==1 remainder decoder")
        if _poly_degree(tilde_H2) != 2 or _poly_coeff(tilde_H2, 2, field) != field.one():
            raise ValueError("expected monic degree-2 tilde_H2 for l==1 remainder decoder")
        delta = _poly_trim(_poly_sub(tilde_H2, H2, field), field)
        if _poly_degree(delta) > 0:
            raise ValueError("the shared l==1 base requires tilde_H2 - H2 to be a scalar")

        m_int = k // 2
        total = (k - 1) * 2
        x = [field.zero(), field.one()]

        def _tail_remainder(a0: Number, a1: Number) -> Poly:
            al = [field.zero()] * total
            al[total - 2] = a0
            al[total - 1] = a1
            return _poly_remainder_poly_from_T(k=k, l=1, alpha=al, Hs=Hs, tilde_H_2l=tilde_H2, field=field)

        tail_vals = [field.zero(), field.zero()]  # (a0, a1)
        for idx, row in ((1, 2 * k - 2), (0, 2 * k - 3)):
            base = _tail_remainder(tail_vals[0], tail_vals[1])
            probe_vals = list(tail_vals)
            probe_vals[idx] = field.add(probe_vals[idx], field.one())
            probe = _tail_remainder(probe_vals[0], probe_vals[1])
            slope = field.sub(_poly_coeff(probe, row, field), _poly_coeff(base, row, field))
            if field.is_zero(slope):
                raise ValueError("l==1 even decoder: zero pivot slope (field not admissible?)")
            tail_vals[idx] = field.div(
                field.sub(_poly_coeff(P_R, row, field), _poly_coeff(base, row, field)), slope
            )
        alpha_const, alpha_shift = tail_vals[0], tail_vals[1]

        # Build (H4, tilde_H4) and isolate the inner remainder exactly.
        x_plus = _poly_add_const(x, alpha_shift, field)
        H4 = _poly_add(_poly_sub(_poly_square(H2, field), _poly_square(x_plus, field), field), [alpha_const], field)
        tilde_H4 = _poly_trim(_poly_add(H4, delta, field), field)

        base_poly = _poly_add(
            _poly_shift_xk(_poly_sub(_poly_pow(H4, m_int, field), _poly_pow(H2, k, field), field), 1, field),
            _poly_sub(_poly_pow(tilde_H4, m_int, field), _poly_pow(tilde_H2, k, field), field),
            field,
        )
        P_inner = _poly_sub(P_R, base_poly, field)

        inner_alphas: List[Number] = []
        Hs_out = [Hs[0], H2, _poly_trim(H4, field)]
        tilde_out = tilde_H4
        if m_int > 1:
            inner_alphas, Hs_out, tilde_out = _decode_R_k(
                k=m_int, l=2, P_R=P_inner, Hs=[Hs[0], H2, _poly_trim(H4, field)], tilde_H_2l=tilde_H4, field=field
            )

        full = list(inner_alphas) + [alpha_const, alpha_shift]
        if len(full) != total:
            raise ValueError("internal: decoded alpha count mismatch (l==1 even decoder)")
        return full, Hs_out, tilde_out

    # l>=2 branch
    D = 1 << l
    total = (k - 1) * D
    d = (k - 2) * D
    m = k // 2
    inv_m = field.inv(field.coerce(m))

    P_R = _poly_trim(P_R, field)
    H = _poly_trim(Hs[l], field)
    H_half = _poly_trim(Hs[l - 1], field)
    tilde_H_2l = _poly_trim(tilde_H_2l, field)

    H_pow = _poly_pow(H, k - 2, field)
    Ht_pow = _poly_pow(tilde_H_2l, k - 2, field)

    # Stage 1: recover S1_1 from the top window (> d + D/2) by peeling the monic factor.
    known_tilde_top = _poly_scale_int(_poly_mul(_poly_square(H_half, field), Ht_pow, field), -1, field)

    max_prod_deg = d + D
    prod = [field.zero()] * (max_prod_deg + 1)
    for u_deg in range(D, (D // 2) - 1, -1):
        p_deg = d + u_deg
        pr_deg = p_deg + 1
        rhs = field.sub(field.mul(_poly_coeff(P_R, pr_deg, field), inv_m), _poly_coeff(known_tilde_top, pr_deg, field))
        prod[p_deg] = field.neg(rhs)

    S1_1_sq_high = _recover_monic_factor_high_coeffs_from_product(
        product=prod,
        known_factor=H_pow,
        factor_deg=D,
        min_deg=D // 2,
        field=field,
    )
    S1_1_sq_poly: Poly = [field.zero()] * (D + 1)
    for deg_i, coeff_i in S1_1_sq_high.items():
        S1_1_sq_poly[deg_i] = field.coerce(coeff_i)
    S1_1_sq_poly[D] = field.one()
    S1_1 = _monic_sqrt_from_high_square_coeffs(S1_1_sq_poly, root_deg=D // 2, field=field)

    # Decode the embedded Q_{2^{l-1}-1} block in S1_1: Q_hi = S1_1 - H_half.
    Q_hi = _poly_sub(S1_1, H_half, field)
    k_q = l - 1
    q_hi_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=Q_hi, k=k_q, Hs=Hs[: l - 1], field=field)

    # Stage 1.5: recover scalar shift s in S2_1 = H_half + s from the boundary degree.
    target_deg = d + (D // 2)
    C_tdeg = field.mul(_poly_coeff(P_R, target_deg, field), inv_m)
    x_neg_s1_sq_hpow = _poly_shift_xk(
        _poly_scale_int(_poly_mul(_poly_square(S1_1, field), H_pow, field), -1, field), 1, field
    )
    tilde_base = _poly_coeff(known_tilde_top, target_deg, field)
    s2_1_shift = field.mul(field.sub(field.add(field.add(_poly_coeff(x_neg_s1_sq_hpow, target_deg, field), field.one()), tilde_base), C_tdeg), inv2)
    S2_1 = _poly_add_const(H_half, s2_1_shift, field)
    tilde_term = _poly_scale_int(_poly_mul(_poly_square(S2_1, field), Ht_pow, field), -1, field)

    # Stage 2: recover S1_2 coefficients in degrees >= 1 via monic-factor peeling.
    factor_deg = (D // 2) - 1
    prod2 = [field.zero()] * (d + (D // 2) + 1)
    for u_deg in range((D // 2) - 1, 0, -1):
        pr_deg = d + u_deg + 1
        if pr_deg <= d + 1:
            continue
        C_pr = field.mul(_poly_coeff(P_R, pr_deg, field), inv_m)
        known = field.add(_poly_coeff(x_neg_s1_sq_hpow, pr_deg, field), _poly_coeff(tilde_term, pr_deg, field))
        rhs = field.sub(C_pr, known)
        prod2[pr_deg - 1] = rhs

    S1_2_high = _recover_monic_factor_high_coeffs_from_product(
        product=prod2,
        known_factor=H_pow,
        factor_deg=factor_deg,
        min_deg=1,
        field=field,
    )
    S1_2_no_const: Poly = [field.zero()] * (factor_deg + 1)
    for deg_i, coeff_i in S1_2_high.items():
        if deg_i <= factor_deg:
            S1_2_no_const[deg_i] = field.coerce(coeff_i)
    S1_2_no_const[0] = field.zero()
    S1_2_no_const = _poly_trim(S1_2_no_const, field)

    # Boundary degrees: solve the constant term of S1_2 and the scalar S2_2.
    #
    # We compute the paper's boundary-error coefficients (e_{d+1}, e_d) using an
    # auxiliary assignment where:
    #   - recursive block is 0 (prefix all zeros),
    #   - S2_2 is 0,
    #   - and S1_2 is any monic polynomial with the recovered high coefficients
    #     and constant term forced to 0 (so it's still a valid Q instance by decodability).
    q_lo_params_aux = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(
        Q=S1_2_no_const, k=k_q, Hs=Hs[: l - 1], field=field
    )
    tail: List[Number] = [field.zero()] * D
    tail[0] = field.zero()  # S2_2 scalar forced to 0
    for i, v in enumerate(q_lo_params_aux):
        tail[1 + i] = v
    tail[D // 2] = s2_1_shift
    for i, v in enumerate(q_hi_params):
        tail[(D // 2) + 1 + i] = v

    alphas_aux = [field.zero()] * total
    for i in range(D):
        alphas_aux[d + i] = tail[i]
    P_aux = _poly_remainder_poly_from_T(k=k, l=l, alpha=alphas_aux, Hs=Hs, tilde_H_2l=tilde_H_2l, field=field)

    C_aux = _poly_add(
        _poly_shift_xk(_poly_mul(_poly_add(_poly_scale_int(_poly_square(S1_1, field), -1, field), S1_2_no_const, field), H_pow, field), 1, field),
        _poly_mul(_poly_scale_int(_poly_square(S2_1, field), -1, field), Ht_pow, field),
        field,
    )
    E_aux = _poly_sub(P_aux, _poly_scale_int(C_aux, m, field), field)
    e_d1 = _poly_coeff(E_aux, d + 1, field)
    e_d0 = _poly_coeff(E_aux, d, field)

    # Solve s1_2_0 from degree d+1.
    C_d1 = field.mul(field.sub(_poly_coeff(P_R, d + 1, field), e_d1), inv_m)
    known_d1 = field.add(_poly_coeff(x_neg_s1_sq_hpow, d + 1, field), _poly_coeff(tilde_term, d + 1, field))
    prod_d = field.sub(C_d1, known_d1)  # equals [x^d](S1_2*H_pow)
    prod_known = _poly_coeff(_poly_mul(S1_2_no_const, H_pow, field), d, field)
    s1_2_0 = field.sub(prod_d, prod_known)
    S1_2 = _poly_add_const(S1_2_no_const, s1_2_0, field)

    # Solve S2_2 scalar from degree d.
    C_d0 = field.mul(field.sub(_poly_coeff(P_R, d, field), e_d0), inv_m)
    x_s1_2_hpow_d0 = _poly_coeff(_poly_shift_xk(_poly_mul(S1_2, H_pow, field), 1, field), d, field)
    known_d0 = field.add(field.add(_poly_coeff(x_neg_s1_sq_hpow, d, field), x_s1_2_hpow_d0), _poly_coeff(tilde_term, d, field))
    s2_2_scalar = field.sub(C_d0, known_d0)

    # Decode q_lo parameters from the fully recovered S1_2.
    q_lo_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S1_2, k=k_q, Hs=Hs[: l - 1], field=field)

    # Assemble the tail alphas in the exact layout used by `_paper_T` (even case l>=2).
    tail_out: List[Number] = [field.zero()] * D
    tail_out[0] = s2_2_scalar
    for i, v in enumerate(q_lo_params):
        tail_out[1 + i] = v
    tail_out[D // 2] = s2_1_shift
    for i, v in enumerate(q_hi_params):
        tail_out[(D // 2) + 1 + i] = v

    # Build H_{2^{l+1}} and \\tilde H_{2^{l+1}} from the decoded tail, using the k=2 instance.
    T1_tail, T2_tail, Hs_out_tail, tilde_out_tail = _poly_paper_T(
        k=2, l=l, alpha=tail_out, Hs=Hs, tilde_H_2l=tilde_H_2l, field=field
    )
    H_next = _poly_trim(Hs_out_tail[l + 1], field)
    H_tilde_next = _poly_trim(tilde_out_tail, field)

    # Isolate the prefix remainder polynomial by subtracting the tail-only remainder,
    # then compensate by adding the zero-parameter recursive remainder (boundary correction).
    tail_only = [field.zero()] * total
    for i in range(D):
        tail_only[d + i] = tail_out[i]
    P_tail = _poly_remainder_poly_from_T(k=k, l=l, alpha=tail_only, Hs=Hs, tilde_H_2l=tilde_H_2l, field=field)

    prefix: List[Number] = []
    P_prefix = _poly_sub(P_R, P_tail, field)
    if m > 1:
        P_inner0 = _poly_remainder_poly_from_T(
            k=m, l=l + 1, alpha=[field.zero()] * d, Hs=list(Hs) + [H_next], tilde_H_2l=H_tilde_next, field=field
        )
        P_prefix = _poly_add(P_prefix, P_inner0, field)

        inner_alpha, Hs_out, tilde_out = _decode_R_k(
            k=m, l=l + 1, P_R=P_prefix, Hs=list(Hs) + [H_next], tilde_H_2l=H_tilde_next, field=field
        )
        if len(inner_alpha) != d:
            raise ValueError("internal: prefix length mismatch in even-k decoder")
        prefix = inner_alpha
        Hs_out_final = Hs_out
        tilde_out_final = tilde_out
    else:
        Hs_out_final = list(Hs) + [H_next]
        tilde_out_final = H_tilde_next

    alpha_out = prefix + tail_out
    if len(alpha_out) != total:
        raise ValueError("internal: decoded alpha count mismatch in even-k decoder")
    return alpha_out, Hs_out_final, tilde_out_final


def _hatR1_combined_coeff_at_degree(
    *,
    k: int,
    H: Poly,
    S1_1: Poly,
    H_tilde: Poly,
    S2_1: Poly,
    deg: int,
    field: Field,
) -> Number:
    """
    Coefficient helper for the odd-k branch of `R_{k,2^l}` decoding.

    Matches `tools/impl/splittable_decode.py:_hatR1_combined_coeff_at_degree` in
    coefficient-list arithmetic:

      \\hat R^{(1)}_1 = sum_{i=3}^{k-1} binom(k-1,i) H^{k-i} S1_1^i
                       - (k-1) sum_{i=2}^{k-1} binom(k-1,i) H^{k-i-1} S1_1^{i+1}
      \\hat R^{(2)}_1 = same with (H_tilde,S2_1)

    Returns coeff( x*\\hat R^{(1)}_1 + \\hat R^{(2)}_1, deg ).

    We truncate to i<=4, which suffices for the boundary degrees used by the
    proof/decoder (higher i cannot reach those degrees by degree reasons).
    """

    if k < 3 or (k % 2) == 0:
        raise ValueError("_hatR1 helper requires odd k>=3")
    if deg < 0:
        return field.zero()

    H = _poly_trim(H, field)
    S1_1 = _poly_trim(S1_1, field)
    H_tilde = _poly_trim(H_tilde, field)
    S2_1 = _poly_trim(S2_1, field)

    i_max = min(4, k - 1)

    hat1: Poly = [field.zero()]
    for i in range(3, i_max + 1):
        term = _poly_mul(_poly_pow(H, k - i, field), _poly_pow(S1_1, i, field), field)
        hat1 = _poly_add(hat1, _poly_scale_int(term, math.comb(k - 1, i), field), field)
    for i in range(2, i_max + 1):
        if k - i - 1 < 0:
            continue
        term = _poly_mul(_poly_pow(H, k - i - 1, field), _poly_pow(S1_1, i + 1, field), field)
        hat1 = _poly_sub(hat1, _poly_scale_int(term, (k - 1) * math.comb(k - 1, i), field), field)

    hat2: Poly = [field.zero()]
    for i in range(3, i_max + 1):
        term = _poly_mul(_poly_pow(H_tilde, k - i, field), _poly_pow(S2_1, i, field), field)
        hat2 = _poly_add(hat2, _poly_scale_int(term, math.comb(k - 1, i), field), field)
    for i in range(2, i_max + 1):
        if k - i - 1 < 0:
            continue
        term = _poly_mul(_poly_pow(H_tilde, k - i - 1, field), _poly_pow(S2_1, i + 1, field), field)
        hat2 = _poly_sub(hat2, _poly_scale_int(term, (k - 1) * math.comb(k - 1, i), field), field)

    combined = _poly_add(_poly_shift_xk(hat1, 1, field), hat2, field)
    return _poly_coeff(combined, deg, field)


def _decode_R_odd_k(
    *,
    k: int,
    l: int,
    P_R: Poly,
    Hs: List[Poly],
    tilde_H_2l: Poly,
    field: Field,
) -> Tuple[List[Number], List[Poly], Poly]:
    """
    Odd-k branch of `_decode_R_k` (paper Algorithm `alg:decode-Rk2l` / Lemma `lem:Rk2l`).

    Structure:
      - `l == 2` (shared-product base, Algorithm `alg:constr-Tk2l-base`, odd
        branch): the four tail scalars u,v,w,z are recovered from the four
        descending affine pivots of `P_R` at degrees d-1..d-4 (d = 4(k-1)),
        whose slopes are -k(k-1), -(k-1), m, m -- the pivot table in the
        shared-base part of the proof of `lem:Rk2l`.
      - `l >= 3`: the tail block is recovered by the stage-1/stage-2 window
        peeling of the proof of `lem:Rk2l` (`lem:peel-monic-factor`,
        `lem:monic-from-power` with m=2, `lem:scalar-shift-square`).
      - In both cases the remaining head+mid parameters are then extracted by
        descending affine pivots of the frozen-tail remainder map
        (`_decode_by_descending_pivots`); this realizes the Multiplicativity /
        Additivity certificate steps of `alg:decode-Rk2l` numerically.
    """

    if k < 3 or (k % 2) == 0:
        raise ValueError("decode_R_odd_k expects odd k>=3")
    if l < 2:
        raise ValueError("odd-k remainder decoding requires l>=2")
    if len(Hs) <= l:
        raise ValueError("Hs must include H_{2^l} at index l")

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("odd-k remainder decoding requires char(F) != 2")
    inv2 = field.inv(two)

    three = field.coerce(3)
    if field.is_zero(three):
        raise NotImplementedError("odd-k remainder decoding currently requires char(F) != 3")
    inv3 = field.inv(three)

    D = 1 << l
    total = (k - 1) * D
    k_half = (k - 1) // 2
    m = field.coerce(k_half)
    if field.is_zero(m):
        raise NotImplementedError("odd-k remainder decoding requires (k-1)/2 invertible in the field")
    inv_m = field.inv(m)

    P_R = _poly_trim(P_R, field)
    H = _poly_trim(Hs[l], field)
    H_tilde = _poly_trim(tilde_H_2l, field)
    H_half = _poly_trim(Hs[l - 1], field)
    H_quarter = _poly_trim(Hs[l - 2], field)

    if l == 2:
        # Shared-product odd base.  Check the admissibility precondition
        # tilde_H4 - H4 scalar, then run the four tail pivots.
        rho = _poly_trim(_poly_sub(H_tilde, H, field), field)
        if _poly_degree(rho) > 0:
            raise ValueError("the shared odd l==2 base requires tilde_H4 - H4 to be a scalar")

        d = total
        # Tail layout (alpha[total-4:total]): [z, w, v, u] with
        #   u = alpha_{4k-5} (S1_1 shift), v = alpha_{4k-6} (S1_2 shift),
        #   w = alpha_{4k-7} (S1_3),       z = alpha_{4k-8} (tilde_H8 shift).
        expected_slopes = {1: -k * (k - 1), 2: -(k - 1), 3: k_half, 4: k_half}

        def _tail_remainder(vals: List[Number]) -> Poly:
            al = [field.zero()] * total
            for i, v in enumerate(vals):
                al[total - 4 + i] = v
            return _poly_remainder_poly_from_T(k=k, l=2, alpha=al, Hs=Hs, tilde_H_2l=H_tilde, field=field)

        tail_vals: List[Number] = [field.zero()] * 4
        for j in (1, 2, 3, 4):
            row = d - j
            base = _tail_remainder(tail_vals)
            probe_vals = list(tail_vals)
            probe_vals[4 - j] = field.add(probe_vals[4 - j], field.one())
            probe = _tail_remainder(probe_vals)
            slope = field.sub(_poly_coeff(probe, row, field), _poly_coeff(base, row, field))
            if field.is_zero(slope):
                raise ValueError("l==2 odd base: zero pivot slope (field not admissible?)")
            if slope != field.coerce(expected_slopes[j]):
                raise ValueError("l==2 odd base: pivot slope does not match the lem:Rk2l table")
            tail_vals[4 - j] = field.div(
                field.sub(_poly_coeff(P_R, row, field), _poly_coeff(base, row, field)), slope
            )
        tail_out: List[Number] = list(tail_vals)
    else:
        # Stage 1: recover S1_1 (monic degree D/2).
        c1 = field.mul(field.mul(field.coerce(k), field.coerce(k - 1)), inv2)  # k(k-1)/2
        if field.is_zero(c1):
            raise NotImplementedError("odd-k remainder decoding requires k(k-1)/2 invertible in the field")
        inv_c1 = field.inv(c1)

        H_pow = _poly_pow(H, k - 2, field)
        Ht_pow = _poly_pow(H_tilde, k - 2, field)

        known_R2_top = _poly_mul(_poly_mul(_poly_square(H_half, field), Ht_pow, field), [field.neg(c1)], field)

        prod1: Poly = [field.zero()] * ((k - 1) * D + 1)  # degrees 0..(k-1)D
        cubic_top = field.mul(field.coerce(k * (k - 1) * (k - 2)), inv3)  # k(k-1)(k-2)/3
        for d in range((k - 1) * D, (k - 2) * D + (D // 2) - 1, -1):
            pr_deg = d + 1
            rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_R2_top, pr_deg, field))
            if d == (k - 2) * D + (D // 2):
                # Boundary correction: stage-2 contributes -m at this top degree and
                # the x-shifted cubic term contributes -cubic_top.
                rhs = field.add(rhs, field.add(field.coerce(k_half), cubic_top))
            prod1[d] = field.mul(field.neg(rhs), inv_c1)

        U1_high = _recover_monic_factor_high_coeffs_from_product(
            product=prod1,
            known_factor=H_pow,
            factor_deg=D,
            min_deg=D // 2,
            field=field,
        )
        U1_poly: Poly = [field.zero()] * (D + 1)
        for deg_i, coeff_i in U1_high.items():
            U1_poly[deg_i] = field.coerce(coeff_i)
        U1_poly[D] = field.one()
        S1_1 = _monic_sqrt_from_high_square_coeffs(_poly_trim(U1_poly, field), root_deg=D // 2, field=field)

        Q_hi = _poly_sub(S1_1, H_half, field)
        q_hi_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=Q_hi, k=l - 1, Hs=Hs[: l - 1], field=field)

        # Precompute K1 (depends only on H and S1_1).
        K1 = _poly_mul(
            _poly_sub(H, _poly_scale_int(S1_1, k - 1, field), field),
            _poly_pow(_poly_add(H, S1_1, field), k - 3, field),
            field,
        )
        degK1 = _poly_degree(K1)
        if degK1 != (k - 2) * D:
            raise ValueError("internal: unexpected deg(K1) in odd-k decoder")

        # Stage 1.5: recover the scalar shift in S2_1 = H_half + s.
        deg_shift = (k - 2) * D + (D // 2)
        stage1_x = _poly_shift_xk(
            _poly_mul(_poly_mul(_poly_square(S1_1, field), H_pow, field), [field.neg(c1)], field),
            1,
            field,
        )
        cubic_coeff = field.neg(cubic_top)
        cubic_x = _poly_shift_xk(
            _poly_mul(_poly_mul(_poly_pow(H, k - 3, field), _poly_pow(S1_1, 3, field), field), [cubic_coeff], field),
            1,
            field,
        )

        # Stage-2 contribution at deg_shift uses only the top 2 coefficients of G1 and K1.
        # Leading G1 coefficient is -1; next is -2*a where a = [x^{D/4-1}]S1_2 and
        # S1_2's top-two coefficients are known from H_quarter and monicity.
        D4 = D // 4
        a_s1_2 = field.add(_poly_coeff(H_quarter, D4 - 1, field), field.one())
        g1k1_deg_shift_minus1 = field.sub(field.neg(_poly_coeff(K1, degK1 - 1, field)), _field_mul_int(field, a_s1_2, 2))
        stage2_at_deg_shift = field.mul(m, field.sub(g1k1_deg_shift_minus1, field.one()))

        # Also subtract the tilde-side cubic top coefficient at this degree: cubic_coeff.
        coeff_stage1_tilde_boundary = field.sub(_poly_coeff(P_R, deg_shift, field), _poly_coeff(stage1_x, deg_shift, field))
        coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, _poly_coeff(cubic_x, deg_shift, field))
        coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, cubic_coeff)
        coeff_stage1_tilde_boundary = field.sub(coeff_stage1_tilde_boundary, stage2_at_deg_shift)

        s2_1_shift = _scalar_shift_from_square_boundary(
            coeff_P_at_boundary=coeff_stage1_tilde_boundary,
            H=H_half,
            M=Ht_pow,
            lam=field.neg(c1),
            field=field,
        )
        S2_1 = _poly_add_const(H_half, s2_1_shift, field)

        # Stage 2: recover U=(S1_2)^2 - S1_3 and the scalar shift in S2_2 = H_quarter + t.
        K2 = _poly_mul(
            _poly_sub(H_tilde, _poly_scale_int(S2_1, k - 1, field), field),
            _poly_pow(_poly_add(H_tilde, S2_1, field), k - 3, field),
            field,
        )
        degK2 = _poly_degree(K2)
        if degK2 != (k - 2) * D:
            raise ValueError("internal: unexpected deg(K2) in odd-k decoder")

        stage1_tilde = _poly_mul(_poly_mul(_poly_square(S2_1, field), Ht_pow, field), [field.neg(c1)], field)
        cubic_tilde = _poly_mul(
            _poly_mul(_poly_pow(H_tilde, k - 3, field), _poly_pow(S2_1, 3, field), field),
            [cubic_coeff],
            field,
        )
        known_stage12 = _poly_add(_poly_add(stage1_x, stage1_tilde, field), _poly_add(cubic_x, cubic_tilde, field), field)

        # High part of G2 is independent of t and equals -H_quarter^2 in degrees > D/4.
        Hq2 = _poly_square(H_quarter, field)
        g2_high: Poly = [field.zero()] * ((D // 2) + 1)
        for i in range(D4 + 1, (D // 2) + 1):
            g2_high[i] = field.neg(_poly_coeff(Hq2, i, field))
        g2_high_term = _poly_mul(g2_high, K2, field)

        prod2: Poly = [field.zero()] * ((k - 2) * D + (D // 2) + 1)
        for d in range((k - 2) * D + (D // 2), (k - 2) * D + D4 - 1, -1):
            pr_deg = d + 1
            rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_stage12, pr_deg, field))
            rhs = field.mul(rhs, inv_m)
            rhs = field.sub(rhs, _poly_coeff(g2_high_term, pr_deg, field))
            prod2[d] = field.neg(rhs)

        U_high = _recover_monic_factor_high_coeffs_from_product(
            product=prod2,
            known_factor=K1,
            factor_deg=D // 2,
            min_deg=D4,
            field=field,
        )
        U_poly: Poly = [field.zero()] * ((D // 2) + 1)
        for deg_i, coeff_i in U_high.items():
            U_poly[deg_i] = field.coerce(coeff_i)
        U_poly[D // 2] = field.one()
        S1_2 = _monic_sqrt_from_high_square_coeffs(_poly_trim(U_poly, field), root_deg=D4, field=field)

        Q_mid = _poly_sub(S1_2, H_quarter, field)
        if l == 2:
            # In the special base construction at l==2 (Alg. `alg:constr-Tk2l-base`, odd branch),
            # S1_2 is fixed to x and carries no Q_{2^{l-2}-1} parameter block.
            Q_mid = _poly_trim(Q_mid, field)
            if _poly_degree(Q_mid) > 0 or _poly_coeff(Q_mid, 0, field) != field.zero():
                raise ValueError("l==2 odd-k decoder expected S1_2 == x (no mid Q-block)")
            q_mid_params = []
        else:
            q_mid_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=Q_mid, k=l - 2, Hs=Hs[: l - 2], field=field)

        # Recover t := s2_2 shift at the boundary degree (k-2)D + D/4.
        deg_t = (k - 2) * D + D4
        stage2_coeff = field.sub(_poly_coeff(P_R, deg_t, field), _poly_coeff(known_stage12, deg_t, field))
        stage2_coeff = field.mul(stage2_coeff, inv_m)

        # Compute the x*G1*K1 contribution at this degree using U_high's degree-(D4-1) coefficient.
        S1_2_sq = _poly_square(S1_2, field)
        u_d4m1 = field.sub(_poly_coeff(S1_2_sq, D4 - 1, field), field.one())
        uk1_coeff = field.zero()
        # prod_deg = (k-2)D + (D4-1) uses only U degrees >= D4-1.
        for j in range(0, (D // 2) - (D4 - 1) + 1):
            udeg = (D4 - 1) + j
            if udeg > (D // 2):
                break
            if udeg == D4 - 1:
                ucoef = u_d4m1
            else:
                ucoef = field.coerce(U_high.get(udeg, field.zero()))
            uk1_coeff = field.add(uk1_coeff, field.mul(ucoef, _poly_coeff(K1, degK1 - j, field)))
        x_g1k1_at_deg_t = field.neg(uk1_coeff)  # G1=-U, x-shift

        # Isolate g2k2 coefficient at this degree and solve t from [x^{D4}]G2 = -Hq2[D4] - 2t.
        g2k2_coeff = field.sub(stage2_coeff, x_g1k1_at_deg_t)
        g2_known_high = field.zero()
        for j in range(1, (D // 2) - D4 + 1):
            gdeg = D4 + j
            gcoef = field.neg(_poly_coeff(Hq2, gdeg, field))
            g2_known_high = field.add(g2_known_high, field.mul(gcoef, _poly_coeff(K2, degK2 - j, field)))
        g2_d4_coeff = field.sub(g2k2_coeff, g2_known_high)
        s2_2_shift = field.mul(field.neg(field.add(g2_d4_coeff, _poly_coeff(Hq2, D4, field))), inv2)
        S2_2 = _poly_add_const(H_quarter, s2_2_shift, field)

        # Recover U down to degree 1 (clean window) and then solve U0 on the contaminated boundary.
        G2_no_const = _poly_scale_int(_poly_square(S2_2, field), -1, field)
        g2k2_no_const = _poly_mul(G2_no_const, K2, field)

        prod2_low: Poly = [field.zero()] * ((k - 2) * D + (D // 2) + 1)
        # Clean stage-2 window: recover U down to degree 1 (inclusive), i.e. d down to (k-2)D+1.
        for d in range((k - 2) * D + (D // 2), (k - 2) * D, -1):
            pr_deg = d + 1
            rhs = field.sub(_poly_coeff(P_R, pr_deg, field), _poly_coeff(known_stage12, pr_deg, field))
            rhs = field.mul(rhs, inv_m)
            rhs = field.sub(rhs, _poly_coeff(g2k2_no_const, pr_deg, field))
            prod2_low[d] = field.neg(rhs)

        U_low = _recover_monic_factor_high_coeffs_from_product(
            product=prod2_low,
            known_factor=K1,
            factor_deg=D // 2,
            min_deg=1,
            field=field,
        )

        degB = (k - 2) * D + 1
        if (k_half % 2) == 0:
            inner_lead = field.neg(field.mul(field.coerce(k_half), inv2))
        else:
            inner_lead = field.neg(field.mul(field.coerce(k_half * (k_half - 1)), inv2))

        rhsB = field.sub(_poly_coeff(P_R, degB, field), _poly_coeff(stage1_x, degB, field))
        rhsB = field.sub(rhsB, _poly_coeff(stage1_tilde, degB, field))
        rhsB = field.sub(rhsB, _hatR1_combined_coeff_at_degree(k=k, H=H, S1_1=S1_1, H_tilde=H_tilde, S2_1=S2_1, deg=degB, field=field))
        rhsB = field.sub(rhsB, inner_lead)
        rhsB = field.mul(rhsB, inv_m)
        rhsB = field.sub(rhsB, _poly_coeff(g2k2_no_const, degB, field))

        # rhsB == (G1*K1)[(k-2)D] = -(U*K1)[degK1]; solve U0.
        known_sum = field.zero()
        for j in range(1, (D // 2) + 1):
            uj = field.coerce(U_low.get(j, field.zero()))
            if field.is_zero(uj):
                continue
            known_sum = field.add(known_sum, field.mul(uj, _poly_coeff(K1, degK1 - j, field)))
        U0 = field.sub(field.neg(rhsB), known_sum)

        # Build S1_3 = S1_2^2 - U (degree < D/4, monic degree D/4-1).
        S1_3: Poly = [field.zero()] * D4
        S1_3[D4 - 1] = field.one()
        for i in range(1, D4 - 1):
            ui = field.coerce(U_low.get(i, field.zero()))
            S1_3[i] = field.sub(_poly_coeff(S1_2_sq, i, field), ui)
        S1_3[0] = field.sub(_poly_coeff(S1_2_sq, 0, field), U0)
        S1_3 = _poly_trim(S1_3, field)

        if l == 2:
            # In the l==2 base construction, S1_3 is fixed to 0 and has no parameters.
            if _poly_degree(S1_3) > 0 or _poly_coeff(S1_3, 0, field) != field.zero():
                raise ValueError("l==2 odd-k decoder expected S1_3 == 0 (no low Q-block)")
            q_low_params = []
        else:
            q_low_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S1_3, k=l - 2, Hs=Hs[: l - 2], field=field)

        # Recover s2_3 from degree (k-2)D (clean of inner recursion and head).
        degC = (k - 2) * D
        rhsC = field.sub(_poly_coeff(P_R, degC, field), _poly_coeff(stage1_x, degC, field))
        rhsC = field.sub(rhsC, _poly_coeff(stage1_tilde, degC, field))
        rhsC = field.sub(rhsC, _hatR1_combined_coeff_at_degree(k=k, H=H, S1_1=S1_1, H_tilde=H_tilde, S2_1=S2_1, deg=degC, field=field))
        rhsC = field.mul(rhsC, inv_m)

        # Subtract x*G1*K1 and the known -S2_2^2*K2 part to isolate the constant s2_3.
        U_full: Poly = [field.zero()] * ((D // 2) + 1)
        for deg_i, coeff_i in U_low.items():
            U_full[deg_i] = field.coerce(coeff_i)
        U_full[0] = U0
        U_full[D // 2] = field.one()
        x_g1k1_at_degC = _poly_coeff(_poly_shift_xk(_poly_mul(_poly_scale_int(U_full, -1, field), K1, field), 1, field), degC, field)
        rhsC = field.sub(rhsC, x_g1k1_at_degC)
        rhsC = field.sub(rhsC, _poly_coeff(g2k2_no_const, degC, field))

        # rhsC is affine in the unknown scalar s2_3 (tail[0]), but can include a fixed
        # contribution from the inner recursion / head gadget that is independent of s2_3.
        #
        # Compute and subtract that fixed part by evaluating the same expression on a
        # synthetic instance where head/mid are zero and s2_3 is set to 0, while all
        # other already-recovered tail parameters are kept.
        alpha_synth: List[Number] = [field.zero()] * total
        tail_synth: List[Number] = [field.zero()] * D
        # tail layout: [s2_3] + q_low + [s2_2_shift] + q_mid + [s2_1_shift] + q_hi
        tail_synth[0] = field.zero()
        for i, v in enumerate(q_low_params):
            tail_synth[1 + i] = v
        tail_synth[D // 4] = s2_2_shift
        for i, v in enumerate(q_mid_params):
            tail_synth[(D // 4) + 1 + i] = v
        tail_synth[D // 2] = s2_1_shift
        for i, v in enumerate(q_hi_params):
            tail_synth[(D // 2) + 1 + i] = v
        tail_start = D + ((k - 3) * D)
        for i, v in enumerate(tail_synth):
            alpha_synth[tail_start + i] = v
        P_R_synth = _poly_remainder_poly_from_T(k=k, l=l, alpha=alpha_synth, Hs=Hs, tilde_H_2l=H_tilde, field=field)

        rhsC_synth = field.sub(_poly_coeff(P_R_synth, degC, field), _poly_coeff(stage1_x, degC, field))
        rhsC_synth = field.sub(rhsC_synth, _poly_coeff(stage1_tilde, degC, field))
        rhsC_synth = field.sub(
            rhsC_synth,
            _hatR1_combined_coeff_at_degree(k=k, H=H, S1_1=S1_1, H_tilde=H_tilde, S2_1=S2_1, deg=degC, field=field),
        )
        rhsC_synth = field.mul(rhsC_synth, inv_m)
        rhsC_synth = field.sub(rhsC_synth, x_g1k1_at_degC)
        rhsC_synth = field.sub(rhsC_synth, _poly_coeff(g2k2_no_const, degC, field))

        s2_3 = field.sub(rhsC, rhsC_synth)

        # Assemble tail alpha layout (exactly as `_poly_paper_T`, odd case l>=3).
        tail_out: List[Number] = [field.zero()] * D
        tail_out[0] = s2_3
        for i, v in enumerate(q_low_params):
            tail_out[1 + i] = v
        tail_out[D // 4] = s2_2_shift
        for i, v in enumerate(q_mid_params):
            tail_out[(D // 4) + 1 + i] = v
        tail_out[D // 2] = s2_1_shift
        for i, v in enumerate(q_hi_params):
            tail_out[(D // 2) + 1 + i] = v

    # ---- Head + mid parameters via descending pivots of the frozen-tail map. ----
    rest_len = total - D

    def _rest_remainder(rest: List[Number]) -> Poly:
        al = list(rest) + list(tail_out)
        return _poly_remainder_poly_from_T(k=k, l=l, alpha=al, Hs=Hs, tilde_H_2l=H_tilde, field=field)

    rest = _decode_by_descending_pivots(
        target=P_R, encode_fn=_rest_remainder, nparams=rest_len, field=field, what=f"R_odd(k={k},l={l})"
    )

    alphas_out = list(rest) + list(tail_out)
    if len(alphas_out) != total:
        raise ValueError("internal: odd-k alpha length mismatch")
    _T1, _T2, Hs_out, tilde_out = _poly_paper_T(
        k=k, l=l, alpha=alphas_out, Hs=Hs, tilde_H_2l=H_tilde, field=field
    )
    return alphas_out, Hs_out, tilde_out


def _decode_A_fill_coeffs(
    *,
    P: Poly,
    l: int,
    Hs: List[Poly],
    H_S: Poly,
    field: Field,
) -> Tuple[List[Number], List[Number], Poly, Poly]:
    """
    Decode the fill construction `A_{2^l}` in the *Q-context* input shape.

    Currently implemented: `l == 2` (i.e. `A_4`), mirroring `tools/impl/a_decode.py:decode_A4_for_Q`.

    Input shape for `l=2`:
      S1_4 = H_S + (x^3 + e2*x^2 + e1*x + e0)
      S2_4 = H_S + s2

    Returns:
      (alpha_block, beta_block, S1_4, S2_4)
    with alpha_block = [α0..α5] and beta_block = [β0..β4] matching `_paper_A_fill`.
    """

    P = _poly_trim(P, field)
    if _poly_coeff(P, _poly_degree(P), field) != field.one():
        raise ValueError("A_fill decoder expects monic P")
    if l != 2:
        raise NotImplementedError("A_fill coefficient decoder is currently implemented for l=2 only")

    H_S = _poly_trim(H_S, field)
    if _poly_coeff(H_S, _poly_degree(H_S), field) != field.one():
        raise ValueError("H_S must be monic")

    deg_P = _poly_degree(P)
    # For l=2, A_4 output has degree n+7.
    n = _poly_degree(H_S)
    if deg_P != n + 7:
        raise ValueError(f"A_4 decoder expects deg(P)=n+7, got deg(P)={deg_P} and n={n}")
    if _poly_degree(H_S) != n:
        raise ValueError(f"H_S degree mismatch: expected {n}, got {_poly_degree(H_S)}")

    if len(Hs) != 3:
        raise ValueError("A_4 decoder expects Hs=[x,H2,H4]")
    x, H2, H4 = Hs
    H2 = _poly_trim(H2, field)
    H4 = _poly_trim(H4, field)
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("A_4 decoder expects monic degree-2 H2")
    if _poly_degree(H4) != 4 or _poly_coeff(H4, 4, field) != field.one():
        raise ValueError("A_4 decoder expects monic degree-4 H4")

    h2_1 = _poly_coeff(H2, 1, field)
    h2_0 = _poly_coeff(H2, 0, field)

    # Step 1: recover beta0,beta1,beta2,beta3 from top-degree structure.
    HS2 = _poly_mul(H4, H_S, field)
    s2_n4 = _poly_coeff(HS2, n + 4, field)  # = 1
    if s2_n4 != field.one():
        raise ValueError("internal error: expected [x^{n+4}]H4*H_S == 1")
    s2_n3 = _poly_coeff(HS2, n + 3, field)
    s2_n2 = _poly_coeff(HS2, n + 2, field)
    s2_n1 = _poly_coeff(HS2, n + 1, field)
    s2_n0 = _poly_coeff(HS2, n + 0, field)

    # A1_{n+5} = h2_1 + s2_{n+3}
    A1_n5 = field.add(h2_1, s2_n3)
    beta0 = field.sub(field.sub(_poly_coeff(P, n + 6, field), A1_n5), field.one())

    # A2_{n+5} matches as well.
    A2_n5 = A1_n5
    A1_n4 = field.sub(_poly_coeff(P, n + 5, field), field.add(field.mul(beta0, A1_n5), A2_n5))

    # A1_{n+4} = (h2_0+beta1) + h2_1*s2_{n+3} + s2_{n+2}
    beta1 = field.sub(A1_n4, field.add(h2_0, field.add(field.mul(h2_1, s2_n3), s2_n2)))

    # A1_{n+3} = s2_{n+1} + h2_1*s2_{n+2} + (h2_0+beta1)*s2_{n+3}
    A1_n3 = field.add(s2_n1, field.add(field.mul(h2_1, s2_n2), field.mul(field.add(h2_0, beta1), s2_n3)))

    # From P_{n+4} = A1_{n+3} + beta0*A1_{n+4} + A2_{n+4}.
    A2_n4 = field.sub(_poly_coeff(P, n + 4, field), field.add(A1_n3, field.mul(beta0, A1_n4)))

    # A2_{n+4} = (h2_0+beta2) + h2_1*s2_{n+3} + s2_{n+2}
    beta2 = field.sub(A2_n4, field.add(h2_0, field.add(field.mul(h2_1, s2_n3), s2_n2)))

    # A2_{n+3} = s2_{n+1} + h2_1*s2_{n+2} + (h2_0+beta2)*s2_{n+3}
    A2_n3 = field.add(s2_n1, field.add(field.mul(h2_1, s2_n2), field.mul(field.add(h2_0, beta2), s2_n3)))

    # From P_{n+3} = A1_{n+2} + beta0*A1_{n+3} + A2_{n+3}.
    A1_n2 = field.sub(_poly_coeff(P, n + 3, field), field.add(field.mul(beta0, A1_n3), A2_n3))

    # beta3 first appears via S1_2[n] = HS2[n] + beta3 (since S1_4 is monic tail of degree 3).
    beta3 = field.sub(A1_n2, field.add(s2_n0, field.add(field.mul(h2_1, s2_n1), field.mul(field.add(h2_0, beta1), s2_n2))))

    # Step 2: solve remaining low-tail variables without 0/1/2 probing.
    #
    # We use a deterministic affine peeling solver over GF(p) (symbolic in the
    # unknown tail parameters, numeric in the known-power coefficients).
    if field.modulus is None:
        raise NotImplementedError("A_4 decoder currently requires Field(modulus=p) for a prime p")

    try:
        import sympy as sp  # local import: used only in decoders
    except ModuleNotFoundError as e:
        raise NotImplementedError("A_4 low-tail solver requires sympy to be installed") from e

    p = int(field.modulus)
    if p == 2:
        raise NotImplementedError("A_4 decoder assumes char(F) != 2")
    if p <= 1 or not sp.ntheory.primetest.isprime(p):
        raise ValueError(f"A_4 decoder requires a prime modulus; got p={p}")
    if n > 64:
        raise NotImplementedError(
            "A_4 low-tail solver is SymPy-based and only intended for small heads; "
            f"got deg(H_S)={n}. Implement a truncated coefficient solver to support large n."
        )
    x_sym = sp.Symbol("x")

    def _sym_expr_from_poly(poly: Poly) -> sp.Expr:
        poly = _poly_trim(poly, field)
        expr = sp.Integer(0)
        for i, c in enumerate(poly):
            ci = int(field.coerce(c)) % p
            if ci:
                expr += sp.Integer(ci) * (x_sym**i)
        return expr

    H2_sym = _sym_expr_from_poly(H2)
    H4_sym = _sym_expr_from_poly(H4)
    HS_sym = _sym_expr_from_poly(H_S)
    P_target_sym = _sym_expr_from_poly(P)

    beta4_s, s2_s = sp.symbols("beta4 s2")
    e0_s, e1_s, e2_s = sp.symbols("e0 e1 e2")
    alpha0_s, alpha1_s, alpha2_s = sp.symbols("alpha0 alpha1 alpha2")
    q0_s, q1_s, q2_s = sp.symbols("q0 q1 q2")

    beta0_i = int(beta0) % p
    beta1_i = int(beta1) % p
    beta2_i = int(beta2) % p
    beta3_i = int(beta3) % p

    S1_4_sym = HS_sym + (x_sym**3 + e2_s * x_sym**2 + e1_s * x_sym + e0_s)
    S2_4_sym = HS_sym + s2_s
    Q3_sym = x_sym**3 + q2_s * x_sym**2 + q1_s * x_sym + q0_s

    S1_2_sym = (H4_sym + beta3_i) * S1_4_sym + Q3_sym
    S2_2_sym = (H4_sym + beta4_s) * S2_4_sym + alpha2_s

    A1_sym = (H2_sym + beta1_i) * S1_2_sym + alpha1_s
    A2_sym = (H2_sym + beta2_i) * S2_2_sym + alpha0_s
    P_sym = (x_sym + beta0_i) * A1_sym + A2_sym

    # These unknowns can only influence degrees <= n+2.
    max_deg = n + 2
    unknown_syms = [
        beta4_s,
        s2_s,
        e0_s,
        e1_s,
        e2_s,
        alpha0_s,
        alpha1_s,
        alpha2_s,
        q0_s,
        q1_s,
        q2_s,
    ]

    def _mod_expr(expr: sp.Expr) -> sp.Expr:
        expr = sp.expand(expr)
        if expr == 0:
            return sp.Integer(0)
        return sp.Poly(expr, *unknown_syms, domain=sp.ZZ).trunc(p).as_expr()

    # Extract coefficient equations in x and reduce them mod p as polynomials in the unknowns.
    diff_x = sp.Poly(sp.expand(P_sym - P_target_sym), x_sym)
    eqs = []
    for d in range(max_deg + 1):
        eq = _mod_expr(diff_x.nth(d))
        if eq != 0:
            eqs.append(eq)

    def _is_affine_in(eq: sp.Expr, var: sp.Symbol) -> Tuple[bool, sp.Expr, sp.Expr]:
        poly_var = sp.Poly(eq, var)
        deg = poly_var.degree()
        if deg is sp.S.NegativeInfinity:
            return True, sp.Integer(0), sp.Integer(0)
        if deg > 1:
            return False, sp.Integer(0), sp.Integer(0)
        a = _mod_expr(poly_var.nth(1))
        b = _mod_expr(poly_var.nth(0))
        return True, a, b

    def _inv_mod_int(a: sp.Expr) -> int:
        if a.free_symbols:
            raise ValueError("expected constant slope")
        ai = int(a) % p
        if ai == 0:
            raise ValueError("zero slope in affine equation")
        return pow(ai, -1, p)

    sol: Dict[sp.Symbol, sp.Expr] = {}
    remaining = list(unknown_syms)
    eqs_work = list(eqs)
    for _ in range(len(remaining) + 5):
        if not remaining:
            break
        progress = False
        for var in list(remaining):
            for eq in eqs_work:
                eq = _mod_expr(eq.subs(sol))
                if var not in eq.free_symbols:
                    continue
                ok, a, b = _is_affine_in(eq, var)
                if not ok:
                    continue
                if any((u in a.free_symbols) for u in remaining if u != var):
                    continue
                inv_a = _inv_mod_int(a)
                if b.free_symbols:
                    continue
                val = (-int(b) * inv_a) % p
                sol[var] = sp.Integer(val)
                remaining.remove(var)
                eqs_work = [_mod_expr(e.subs(var, sol[var])) for e in eqs_work]
                eqs_work = [e for e in eqs_work if e != 0]
                progress = True
                break
            if progress:
                break
        if not progress:
            raise RuntimeError(f"A_4 low-tail affine peeling got stuck; remaining={len(remaining)}")
    if remaining or eqs_work:
        raise RuntimeError("A_4 low-tail affine peeling did not fully solve the system")

    def _to_field(sym: sp.Symbol) -> Number:
        return field.coerce(int(sol[sym]) % p)

    beta4 = _to_field(beta4_s)
    s2 = _to_field(s2_s)
    e0 = _to_field(e0_s)
    e1 = _to_field(e1_s)
    e2 = _to_field(e2_s)
    alpha0 = _to_field(alpha0_s)
    alpha1 = _to_field(alpha1_s)
    alpha2 = _to_field(alpha2_s)
    q0 = _to_field(q0_s)
    q1 = _to_field(q1_s)
    q2 = _to_field(q2_s)

    # Sanity: reconstructed parameters reproduce P exactly.
    S1_4_chk = _poly_add(H_S, [e0, e1, e2, field.one()], field)
    S2_4_chk = _poly_add_const(H_S, s2, field)
    Q3_chk = [q0, q1, q2, field.one()]
    S1_2_chk = _poly_add(_poly_mul(_poly_add_const(H4, beta3, field), S1_4_chk, field), Q3_chk, field)
    S2_2_chk = _poly_add_const(_poly_mul(_poly_add_const(H4, beta4, field), S2_4_chk, field), alpha2, field)
    A1_chk = _poly_add_const(_poly_mul(_poly_add_const(H2, beta1, field), S1_2_chk, field), alpha1, field)
    A2_chk = _poly_add_const(_poly_mul(_poly_add_const(H2, beta2, field), S2_2_chk, field), alpha0, field)
    P_chk = _poly_add(_poly_mul(_poly_add_const(x, beta0, field), A1_chk, field), A2_chk, field)
    if _poly_trim(P_chk, field) != _poly_trim(P, field):
        raise RuntimeError("A_4 low-tail solver produced parameters that do not reproduce P")

    # Decode Q3 coefficients to (alpha3,alpha4,alpha5) given H2.
    Q3_poly = [q0, q1, q2, field.one()]
    alpha3, alpha4, alpha5 = _decode_Q3_coeffs_to_alpha_given_H2(Q3_poly, H2, field)

    alpha = [alpha0, alpha1, alpha2, alpha3, alpha4, alpha5]
    beta = [beta0, beta1, beta2, beta3, beta4]

    S1_4 = _poly_add(H_S, [e0, e1, e2, field.one()], field)
    S2_4 = _poly_add_const(H_S, s2, field)
    return alpha, beta, S1_4, S2_4


def _decode_A_fill_coeffs_via_closure(
    *,
    P: Poly,
    l: int,
    Hs: List[Poly],
    input_algo: "object",
    field: Field,
) -> Tuple[List[Number], List[Number], Poly, Poly]:
    """
    Decode the fill construction `A_{2^l}` using the paper’s constructive
    compatibility-closure approach (no probing).

    This is the algorithmic content of `sections/constructions.tex`:
      - Lemma `lem:fill-correctness`
      - Algorithm `alg:decode-fill`

    Args:
      P:
        The monic output polynomial of `A_{2^l}`.
      l:
        Level >= 1.
      Hs:
        Known powers `[x, H2, ..., H_{2^l}]`.
      input_algo:
        A compatibility “certificate as an algorithm” for the input pair
        `(S^{(1)}_{2^l}, S^{(2)}_{2^l})`. Must provide `n`, `window`,
        `derive_phi`, `coeff_p1`, `coeff_p2` (see `tools/compat_algos.py`).

    Returns:
      (alpha_block, beta_block, S1_2l, S2_2l)
    matching `_poly_paper_A_fill`.
    """

    # Local imports to avoid cycles: compat_algos imports this module.
    from tools.compat_algos import (  # type: ignore[import-not-found]
        AddCompat,
        AuxHeadCompat,
        MonicPlusConstantsCompat,
        MonicPolyTimesXPlusConstCompat,
        MulCompat,
        recover_x_plus_beta_mix,
    )
    from tools.compat_closure import MultiplicativeSplitSpec, split_phi_product_on_disjoint_shifted_windows
    from tools.compat_primitives import AuxAddLeftCompat

    if l < 1:
        raise ValueError("fill decoder requires l>=1")
    if len(Hs) <= l:
        raise ValueError("Hs must include H_{2^l} at index l")

    P = _poly_trim(P, field)
    if _poly_degree(P) < 0 or _poly_coeff(P, _poly_degree(P), field) != field.one():
        raise ValueError("A_fill decoder expects monic P")

    if not hasattr(input_algo, "n") or not hasattr(input_algo, "window"):
        raise TypeError("input_algo must satisfy the CompatAlgo interface (see tools/compat_algos.py)")

    n = int(getattr(input_algo, "n"))
    m2 = (1 << (l + 1)) - 1
    if _poly_degree(P) != n + m2:
        raise ValueError(f"A_fill decoder expects deg(P)=n+{m2}, got deg(P)={_poly_degree(P)} and n={n}")

    x = _poly_trim(Hs[0], field)
    H2 = _poly_trim(Hs[1], field)
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("expected monic degree-2 H2")

    # ---- Base case l=1: decode A_2. ----
    if l == 1:
        # Build compatibility for (A1_2,A2_2) on G' as in the proof:
        #   product pair: (S1,S2) * (H2+β1, H2+β2)
        #   + monic-plus-constants (x^{n+2}+α1, x^{n+2}+α0), equal-degree add
        h2_pair = AuxHeadCompat(H=H2)
        prod_pair = MulCompat(f1=input_algo, f2=h2_pair)
        const_pair = MonicPlusConstantsCompat(n=n + 2)
        a_pair = AddCompat(p1=prod_pair, p2=const_pair, equal_degree=True)

        beta0, _Phi, A1, A2 = recover_x_plus_beta_mix(P=P, algo=a_pair, field=field)

        # Extract β1 and β2 from [x^n]A1 and [x^n]A2.
        # This uses only the top coefficients of (S1,S2), which are derivable
        # from the auxiliary data alone because input_algo.window ⊆ rng(n-2).
        seed_phi: Dict[int, Number] = {n + 1: field.one()}
        s1_n_minus_1 = field.coerce(input_algo.coeff_p1(n - 1, seed_phi, field))
        s1_n_minus_2 = field.coerce(input_algo.coeff_p1(n - 2, seed_phi, field))
        s2_n_minus_1 = field.coerce(input_algo.coeff_p2(n - 1, seed_phi, field))
        s2_n_minus_2 = field.coerce(input_algo.coeff_p2(n - 2, seed_phi, field))

        h2_0 = _poly_coeff(H2, 0, field)
        h2_1 = _poly_coeff(H2, 1, field)
        # coeff(H2*S, n) = S[n-2] + h2_1*S[n-1] + h2_0*S[n]
        coeff_h2_s1_at_n = field.add(s1_n_minus_2, field.add(field.mul(h2_1, s1_n_minus_1), h2_0))
        coeff_h2_s2_at_n = field.add(s2_n_minus_2, field.add(field.mul(h2_1, s2_n_minus_1), h2_0))

        beta1 = field.sub(_poly_coeff(A1, n, field), coeff_h2_s1_at_n)
        beta2 = field.sub(_poly_coeff(A2, n, field), coeff_h2_s2_at_n)

        H2_plus_beta1 = _poly_add_const(H2, beta1, field)
        H2_plus_beta2 = _poly_add_const(H2, beta2, field)
        S1, rem1 = _poly_divmod_monic(A1, H2_plus_beta1, field)
        S2, rem2 = _poly_divmod_monic(A2, H2_plus_beta2, field)
        rem1 = _poly_trim(rem1, field)
        rem2 = _poly_trim(rem2, field)
        if _poly_degree(rem1) > 0 or _poly_degree(rem2) > 0:
            raise ValueError("expected constant remainders α1 and α0 in A_2 decoding")
        alpha1 = _poly_coeff(rem1, 0, field)
        alpha0 = _poly_coeff(rem2, 0, field)
        return [alpha0, alpha1], [beta0, beta1, beta2], _poly_trim(S1, field), _poly_trim(S2, field)

    # ---- Recursive step: first decode the outer A_{2^{l-1}} call to get the intermediate pair. ----
    m = 1 << l
    low_deg = m - 1

    if l == 2:
        H4 = _poly_trim(Hs[2], field)
        if _poly_degree(H4) != 4 or _poly_coeff(H4, 4, field) != field.one():
            raise ValueError("expected monic degree-4 H4")
        factor_pair = AuxHeadCompat(H=H4)
    else:
        Hm = _poly_trim(Hs[l], field)
        if _poly_degree(Hm) != m or _poly_coeff(Hm, m, field) != field.one():
            raise ValueError("expected monic H_{2^l}")
        half = 1 << (l - 1)
        # (H_{2^l}+Q_low, H_{2^l}+β_{2^l}) is aux-add-left with deg(Q_low)=2^{l-1}-1.
        factor_pair = AuxAddLeftCompat(H=Hm, q_deg=half - 1)

    prod_pair = MulCompat(f1=input_algo, f2=factor_pair)
    low_pair = MonicPolyTimesXPlusConstCompat(n=low_deg)
    intermediate_algo = AddCompat(p1=prod_pair, p2=low_pair, equal_degree=False)

    alpha_low, beta_low, S1_prev, S2_prev = _decode_A_fill_coeffs_via_closure(
        P=P, l=l - 1, Hs=Hs[:l], input_algo=intermediate_algo, field=field
    )

    # ---- Invert the l-th fill step, using the derived intermediate pair. ----
    if l == 2:
        H4 = _poly_trim(Hs[2], field)
        # Extract β3,β4 from [x^n]S1_prev and [x^n]S2_prev using the top coeffs of the true inputs.
        seed_phi = {n + 1: field.one()}
        # Need S[n-i] for i=1..4 (top 4 coeffs) to compute coeff(H4*S, n).
        s1_top = [field.one()]
        s2_top = [field.one()]
        for i in range(1, 5):
            s1_top.append(field.coerce(input_algo.coeff_p1(n - i, seed_phi, field)))
            s2_top.append(field.coerce(input_algo.coeff_p2(n - i, seed_phi, field)))

        def _coeff_H4_times_S_at_n(S_top: List[Number]) -> Number:
            # S_top[i] = S[n-i], i=0..4
            acc = field.zero()
            for i in range(0, 5):
                acc = field.add(acc, field.mul(_poly_coeff(H4, i, field), S_top[i]))
            return acc

        coeff_h4_s1_at_n = _coeff_H4_times_S_at_n(s1_top)
        coeff_h4_s2_at_n = _coeff_H4_times_S_at_n(s2_top)

        beta3 = field.sub(_poly_coeff(S1_prev, n, field), coeff_h4_s1_at_n)
        beta4 = field.sub(_poly_coeff(S2_prev, n, field), coeff_h4_s2_at_n)

        H4_plus_beta3 = _poly_add_const(H4, beta3, field)
        H4_plus_beta4 = _poly_add_const(H4, beta4, field)

        S1_4, Q3 = _poly_divmod_monic(S1_prev, H4_plus_beta3, field)
        S2_4, rem2 = _poly_divmod_monic(S2_prev, H4_plus_beta4, field)
        Q3 = _poly_trim(Q3, field)
        rem2 = _poly_trim(rem2, field)
        if _poly_degree(Q3) != 3 or _poly_coeff(Q3, 3, field) != field.one():
            raise ValueError("expected monic degree-3 remainder Q3 in A_4 decoding")
        if _poly_degree(rem2) > 0:
            raise ValueError("expected constant remainder α2 in A_4 decoding")
        alpha2 = _poly_coeff(rem2, 0, field)

        alpha3, alpha4, alpha5 = _decode_Q3_coeffs_to_alpha_given_H2(Q3, H2, field)
        alpha = [alpha_low[0], alpha_low[1], alpha2, alpha3, alpha4, alpha5]
        beta = [beta_low[0], beta_low[1], beta_low[2], beta3, beta4]
        return alpha, beta, _poly_trim(S1_4, field), _poly_trim(S2_4, field)

    # l >= 3: recover the aux-add-left factor (H_{2^l}+Q_low, H_{2^l}+β_{2^l}) from Φ_prod on W.
    Hm = _poly_trim(Hs[l], field)
    half = 1 << (l - 1)
    G1 = set(getattr(input_algo, "window"))
    G2 = set(range(0, half))
    spec = MultiplicativeSplitSpec(n1=n, n2=m, G1=G1, G2=G2)

    Phi = _poly_add(_poly_shift_xk(S1_prev, 1, field), S2_prev, field)
    W = {m + g for g in G1} | {n + g for g in G2}
    phi_prod_on_W: Dict[int, Number] = {}
    for d in W:
        c = _poly_coeff(Phi, d, field)
        if d == m:
            c = field.sub(c, field.one())
        phi_prod_on_W[d] = c

    factor_algo = AuxAddLeftCompat(H=Hm, q_deg=half - 1)
    _phiS_on_G1, phiF_on_G2 = split_phi_product_on_disjoint_shifted_windows(
        spec=spec,
        phi_prod_on_W=phi_prod_on_W,
        field=field,
        derive_phi1=lambda d, phi1_known: getattr(input_algo, "derive_phi")(d, phi1_known, field),
        derive_phi2=lambda d, phi2_known: factor_algo.derive_phi(d, phi2_known, field),
        coeff_p1_1=lambda i, phi1_known: getattr(input_algo, "coeff_p1")(i, phi1_known, field),
        coeff_p2_1=lambda i, phi1_known: getattr(input_algo, "coeff_p2")(i, phi1_known, field),
        coeff_p1_2=lambda i, phi2_known: factor_algo.coeff_p1(i, phi2_known, field),
        coeff_p2_2=lambda i, phi2_known: factor_algo.coeff_p2(i, phi2_known, field),
        min_d_prod=0,
    )

    Q_low, beta_2l = factor_algo.decode_Q_b(phi_on_G=phiF_on_G2, field=field)
    H_plus_Q_low = _poly_add(Hm, Q_low, field)
    H_plus_beta = _poly_add_const(Hm, beta_2l, field)

    S1_2l, Q_high = _poly_divmod_monic(S1_prev, H_plus_Q_low, field)
    S2_2l, rem2 = _poly_divmod_monic(S2_prev, H_plus_beta, field)
    Q_high = _poly_trim(Q_high, field)
    rem2 = _poly_trim(rem2, field)
    if _poly_degree(rem2) > 0:
        raise ValueError("expected constant remainder α_{2^l-2} in S2 branch")
    alpha_2l_minus_2 = _poly_coeff(rem2, 0, field)
    if _poly_degree(Q_high) != m - 1 or _poly_coeff(Q_high, m - 1, field) != field.one():
        raise ValueError("expected monic degree-(2^l-1) remainder Q_high")

    # Decode Q_low and Q_high to recover the remaining parameter blocks.
    qlow_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=Q_low, k=l - 1, Hs=Hs[: l - 1], field=field)
    qhigh_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=Q_high, k=l, Hs=Hs[:l], field=field)

    alpha: List[Number] = [field.zero()] * ((1 << (l + 1)) - 2)
    # Lower α-block from recursion: α0..α_{2^l-3}.
    for i, v in enumerate(alpha_low):
        alpha[i] = v
    alpha[m - 2] = alpha_2l_minus_2
    for i, v in enumerate(qhigh_params):
        alpha[(m - 1) + i] = v

    beta: List[Number] = [field.zero()] * (m + 1)
    # Lower β-block from recursion: β0..β_{2^{l-1}}.
    for i, v in enumerate(beta_low):
        beta[i] = v
    # Q_low params are [β_{2^l-1}, ..., β_{2^{l-1}+1}].
    for idx in range((1 << (l - 1)) + 1, m):
        beta[idx] = qlow_params[(m - 1) - idx]
    beta[m] = beta_2l

    return alpha, beta, _poly_trim(S1_2l, field), _poly_trim(S2_2l, field)


def _decode_Q_power_of_2_minus_1_coeffs_to_alpha(
    *,
    Q: Poly,
    k: int,
    Hs: List[Poly],
    field: Field,
) -> List[Number]:
    """
    Decode `Q_{2^k-1}` (Algorithm `alg:constr-known-2n-1`) to its α-parameters.

    Constructive (paper-faithful) decoder following Algorithm `alg:decode-Q-2kminus1`.
    """

    Q = _poly_trim(Q, field)
    if _poly_degree(Q) != (1 << k) - 1 or _poly_coeff(Q, (1 << k) - 1, field) != field.one():
        raise ValueError("Q decoder expects monic degree (2^k-1)")
    if len(Hs) < k:
        raise ValueError("Q decoder expects Hs=[x,H2,...,H_{2^{k-1}}]")

    if PEELED_Q and k >= 3:
        # Q = (H_{2^{k-1}} + gamma) * W + B: divide by the known monic H
        # (quotient = W since deg(gamma*W + B) < deg H), read gamma at the
        # residual's top row (W and B are monic), subtract.
        m = (1 << (k - 1)) - 1
        W, R = _poly_divmod_monic(Q, Hs[k - 1], field)
        if _poly_degree(W) != m or _poly_coeff(W, m, field) != field.one():
            raise ValueError("peeled Q decoder: quotient is not monic of the right degree")
        gamma = field.sub(_poly_coeff(R, m, field), field.one())
        B = _poly_sub(R, _poly_scale_const(W, gamma, field), field)
        return ([gamma]
                + _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=W, k=k - 1, Hs=Hs[: k - 1], field=field)
                + _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=B, k=k - 1, Hs=Hs[: k - 1], field=field))

    x = Hs[0]
    if k == 1:
        # Q_1 = x + α0.
        if _poly_degree(Q) != 1:
            raise ValueError("Q1 must have degree 1")
        return [field.sub(_poly_coeff(Q, 0, field), _poly_coeff(x, 0, field))]
    if k == 2:
        return _decode_Q3_coeffs_to_alpha_given_H2(Q, Hs[1], field)
    if k == 3:
        return _decode_Q7_coeffs_to_alpha_given_H2_H4(Q, Hs[1], Hs[2], field)
    if k < 4:
        raise RuntimeError("unreachable")

    # k >= 4: by Lemma `lem:Q-unitriangular` the coefficient map of `Q_{2^k-1}`
    # is unitriangular from high to low degree in the encoder's own parameter
    # order: coeff_j = alpha_j + f_j(alpha_{j+1}, ..., alpha_{2^k-2}).  Solve by
    # descending back-substitution, re-encoding to evaluate each f_j.
    q = (1 << k) - 1
    alpha = [field.zero()] * q
    for j in range(q - 1, -1, -1):
        cur = _poly_paper_Q_known_powers(k=k, alpha=alpha, Hs=Hs, field=field)
        alpha[j] = field.sub(_poly_coeff(Q, j, field), _poly_coeff(cur, j, field))

    chk = _poly_paper_Q_known_powers(k=k, alpha=alpha, Hs=Hs, field=field)
    if _poly_trim(chk, field) != _poly_trim(Q, field):
        raise ValueError("Q_{2^k-1} decode failed verification (input is not a Q instance for these powers)")
    return alpha


def _invert_fill_step_l_ge_3_q_context(
    *,
    l: int,
    S1_prev: Poly,
    S2_prev: Poly,
    H_S: Poly,
    Hs: List[Poly],
    field: Field,
) -> Tuple[Number, Number, Poly, Poly, Poly, Poly]:
    """
    Invert the *single* l>=3 fill-step that defines the intermediate pair:

      S1_prev = (H_{2^l} + Q_low) * S1 + Q_high
      S2_prev = (H_{2^l} + β_{2^l}) * S2 + α_{2^l-2}

    in the Q-context usage, where:
      - H_{2^l} is known (monic degree 2^l),
      - S1,S2 are monic degree n with the shared head `H_S`:
          S1[d] == H_S[d] and S2[d] == H_S[d] for all d >= 2^l,
      - and we assume n >= 2^(l+1) (so the boundary identities below only touch the known head region).

    Returns:
      (beta_2l, alpha_2l_minus_2, Q_low, Q_high, S1, S2)

    This routine is “paper-faithful”: it uses only coefficient identities + monic division,
    plus separate decoding of the Q-polynomials (handled elsewhere).
    """

    if l < 3:
        raise ValueError("fill-step inversion requires l>=3")
    if len(Hs) <= l:
        raise ValueError("Hs must include H_{2^l} at index l")
    H = _poly_trim(Hs[l], field)
    m = 1 << l
    if _poly_degree(H) != m or _poly_coeff(H, m, field) != field.one():
        raise ValueError("expected monic H_{2^l} of degree 2^l")

    H_S = _poly_trim(H_S, field)
    n = _poly_degree(H_S)
    if _poly_coeff(H_S, n, field) != field.one():
        raise ValueError("H_S must be monic")
    if n < (1 << (l + 1)):
        raise NotImplementedError("fill-step inversion currently assumes deg(H_S) >= 2^(l+1)")

    S1_prev = _poly_trim(S1_prev, field)
    S2_prev = _poly_trim(S2_prev, field)
    if _poly_degree(S1_prev) != n + m or _poly_degree(S2_prev) != n + m:
        raise ValueError("expected intermediate pair degrees n+2^l")
    if _poly_coeff(S1_prev, n + m, field) != field.one() or _poly_coeff(S2_prev, n + m, field) != field.one():
        raise ValueError("expected monic intermediate pair")

    # ---- S2 branch: recover β_{2^l}, then divide to get S2 and α_{2^l-2}. ----
    #
    # In degrees > 0, S2 equals H_S, so coeff(H*S2, n) is computable from H and H_S.
    coeff_HS2_at_n = field.zero()
    for i in range(0, m + 1):
        # H[i] * S2[n-i], and S2[n-i] == H_S[n-i] since n-i >= n-m >= m (by n>=2m).
        coeff_HS2_at_n = field.add(
            coeff_HS2_at_n, field.mul(_poly_coeff(H, i, field), _poly_coeff(H_S, n - i, field))
        )

    beta_2l = field.sub(_poly_coeff(S2_prev, n, field), coeff_HS2_at_n)
    H_plus_beta = _poly_add_const(H, beta_2l, field)
    S2, rem2 = _poly_divmod_monic(S2_prev, H_plus_beta, field)
    rem2 = _poly_trim(rem2, field)
    if _poly_degree(rem2) > 0:
        raise ValueError("expected constant remainder α_{2^l-2} in S2 branch")
    alpha_2l_minus_2 = _poly_coeff(rem2, 0, field)

    # ---- S1 branch: recover Q_low via boundary peeling at degrees n..n+2^{l-1}-2. ----
    half = 1 << (l - 1)

    # Recover U := H + Q_low in degrees 0..half-1. Degrees >= half match H.
    U_coeffs: List[Number] = [field.zero()] * (m + 1)
    for d in range(m + 1):
        U_coeffs[d] = _poly_coeff(H, d, field)
    # Monicity at top.
    U_coeffs[m] = field.one()
    # Q_low is monic of degree half-1, so U[half-1] = H[half-1] + 1.
    U_coeffs[half - 1] = field.add(_poly_coeff(H, half - 1, field), field.one())

    # For u from half-2 down to 0:
    #   Prod1[n+u] = Σ_{j=u..m} U[j]*S1[n+u-j], with S1[n+u-j] known from H_S for all needed indices
    #   (since n>=2m implies n+u-j >= n-m >= m).
    for u in range(half - 2, -1, -1):
        known_sum = field.zero()
        for j in range(u + 1, m + 1):
            known_sum = field.add(
                known_sum, field.mul(U_coeffs[j], _poly_coeff(H_S, (n + u) - j, field))
            )
        U_coeffs[u] = field.sub(_poly_coeff(S1_prev, n + u, field), known_sum)

    Q_low = [field.zero()] * (half)
    for u in range(0, half - 1):
        Q_low[u] = field.sub(U_coeffs[u], _poly_coeff(H, u, field))
    Q_low[half - 1] = field.one()
    Q_low = _poly_trim(Q_low, field)

    # Divide to recover S1 and Q_high remainder.
    U = _poly_trim(U_coeffs, field)
    S1, Q_high = _poly_divmod_monic(S1_prev, U, field)
    Q_high = _poly_trim(Q_high, field)
    if _poly_degree(Q_high) >= m:
        raise ValueError("expected deg(Q_high) < 2^l")

    return beta_2l, alpha_2l_minus_2, Q_low, Q_high, _poly_trim(S1, field), _poly_trim(S2, field)


def _decode_aux_add_left_from_combined(
    *,
    Phi: Poly,
    H: Poly,
    q_deg: int,
    field: Field,
) -> Tuple[Poly, Number]:
    """
    Constructive decoder for Lemma `lem:compatible-aux-add-left`:

      P1 = H + Q   (Q monic deg q_deg < deg(H))
      P2 = H + b   (b scalar)
      Phi = x*P1 + P2

    Given (Phi, H), recover (Q, b).
    """

    Phi = _poly_trim(Phi, field)
    H = _poly_trim(H, field)
    m = _poly_degree(H)
    if q_deg < 0 or q_deg >= m:
        raise ValueError("q_deg must satisfy 0 <= q_deg < deg(H)")
    if _poly_coeff(H, m, field) != field.one():
        raise ValueError("H must be monic")

    # Xi = Phi - (xH + H) = xQ + b.
    xH_plus_H = _poly_add(_poly_shift_xk(H, 1, field), H, field)
    Xi = _poly_sub(Phi, xH_plus_H, field)
    b = _poly_coeff(Xi, 0, field)
    Q: Poly = [field.zero()] * (q_deg + 2)
    # coeff(Xi, i) = coeff(Q, i-1) for 1<=i<=q_deg+1
    for i in range(1, q_deg + 2):
        Q[i - 1] = _poly_coeff(Xi, i, field)
    Q[q_deg + 1] = field.zero()
    # Ensure monic Q degree q_deg.
    if q_deg >= 0:
        Q[q_deg] = field.one()
        Q = _poly_trim(Q[: q_deg + 1], field)
    return Q, b


def _decode_monic_plus_constants_from_combined(*, Phi: Poly, n: int, field: Field) -> Tuple[Number, Number]:
    """
    Constructive decoder for Lemma `lem:compatible-monic-plus-constants`.

      F1 = x^n + u
      F2 = x^n + v
      Phi = x*F1 + F2 = x^{n+1} + x^n + u*x + v

    Given Phi, recover (u,v).
    """

    if n < 2:
        raise ValueError("requires n>=2")
    Phi = _poly_trim(Phi, field)
    v = _poly_coeff(Phi, 0, field)
    u = _poly_coeff(Phi, 1, field)
    return u, v


def _decode_auxhead_deg2_from_combined(*, Phi: Poly, H2: Poly, field: Field) -> Tuple[Number, Number]:
    """
    Constructive decoder for Lemma `lem:compatible-auxhead-deg2`.

      F1 = H2 + b1
      F2 = H2 + b2
      Phi = x*F1 + F2

    Given (Phi,H2), recover (b1,b2).
    """

    Phi = _poly_trim(Phi, field)
    H2 = _poly_trim(H2, field)
    if _poly_degree(H2) != 2 or _poly_coeff(H2, 2, field) != field.one():
        raise ValueError("expected monic degree-2 H2")
    b2 = field.sub(_poly_coeff(Phi, 0, field), _poly_coeff(H2, 0, field))
    b1 = field.sub(field.sub(_poly_coeff(Phi, 1, field), _poly_coeff(H2, 1, field)), _poly_coeff(H2, 0, field))
    return b1, b2

def _decode_P11_coeffs_to_alpha(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode `P_11[α0..α10]` (the k=1 instance of the 8k+3 induction).

    For k=1 the “compatibility” recovery step collapses to a genuine square-gadget
    because the inner splittable pair is `n=3`, where
      (S1_1,S1_2) = (H2, H2+α2).
    """

    coeffs = _poly_trim(coeffs, field)
    if _poly_degree(coeffs) != 11 or _poly_coeff(coeffs, 11, field) != field.one():
        raise ValueError("P11 decoder expects a monic degree-11 polynomial")

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("P11 decoding requires char(F) != 2")

    # Step 1: decode S2=Q5 and a=α5 from the outer square gadget at d=5.
    # The error term contributes degree-5 coefficient -1 (from -x*(S1_1)^2, with S1_1 monic degree 2).
    S2, a = _decode_square_gadget(
        G=coeffs,
        field=field,
        boundary_error_coeff_deg_d=field.neg(field.one()),
    )
    if _poly_degree(S2) != 5:
        raise ValueError("internal error: expected deg(S2)=5 in P11 decoding")

    # Subtract the square gadget to isolate the residual.
    xS2_sq = _poly_shift_xk(_poly_square(S2, field), 1, field)
    S2_plus_a_sq = _poly_square(_poly_add_const(S2, a, field), field)
    P_rem = _poly_sub(coeffs, _poly_add(xS2_sq, S2_plus_a_sq, field), field)

    # Step 2: recover (S1_1, α2) from Ψ = x(S1_1)^2 + (S1_1+α2)^2.
    #
    # For degrees >= 2, the low-degree term (x*α1 + α0) does not contribute, so:
    #   Ψ_{>=2} = -P_rem_{>=2}.
    psi = [field.zero()] * 6  # degree 5 max
    for d in range(2, 6):
        psi[d] = field.neg(_poly_coeff(P_rem, d, field))
    psi[5] = field.one()
    psi = _poly_trim(psi, field)

    S1_1, alpha2 = _decode_square_gadget(G=psi, field=field, boundary_error_coeff_deg_d=field.zero())
    if _poly_degree(S1_1) != 2:
        raise ValueError("internal error: expected deg(S1_1)=2 in P11 decoding")

    # Step 3: recover α0, α1 from P_rem = -Ψ + x*α1 + α0.
    psi_full = _poly_add(_poly_shift_xk(_poly_square(S1_1, field), 1, field), _poly_square(_poly_add_const(S1_1, alpha2, field), field), field)
    resid = _poly_add(P_rem, psi_full, field)
    alpha0 = _poly_coeff(resid, 0, field)
    alpha1 = _poly_coeff(resid, 1, field)

    # Step 4: recover the embedded `n=3` block parameters α3,α4 from S1_1 (=H2).
    # Here H2 = x^2 + α4 x + α3.
    alpha4 = _poly_coeff(S1_1, 1, field)
    alpha3 = _poly_coeff(S1_1, 0, field)

    # Step 5: decode the `Q5` parameter block α6..α10 given H2.
    q_params = _decode_Q5_coeffs_to_alpha_given_H2(S2, S1_1, field)
    if len(q_params) != 5:
        raise ValueError("internal error: expected 5 params from Q5 decoder")

    # Global α layout for n=11 (k=1) per `_paper_splittable_pair`:
    #   α0           : scalar in the final T2
    #   α1           : S3 constant
    #   α2..α4       : P3 block
    #   α5           : square-gadget shift on S2
    #   α6..α10      : Q5 block
    alpha = [field.zero()] * 11
    alpha[0] = alpha0
    alpha[1] = alpha1
    alpha[2] = alpha2
    alpha[3] = alpha3
    alpha[4] = alpha4
    alpha[5] = a
    for i in range(5):
        alpha[6 + i] = q_params[i]
    return alpha


def _decode_P15_coeffs_to_alpha(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode `P_15[α0..α14]` induced by this file’s special-case `n=15` splittable pair.

    Structure (from `_paper_splittable_pair(n=15)`):
      - H2 = x^2 + α7 x + α6
      - H4 = H2^2 - (x+α5)^2 + α4
      - S  = Q_7[α8..α14](x,H2,H4)     (paper `Q_known_powers(k=3)`)
      - T1 = S^2 - (H2+α3)^2 + α1
      - H8 = H4^2 - (H2+α2)^2 + α0
      - P  = (x+1)*T1 + H8

    This decoder is solver-free and uses coefficient algebra + monic square roots.
    Requires char(F) != 2 (and 4 invertible).
    """

    coeffs = _poly_trim(coeffs, field)
    if _poly_degree(coeffs) != 15 or _poly_coeff(coeffs, 15, field) != field.one():
        raise ValueError("P15 decoder expects a monic degree-15 polynomial")

    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("P15 decoding requires char(F) != 2")
    inv2 = field.inv(two)
    four = field.add(two, two)
    if field.is_zero(four):
        raise ValueError("P15 decoding requires 4 invertible in the field")
    inv4 = field.inv(four)

    x = [field.zero(), field.one()]
    x_plus_1 = [field.one(), field.one()]

    # Step 1: recover S^2 coefficients in degrees 7..14 from the clean high window.
    S_sq_high: Poly = [field.zero()] * 15  # degree 14 max
    S_sq_high[14] = field.one()
    for d in range(14, 8, -1):  # d=14..9 gives S^2[d-1]
        S_sq_high[d - 1] = field.sub(_poly_coeff(coeffs, d, field), S_sq_high[d])
    # Degree 8 is still clean (other terms max degree 8 but do not contribute to deg 9+).
    # Degree 7 is obtained from [x^8]P = (S^2[8]+S^2[7]) + [x^8]H4^2, and H4 is monic => [x^8]H4^2 = 1.
    S_sq_high[7] = field.sub(field.sub(_poly_coeff(coeffs, 8, field), field.one()), S_sq_high[8])

    S = _monic_sqrt_from_high_square_coeffs(S_sq_high, root_deg=7, field=field)
    if _poly_degree(S) != 7 or _poly_coeff(S, 7, field) != field.one():
        raise ValueError("internal error: expected monic degree-7 S in P15 decoding")
    S_sq = _poly_square(S, field)

    # Step 2: residual R = P - (x+1)*S^2 = H4^2 - (x+1)(H2+α3)^2 - (H2+α2)^2 + (x+1)α1 + α0.
    R = _poly_sub(coeffs, _poly_mul(S_sq, x_plus_1, field), field)

    # Step 3: recover H4 coefficients from (mostly clean) H4^2 coefficients.
    H4_sq_8 = _poly_coeff(R, 8, field)
    H4_sq_7 = _poly_coeff(R, 7, field)
    H4_sq_6 = _poly_coeff(R, 6, field)
    # Degree 5: subtract the known contribution from -x*(H2+α3)^2, which is -1 at degree 5.
    H4_sq_5 = field.add(_poly_coeff(R, 5, field), field.one())

    if H4_sq_8 != field.one():
        raise ValueError("internal error: expected monic H4^2 at degree 8 in P15 decoding")

    # Let H4 = x^4 + A x^3 + B x^2 + C x + D.
    # Then H4^2 has:
    #   [x^7]=2A, [x^6]=A^2+2B, [x^5]=2AB+2C, [x^4]=B^2+2AC+2D.
    A = field.mul(H4_sq_7, inv2)
    # A = 2*α7 (since H4[3] = 2*α7).
    alpha7 = field.mul(A, inv2)

    A2 = field.mul(A, A)
    B = field.mul(field.sub(H4_sq_6, A2), inv2)
    twoAB = field.add(field.mul(A, B), field.mul(A, B))
    C = field.mul(field.sub(H4_sq_5, twoAB), inv2)

    # Degree 4: R_4 = (H4^2)_4 - ((H2+α3)^2)_3 - 2, and ((H2+α3)^2)_3 = 2*α7 (independent of α3).
    H4_sq_4 = field.add(_poly_coeff(R, 4, field), field.add(_field_mul_int(field, alpha7, 2), field.coerce(2)))
    B2 = field.mul(B, B)
    twoAC = _field_mul_int(field, field.mul(A, C), 2)
    D = field.mul(field.sub(field.sub(H4_sq_4, B2), twoAC), inv2)

    H4 = _poly_trim([D, C, B, A, field.one()], field)
    if _poly_degree(H4) != 4 or _poly_coeff(H4, 4, field) != field.one():
        raise ValueError("internal error: expected monic degree-4 H4 in P15 decoding")

    # Step 4: recover H2 params and α4,α5 from H4 = H2^2 - (x+α5)^2 + α4.
    # Here H2 = x^2 + α7 x + α6.
    alpha6 = field.mul(field.sub(field.add(B, field.one()), field.mul(alpha7, alpha7)), inv2)
    alpha5 = field.sub(field.mul(alpha7, alpha6), field.mul(C, inv2))
    alpha4 = field.sub(D, field.sub(field.mul(alpha6, alpha6), field.mul(alpha5, alpha5)))

    H2 = _poly_trim([alpha6, alpha7, field.one()], field)

    # Step 5: subtract H4^2 and solve the remaining low scalars α0..α3.
    H4_sq_full = _poly_square(H4, field)
    R2 = _poly_sub(R, H4_sq_full, field)

    b = alpha7
    c = alpha6
    # From degree 3:
    #   R2_3 = -((x+1)(H2+α3)^2)_3 - ((H2+α2)^2)_3
    #        = -((H2+α3)^2_3 + (H2+α3)^2_2) - 2b
    # and (H2+α3)^2_2 = b^2 + 2(c+α3).
    s2_sq_2 = field.sub(field.neg(_poly_coeff(R2, 3, field)), _field_mul_int(field, b, 4))
    d3 = field.mul(field.sub(s2_sq_2, field.mul(b, b)), inv2)  # d3 = c + α3
    alpha3 = field.sub(d3, c)

    # From degree 2:
    #   R2_2 = -( (H2+α3)^2_2 + (H2+α3)^2_1 ) - (H2+α2)^2_2
    # where (H2+α3)^2_1 = 2*b*d3 and (H2+α2)^2_2 = b^2 + 2*d2.
    two_b_d3 = _field_mul_int(field, field.mul(b, d3), 2)
    num_d2 = field.sub(
        field.sub(field.neg(_poly_coeff(R2, 2, field)), field.add(s2_sq_2, two_b_d3)),
        field.mul(b, b),
    )
    d2 = field.mul(num_d2, inv2)  # d2 = c + α2
    alpha2 = field.sub(d2, c)

    # Degree 1: R2_1 = -(2*b*d3 + d3^2) - (2*b*d2) + α1.
    alpha1 = field.add(
        _poly_coeff(R2, 1, field),
        field.add(field.add(two_b_d3, field.mul(d3, d3)), _field_mul_int(field, field.mul(b, d2), 2)),
    )

    # Degree 0: R2_0 = -d3^2 - d2^2 + α1 + α0.
    alpha0 = field.sub(
        field.add(_poly_coeff(R2, 0, field), field.add(field.mul(d3, d3), field.mul(d2, d2))),
        alpha1,
    )

    # Step 6: decode the embedded Q7 block α8..α14 from S given (H2,H4).
    q_params = _decode_Q_power_of_2_minus_1_coeffs_to_alpha(Q=S, k=3, Hs=[x, H2, H4], field=field)
    if len(q_params) != 7:
        raise ValueError("internal error: expected 7 params from Q7 decoder")

    alpha: List[Number] = [field.zero()] * 15
    alpha[0] = alpha0
    alpha[1] = alpha1
    alpha[2] = alpha2
    alpha[3] = alpha3
    alpha[4] = alpha4
    alpha[5] = alpha5
    alpha[6] = alpha6
    alpha[7] = alpha7
    for i, v in enumerate(q_params):
        alpha[8 + i] = v

    # Sanity: re-encode.
    chk = _poly_trim(_poly_paper_P_from_params(params=alpha, field=field), field)
    if chk != coeffs:
        raise RuntimeError("P15 decoder produced parameters that do not reproduce the input polynomial")
    return alpha


def _decode_params_by_peeling(
    *,
    target: Poly,
    param_count: int,
    encode_fn,
    field: Field,
    match_degrees: Optional[List[int]] = None,
) -> List[Number]:
    """
    Deterministically recover `param_count` parameters by probing an encoder `encode_fn`
    and peeling affine dependencies on selected coefficient degrees.

    This is a pragmatic fallback used by some higher-level decoders when a dedicated
    closed-form constructive inverse is not yet implemented.
    """

    if param_count < 0:
        raise ValueError("param_count must be >= 0")
    if field.modulus is None:
        raise NotImplementedError("peeling decoder requires a prime field modulus")

    target = _poly_trim(target, field)
    deg = _poly_degree(target)
    if deg < 0:
        raise ValueError("target polynomial must be nonzero")

    if match_degrees is None:
        degrees = list(range(deg, -1, -1))
    else:
        degrees = sorted({int(d) for d in match_degrees if d >= 0}, reverse=True)
        if not degrees:
            raise ValueError("match_degrees must be non-empty")

    one = field.one()
    two = field.add(one, one)

    params: List[Number] = [field.zero()] * param_count
    remaining = set(range(param_count))

    def encode(p: List[Number]) -> Poly:
        return _poly_trim(encode_fn(list(p)), field)

    def coeff(poly: Poly, d: int) -> Number:
        return _poly_coeff(poly, d, field)

    # Safety: guard against infinite loops.
    for _ in range(param_count + 5):
        if not remaining:
            break
        cur = encode(params)

        # Find highest mismatching degree in the requested window.
        rd: Optional[int] = None
        for d in degrees:
            if coeff(cur, d) != coeff(target, d):
                rd = d
                break
        if rd is None:
            break

        found: Optional[Tuple[int, int, Number, Number]] = None  # (deg, idx, c0, slope)

        # Scan downward through the degree window.
        start_idx = degrees.index(rd)
        for deg_idx in range(start_idx, len(degrees)):
            d = degrees[deg_idx]
            c0 = coeff(cur, d)
            tgt = coeff(target, d)
            if c0 == tgt:
                continue

            for idx in sorted(remaining, reverse=True):
                # Affine check at this degree by varying only α[idx].
                trial1 = list(params)
                trial1[idx] = one
                c1 = coeff(encode(trial1), d)
                slope = field.sub(c1, c0)
                if field.is_zero(slope):
                    continue
                trial2 = list(params)
                trial2[idx] = two
                c2 = coeff(encode(trial2), d)
                if field.sub(c2, c1) != slope:
                    continue

                # Witness stability (helps avoid picking an affine-but-coupled coefficient).
                other = [j for j in sorted(remaining, reverse=True) if j != idx]
                witness = other[:1]
                ok = True
                for w in witness:
                    basew = list(params)
                    basew[w] = one
                    c0w = coeff(encode(basew), d)
                    basew1 = list(basew)
                    basew1[idx] = one
                    c1w = coeff(encode(basew1), d)
                    if field.sub(c1w, c0w) != slope:
                        ok = False
                        break
                    basew2 = list(basew)
                    basew2[idx] = two
                    c2w = coeff(encode(basew2), d)
                    if field.sub(c2w, c1w) != slope:
                        ok = False
                        break
                if not ok:
                    continue

                found = (d, idx, c0, slope)
                break
            if found is not None:
                break

        if found is None:
            raise NotImplementedError("peeling got stuck (need a constructive decoder for this encoder)")

        d, idx, c0, slope = found
        params[idx] = field.div(field.sub(coeff(target, d), c0), slope)
        remaining.remove(idx)

    # Validate (on requested degrees).
    chk = encode(params)
    for d in degrees:
        if coeff(chk, d) != coeff(target, d):
            raise RuntimeError("peeling decoder produced params that do not match the requested coefficient window")
    return params


def _decode_params_by_backtracking_peeling(
    *,
    target: Poly,
    param_count: int,
    encode_fn,
    field: Field,
    match_degrees: Optional[List[int]] = None,
    lookahead_degrees: int = 12,
    witness_count: int = 2,
    max_nodes: int = 20000,
) -> List[Number]:
    """
    Backtracking version of `_decode_params_by_peeling`.

    This is intended as a pragmatic fallback when greedy peeling gets stuck due
    to picking an affine-but-coupled variable early on.
    """

    if param_count < 0:
        raise ValueError("param_count must be >= 0")
    if field.modulus is None:
        raise NotImplementedError("backtracking peeling decoder requires a prime field modulus")
    two = field.add(field.one(), field.one())
    if field.is_zero(two):
        raise NotImplementedError("backtracking peeling expects char(F) != 2")

    target = _poly_trim(target, field)
    deg = _poly_degree(target)
    if deg < 0:
        raise ValueError("target polynomial must be nonzero")

    if match_degrees is None:
        degrees = list(range(deg, -1, -1))
    else:
        degrees = sorted({int(d) for d in match_degrees if d >= 0}, reverse=True)
        if not degrees:
            raise ValueError("match_degrees must be non-empty")

    one = field.one()

    from functools import lru_cache

    def _key(params: List[Number]) -> Tuple[int, ...]:
        # Use int() to get a stable key for cached encodes over GF(p).
        return tuple(int(field.coerce(v)) for v in params)

    @lru_cache(maxsize=65536)
    def _encode_cached(key: Tuple[int, ...]) -> Poly:
        params = [field.coerce(v) for v in key]
        return _poly_trim(encode_fn(params), field)

    def encode(params: List[Number]) -> Poly:
        return _encode_cached(_key(params))

    def coeff(poly: Poly, d: int) -> Number:
        return _poly_coeff(poly, d, field)

    def _highest_residual_degree(cur: Poly) -> Optional[int]:
        for d in degrees:
            if coeff(cur, d) != coeff(target, d):
                return d
        return None

    def _higher_degrees_match(cur: Poly, *, above: int) -> bool:
        for d in degrees:
            if d <= above:
                break
            if coeff(cur, d) != coeff(target, d):
                return False
        return True

    nodes = 0

    def _search(params: List[Number], remaining: Set[int]) -> Optional[List[Number]]:
        nonlocal nodes
        nodes += 1
        if nodes > max_nodes:
            return None

        cur = encode(params)
        rd = _highest_residual_degree(cur)
        if rd is None:
            # All degrees match on the requested window.
            return params

        # Try a small lookahead window below rd, to find a peelable coefficient.
        dmin = max(0, rd - max(0, lookahead_degrees))
        candidate_degrees = [d for d in degrees if dmin <= d <= rd]

        for d in candidate_degrees:
            c0 = coeff(cur, d)
            tgt = coeff(target, d)
            if c0 == tgt:
                continue

            # Prefer higher parameter indices.
            for idx in sorted(remaining, reverse=True):
                trial1 = list(params)
                trial1[idx] = one
                c1 = coeff(encode(trial1), d)
                slope = field.sub(c1, c0)
                if field.is_zero(slope):
                    continue

                trial2 = list(params)
                trial2[idx] = two
                c2 = coeff(encode(trial2), d)
                if field.sub(c2, c1) != slope:
                    continue

                # Witness-stability: toggle a few other remaining vars.
                ok = True
                witnesses = [j for j in sorted(remaining, reverse=True) if j != idx][:witness_count]
                for w in witnesses:
                    basew = list(params)
                    basew[w] = one
                    c0w = coeff(encode(basew), d)
                    basew1 = list(basew)
                    basew1[idx] = one
                    c1w = coeff(encode(basew1), d)
                    if field.sub(c1w, c0w) != slope:
                        ok = False
                        break
                    basew2 = list(basew)
                    basew2[idx] = two
                    c2w = coeff(encode(basew2), d)
                    if field.sub(c2w, c1w) != slope:
                        ok = False
                        break
                if not ok:
                    continue

                val = field.div(field.sub(tgt, c0), slope)
                next_params = list(params)
                next_params[idx] = val
                next_cur = encode(next_params)
                if not _higher_degrees_match(next_cur, above=d):
                    continue

                nxt_remaining = set(remaining)
                nxt_remaining.remove(idx)
                solved = _search(next_params, nxt_remaining)
                if solved is not None:
                    return solved

        return None

    params0: List[Number] = [field.zero()] * param_count
    remaining0: Set[int] = set(range(param_count))
    out = _search(params0, remaining0)
    if out is None:
        raise RuntimeError("backtracking peeling failed to recover parameters")

    # Validate on full requested degrees.
    chk = encode(out)
    for d in degrees:
        if coeff(chk, d) != coeff(target, d):
            raise RuntimeError("backtracking peeling produced params that do not match the requested coefficient window")
    return out


def _decode_P_coeffs_to_paper_params(coeffs: Poly, field: Field) -> List[Number]:
    """
    Decode a monic polynomial's coefficients into the paper parameters α0..α_{n-1}
    for the family P_n[α] implemented by `compile_paper_params_chain`.

    Implemented here:
      - the bases n = 1,3,5,7 and the specials n = 11, 15;
      - all even n by the paper's even-lift: P_n = α0 + x * P_{n-1}(α1..);
      - the main splittable family n ≡ 1 (mod 4) (lem:4k+1-splittable +
        alg:decode-Rk2l via `_decode_R_k`).

    The remaining odd families (8k+3, 8k+7, and the specials 27/31) are
    implemented in `tools/polychain.py` on top of the primitives in this file.
    """

    coeffs = _poly_trim(coeffs, field)
    if len(coeffs) <= 1:
        raise ValueError("polynomial must have positive degree for paper decoding")
    if coeffs[-1] != field.one():
        raise ValueError("paper decoding requires a monic polynomial (leading coefficient 1)")

    n = len(coeffs) - 1
    if n == 1:
        return [coeffs[0]]

    if (n % 2) == 0:
        # P_n = α0 + x * P_{n-1}(α1..)
        alpha0 = coeffs[0]
        rest = _decode_P_coeffs_to_paper_params(coeffs[1:], field)
        return [alpha0] + rest

    if n == 3:
        return _decode_P3_coeffs_to_alpha(coeffs, field)
    if n == 5:
        return _decode_P5_coeffs_to_alpha(coeffs, field)
    if n == 7:
        return _decode_P7_coeffs_to_alpha(coeffs, field)
    if n == 11:
        return _decode_P11_coeffs_to_alpha(coeffs, field)
    if n == 15:
        return _decode_P15_coeffs_to_alpha(coeffs, field)

    # Main splittable family: n = 4k+1, k>=2.
    if (n % 4) == 1 and n >= 9:
        return _decode_P_4k_plus_1_coeffs_to_alpha(coeffs, field)

    return _decode_P_coeffs_to_paper_params_peeling_fallback(coeffs, field)


def _require_monic(coeffs: List[Number], field: Field) -> None:
    if len(coeffs) <= 1:
        return
    if coeffs[-1] != field.one():
        raise ValueError(
            "only monic polynomials are supported (leading coefficient must be 1); "
            "for P(x)=a0+a1*x+...+a_{n-1}*x^{n-1}+x^n, pass coefficients [a0..a_{n-1}, 1]"
        )


def _compile_paper_monic(coeffs: List[Number], field: Field) -> PolynomialChain:
    """
    Compile a monic polynomial using paper-style constructions.

    Supported degrees:
    - 0 (constant)
    - 1
    - 3 (Q_3 base construction, 2 multiplications + preprocessing)
    - 5 (Q_5 base construction, 3 multiplications + preprocessing)
    - 7 (4 multiplications + preprocessing; paper variant needs 2 invertible, GF(2) uses a
      different base construction with Frobenius-inverse preprocessing)
    - even degrees via the lift P(x)=a0 + x*Q(x) where Q is monic of degree n-1.
    """

    coeffs = _trim_trailing_zeros(coeffs, field)
    if not coeffs:
        raise ValueError("coeffs must be non-empty")

    _require_monic(coeffs, field)
    n = len(coeffs) - 1

    if n == 0:
        return PolynomialChain(
            wire_names=["1", "x"],
            gates=[],
            output=AffineForm.const_only(field.coerce(coeffs[0])),
            field=field,
        )

    wire_names: List[str] = ["1", "x"]
    gates: List[MulGate] = []

    def mul(left: AffineForm, right: AffineForm) -> int:
        out_wire = len(wire_names)
        gates.append(MulGate(left=left, right=right, out_wire=out_wire))
        wire_names.append(f"y{out_wire - 2}")
        return out_wire

    x_form = AffineForm.wire(1)

    if n == 1:
        out = x_form.add_const(field.coerce(coeffs[0]), field)
        return PolynomialChain(wire_names=wire_names, gates=gates, output=out, field=field)

    # Even-degree lift: P(x)=a0 + x*Q(x) where Q is monic of degree n-1.
    if n % 2 == 0:
        # Q(x) has coefficients [a1, a2, ..., a_{n-1}, 1].
        q_chain = _compile_paper_monic([field.coerce(c) for c in coeffs[1:]], field)
        # Splice in q_chain's gates, then add one multiply by x.
        wire_names = q_chain.wire_names
        gates = list(q_chain.gates)

        y = len(wire_names)
        gates.append(MulGate(left=q_chain.output, right=AffineForm.wire(1), out_wire=y))
        wire_names.append(f"y{y - 2}")

        out = AffineForm.wire(y).add_const(field.coerce(coeffs[0]), field)
        return PolynomialChain(wire_names=wire_names, gates=gates, output=out, field=field)

    if n == 3:
        # Paper base construction Q_3:
        #   out = (x + α2) * (x^2 + α1) + α0
        # with preprocessing
        #   α2 = a2
        #   α1 = a1
        #   α0 = a0 - a1*a2
        a0, a1, a2 = (field.coerce(coeffs[0]), field.coerce(coeffs[1]), field.coerce(coeffs[2]))
        alpha2 = a2
        alpha1 = a1
        alpha0 = field.sub(a0, field.mul(a1, a2))

        x2 = mul(x_form, x_form)
        t = mul(x_form.add_const(alpha2, field), AffineForm.wire(x2).add_const(alpha1, field))
        out = AffineForm.wire(t).add_const(alpha0, field)
        return PolynomialChain(wire_names=wire_names, gates=gates, output=out, field=field)

    if n == 5:
        # Paper base construction Q_5 (see Lean file `lean/FastPolyhash/Constructions/Q5Chain.lean`).
        # Preprocessing (decode):
        #   α2 = a4 - 1
        #   α4 = a2 - α2*a3 + α2^2
        #   α3 = a3 - α2 - α4
        #   α1 = a1 - α4*a3 + α4^2
        #   α0 = a0 - α2*a1 + α2^2*α4
        a0 = field.coerce(coeffs[0])
        a1 = field.coerce(coeffs[1])
        a2 = field.coerce(coeffs[2])
        a3 = field.coerce(coeffs[3])
        a4 = field.coerce(coeffs[4])

        alpha2 = field.sub(a4, field.one())
        alpha2_sq = field.mul(alpha2, alpha2)
        alpha4 = field.add(field.sub(a2, field.mul(alpha2, a3)), alpha2_sq)
        alpha3 = field.sub(field.sub(a3, alpha2), alpha4)
        alpha4_sq = field.mul(alpha4, alpha4)
        alpha1 = field.add(field.sub(a1, field.mul(alpha4, a3)), alpha4_sq)
        alpha0 = field.add(field.sub(a0, field.mul(alpha2, a1)), field.mul(alpha2_sq, alpha4))

        x2 = mul(x_form, x_form)
        z = mul(
            AffineForm.wire(x2).add_const(alpha4, field),
            AffineForm.sum_wires([1, x2], const=alpha3),
        )
        w = mul(
            x_form.add_const(alpha2, field),
            AffineForm.wire(z).add_const(alpha1, field),
        )
        out = AffineForm.wire(w).add_const(alpha0, field)
        return PolynomialChain(wire_names=wire_names, gates=gates, output=out, field=field)

    if n == 7:
        a0, a1, a2, a3, a4, a5, a6 = (field.coerce(c) for c in coeffs[:7])

        two = field.add(field.one(), field.one())
        if field.is_zero(two):
            # Characteristic-2 septic base (fast-polyhash.tex):
            #   y = (x + u6)x
            #   z = (x + u5)(y + u4)
            #   w = (z + u3)z
            #   v = (x + u1)(y + w + u2)
            #   P = v + u0
            #
            # Preprocessing (coeffs -> u) uses square roots (inverse Frobenius).
            c0, c1, c2, c3, c4, c5, c6 = a0, a1, a2, a3, a4, a5, a6

            u1 = c6
            s = field.sqrt(c5)  # s = u5 + u6
            u3 = field.add(c4, field.mul(u1, c5))

            # D = (u4 + u5*u6)^2
            D = field.add(c3, field.mul(u1, u3))
            D = field.add(D, field.mul(u3, s))
            D = field.add(D, field.one())
            E = field.sqrt(D)  # E = u4 + u5*u6

            u1u3 = field.mul(u1, u3)
            u1u3s = field.mul(u1u3, s)
            u1D = field.mul(u1, D)
            u3E = field.mul(u3, E)
            u6 = field.add(c2, u1u3s)
            u6 = field.add(u6, u1D)
            u6 = field.add(u6, u1)
            u6 = field.add(u6, u3E)

            u5 = field.add(s, u6)
            q = field.mul(u5, u6)  # q = u5*u6
            u4 = field.add(E, q)

            u4_sq = field.mul(u4, u4)
            u5_sq = field.mul(u5, u5)
            u4sq_u5sq = field.mul(u4_sq, u5_sq)

            u3u4 = field.mul(u3, u4)
            u3u4u5 = field.mul(u3u4, u5)
            u1u3u4 = field.mul(u1u3, u4)
            u1u3q = field.mul(u1u3, q)
            u1u6 = field.mul(u1, u6)

            u2 = field.add(c1, u1u3u4)
            u2 = field.add(u2, u1u3q)
            u2 = field.add(u2, u1u6)
            u2 = field.add(u2, u3u4u5)
            u2 = field.add(u2, u4sq_u5sq)

            u1u2 = field.mul(u1, u2)
            u1u3u4u5 = field.mul(u1u3u4, u5)
            u1u4sq_u5sq = field.mul(u1, u4sq_u5sq)
            u0 = field.add(c0, u1u2)
            u0 = field.add(u0, u1u3u4u5)
            u0 = field.add(u0, u1u4sq_u5sq)

            y = mul(x_form.add_const(u6, field), x_form)
            z = mul(x_form.add_const(u5, field), AffineForm.wire(y).add_const(u4, field))
            w = mul(AffineForm.wire(z).add_const(u3, field), AffineForm.wire(z))
            v = mul(
                x_form.add_const(u1, field),
                AffineForm.wire(y).add(AffineForm.wire(w), field).add_const(u2, field),
            )
            out = AffineForm.wire(v).add_const(u0, field)
            return PolynomialChain(wire_names=wire_names, gates=gates, output=out, field=field)

        # Paper-style base construction for a monic septic (degree 7) in 4 multiplications.
        # Preprocessing uses division by 2 (so requires char != 2).
        half = field.inv(two)

        s1 = field.mul(a6, half)  # s1 = a6 / 2
        s1_sq = field.mul(s1, s1)
        s2 = field.mul(field.sub(field.sub(a5, s1_sq), field.one()), half)  # (a5 - s1^2 - 1)/2

        v4 = field.sub(a4, field.one())
        s1s2 = field.mul(s1, s2)
        two_s1s2 = field.add(s1s2, s1s2)
        C = field.sub(field.sub(v4, two_s1s2), s1)  # C = v4 - 2*s1*s2 - s1

        v3 = field.sub(a3, s1)
        s2_sq = field.mul(s2, s2)
        p1 = field.sub(field.sub(field.sub(v3, field.mul(s1, C)), s2_sq), s2)

        v2 = field.sub(field.sub(a2, s2), field.one())
        b1 = field.sub(field.sub(v2, field.mul(s1, p1)), field.mul(s2, C))  # b1 = s3 + p3
        a0A = field.sub(C, b1)  # a0A = s3 + p2

        v1 = field.add(field.mul(field.add(s2, field.one()), p1), field.mul(a0A, b1))
        p6 = field.sub(field.sub(a1, v1), b1)

        p4 = field.sub(field.sub(s1, p6), field.one())
        p5 = field.sub(s2, field.mul(p4, field.add(p6, field.one())))
        s3 = field.mul(p4, p5)

        p3 = field.sub(b1, s3)
        p2 = field.sub(a0A, s3)
        p0 = field.sub(a0, field.mul(p1, a0A))

        y = mul(x_form, x_form.add_const(p6, field))
        z = mul(
            AffineForm.sum_wires([1, y], const=p5),
            x_form.add_const(p4, field),
        )
        w = mul(AffineForm.wire(z).add_const(p3, field), x_form)
        v = mul(
            AffineForm.sum_wires([1, z], const=p2),
            AffineForm.wire(w).add_const(p1, field),
        )
        out = AffineForm.sum_wires([y, w, v], const=p0)
        return PolynomialChain(wire_names=wire_names, gates=gates, output=out, field=field)

    raise NotImplementedError(
        f"monic degree {n} not yet supported by the paper-style compiler; "
        "implement the remaining constructions from sections/constructions.tex / old/good-polynomials.tex"
    )


def compile_polynomial_chain(coeffs: Iterable[Number], modulus: Optional[int] = None) -> PolynomialChain:
    """
    Compile P(x) = sum_i a_i x^i to a polynomial chain schedule.

    Args:
        coeffs: iterable [a0,a1,...,an]
        modulus: optional prime modulus for field arithmetic
    """
    coeffs_list = list(coeffs)
    if not coeffs_list:
        raise ValueError("coeffs must be non-empty")

    use_fractions = modulus is None and not any(isinstance(c, float) for c in coeffs_list)
    field = Field(modulus=modulus, use_fractions=use_fractions)

    coeffs_list = _trim_trailing_zeros(coeffs_list, field)
    _require_monic(coeffs_list, field)

    # Decode coefficients into the paper parameters α0..α_{n-1} for P_n[α],
    # then compile the paper construction. This is the intended “coeffs → schedule” path.
    params = _decode_P_coeffs_to_paper_params(coeffs_list, field)
    return compile_paper_params_chain(params, modulus=modulus)


def compile_paper_params_chain(params: Iterable[Number], modulus: Optional[int] = None) -> PolynomialChain:
    """
    Compile the paper's parameterized polynomial family `P_n[α0..α_{n-1}]` into a chain.

    This is the forward (evaluation) direction: it does *not* implement the coefficient → parameter
    decoding step from the notes.
    """

    params_list = list(params)
    if not params_list:
        raise ValueError("params must be non-empty")

    use_fractions = modulus is None and not any(isinstance(c, float) for c in params_list)
    field = Field(modulus=modulus, use_fractions=use_fractions)
    params_list = [field.coerce(a) for a in params_list]

    n = len(params_list)
    builder = ChainBuilder(field)

    def build_P(deg: int, a: List[Number]) -> AffineForm:
        if deg != len(a):
            raise ValueError("internal error: parameter length mismatch in build_P")
        if deg == 1:
            return builder.x.add_const(a[0], field)
        if deg == 5:
            return _paper_P5(builder, a)
        if deg == 7:
            two = field.add(field.one(), field.one())
            if field.is_zero(two):
                return _paper_P7_char2(builder, a)
            return _paper_P7(builder, a)
        if (deg % 2) == 0:
            q = build_P(deg - 1, a[1:])
            return builder.mul(q, builder.x).add_const(a[0], field)

        T1, T2, _H2 = _paper_splittable_pair(builder, deg, a)
        return builder.mul(T1, builder.x).add(T2, field)

    out = build_P(n, params_list)
    chain = builder.finalize(out)
    chain.validate()
    return chain


def _eval_poly_direct(coeffs: List[Number], x: Number, field: Field) -> Number:
    # Horner for verification
    coeffs = _trim_trailing_zeros(coeffs, field)
    acc = field.zero()
    for c in reversed(coeffs):
        acc = field.add(field.mul(acc, field.coerce(x)), field.coerce(c))
    return acc


def main() -> None:
    import argparse

    p = argparse.ArgumentParser(description="Compile polynomial to a multiplication schedule")
    p.add_argument("coeffs", nargs="+", help="Coefficients a0 a1 ... an (ints or rationals like p/q)")
    p.add_argument("--mod", type=int, default=None, help="Prime modulus (compile over GF(p))")
    p.add_argument(
        "--params",
        action="store_true",
        help="Interpret positional args as paper parameters α0..α_{n-1} for P_n (instead of polynomial coefficients)",
    )
    p.add_argument(
        "--selftest",
        action="store_true",
        help="Run a quick internal self-test of the paper constructions (ignores the provided args except --mod)",
    )
    p.add_argument(
        "--check",
        action="store_true",
        help="Verify the compiled schedule by comparing against direct Horner evaluation at random x values",
    )
    p.add_argument(
        "--check-trials",
        type=int,
        default=10,
        help="Number of random x values for --check (default: 10)",
    )
    args = p.parse_args()

    coeffs: List[Number] = []
    for s in args.coeffs:
        if "/" in s:
            coeffs.append(Fraction(s))
        elif "." in s or "e" in s or "E" in s:
            coeffs.append(float(s))
        else:
            coeffs.append(int(s))

    if args.selftest:
        # Self-test the *parameterized* construction, since that’s what handles all degrees.
        for n in range(1, 201):
            chain = compile_paper_params_chain([0] * n, modulus=args.mod)
            want = 0 if n <= 1 else (1 if n == 2 else (n // 2 + 1))
            if chain.mul_count != want:
                raise SystemExit(f"selftest failed at n={n}: got {chain.mul_count}, want {want}")
        print("selftest OK (n<=200)")
        return

    chain = (
        compile_paper_params_chain(coeffs, modulus=args.mod)
        if args.params
        else compile_polynomial_chain(coeffs, modulus=args.mod)
    )
    chain.validate()
    n = len(coeffs) if args.params else (len(_trim_trailing_zeros(coeffs, chain.field)) - 1)
    expected = 0 if n <= 1 else (1 if n == 2 else (n // 2 + 1))
    print(f"# muls: {chain.mul_count} (target {expected} for monic degree {n})")
    print(chain.describe())

    if args.check:
        import random

        if args.params:
            print("# --check: (params mode) smoke-tests chain.eval(x) at random x values")
            for _ in range(args.check_trials):
                x = random.randrange(0, args.mod) if args.mod else random.randint(-5, 5)
                _ = chain.eval(x)
            print("OK")
            return

        print("# --check: compares chain.eval(x) against Horner (reference) on random x values")
        for _ in range(args.check_trials):
            x = random.randrange(0, args.mod) if args.mod else random.randint(-5, 5)
            got = chain.eval(x)
            want = _eval_poly_direct(coeffs, x, chain.field)
            if got != want:
                raise SystemExit(f"mismatch at x={x}: got {got}, want {want}")
        print("OK")


if __name__ == "__main__":
    main()
