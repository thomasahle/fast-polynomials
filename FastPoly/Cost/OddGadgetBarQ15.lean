import FastPoly.Cost.OddGadgetCircuit
import FastPoly.Examples.BarQ15Structural

/-!
# The degree-fifteen barred presentation bridge

The uniform barred compiler at `k = 1` and the optimized finite decoder use the same
seven-product circuit, but the latter writes the supplied monic quadratic and quartic
in coefficient normal form.  This file proves the missing equality explicitly.  It
lets the realized odd-gadget dispatcher use the finite decoder without changing the
circuit witness.
-/

namespace FastPoly.Cost.OddGadget

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

omit [Nontrivial A] in
/-- A monic quadratic is exactly its coefficient normal form. -/
theorem monicQuadratic_eq_barQ15H2 {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2) :
    H₂ = FastPoly.BarQ15.H2 (H₂.coeff 0) (H₂.coeff 1) := by
  have htop := hH₂m.coeff_natDegree
  rw [hH₂d] at htop
  conv_lhs => rw [H₂.as_sum_range_C_mul_X_pow' (n := 3) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, htop, map_one,
    FastPoly.BarQ15.H2]
  ring

omit [Nontrivial A] in
/-- A monic quartic is exactly its coefficient normal form. -/
theorem monicQuartic_eq_barQ15H4 {H₄ : A[X]}
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) :
    H₄ = FastPoly.BarQ15.H4 (H₄.coeff 0) (H₄.coeff 1)
      (H₄.coeff 2) (H₄.coeff 3) := by
  have htop := hH₄m.coeff_natDegree
  rw [hH₄d] at htop
  conv_lhs => rw [H₄.as_sum_range_C_mul_X_pow' (n := 5) (by omega)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, htop, map_one,
    FastPoly.BarQ15.H4]
  ring

omit [Nontrivial A] in
/-- At `k = 1` the uniform barred expression is literally the optimized finite
degree-fifteen expression after normalizing the supplied monic powers. -/
theorem barredOne_eq_barQ15 {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (θ : ℕ → A) :
    FastPoly.BarQGeneral.gadget H₂ H₄ 1 θ =
      FastPoly.BarQ15.barQ15 (H₂.coeff 0) (H₂.coeff 1)
        (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) θ := by
  conv_lhs =>
    rw [monicQuadratic_eq_barQ15H2 hH₂m hH₂d,
      monicQuartic_eq_barQ15H4 hH₄m hH₄d]
  simp only [FastPoly.BarQGeneral.gadget, FastPoly.BarQGeneral.barQ,
    FastPoly.Tpair, FastPoly.TF, if_pos le_rfl,
    FastPoly.BarQGeneral.outer, FastPoly.BarQGeneral.C1,
    FastPoly.BarQGeneral.C2, FastPoly.BarQGeneral.U0,
    FastPoly.BarQGeneral.V0, FastPoly.BarQGeneral.Q3,
    FastPoly.BarQGeneral.H8, FastPoly.BarQGeneral.tower,
    FastPoly.BarQ15.barQ15, FastPoly.BarQ15.C1, FastPoly.BarQ15.C2,
    FastPoly.BarQ15.U0, FastPoly.BarQ15.V0, FastPoly.BarQ15.Q3,
    FastPoly.BarQ15.H8, FastPoly.BarQ15.w, FastPoly.BarQ15.u,
    FastPoly.BarQ15.v, FastPoly.BarQ15.rho, FastPoly.BarQ15.a,
    FastPoly.BarQ15.b]

/-- The uniform seven-product compiler realizes the exact polynomial returned by the
optimized finite decoder. -/
noncomputable def barredOneRealized {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (θ : ℕ → A) :
    Realization (R := R) H₂ H₄ θ
      (FastPoly.BarQ15.barQ15 (H₂.coeff 0) (H₂.coeff 1)
        (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) θ) 7 :=
  (barredRealized (R := R) H₂ H₄ θ 1 (by omega)).copy
    (barredOne_eq_barQ15 hH₂m hH₂d hH₄m hH₄d θ)

end FastPoly.Cost.OddGadget
