import FastPoly.Examples.Char2DecoderSteps
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Lean.Elab.Tactic.Omega

/-!
# Two offset reads at unequal monic degrees

The gate-level inverse used by `char2/verify_n17_uniform_symbolic.py`.
For `0 < dl < dh`, the two selected rows of `(lower + a) * (higher + b)`
recover `a` first and then `b`. The known product is kept opaque throughout.
Both compositions are checked against the actual polynomial product.
-/

namespace FastPoly.Char2UnequalOffsets

set_option maxHeartbeats 20000

open Polynomial Char2Decoder

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def gate (lower higher : R[X]) (offsets : R × R) : R[X] :=
  (lower + C offsets.1) * (higher + C offsets.2)

noncomputable def baseline (lower higher : R[X]) : R[X] := lower * higher

/-- Read the higher pivot before the lower pivot. -/
noncomputable def rows (lower higher : R[X]) (dl dh : ℕ)
    (offsets : R × R) : R × R :=
  ((gate lower higher offsets).coeff dh, (gate lower higher offsets).coeff dl)

/-- The named unit slope at the second row multiplies the already read `a`. -/
noncomputable def recover (lower higher : R[X]) (dl dh : ℕ) (q : R × R) : R × R :=
  let a := q.1 + (baseline lower higher).coeff dh
  (a, q.2 + ((baseline lower higher).coeff dl + a * higher.coeff dl))

omit [CharP R 2] in
theorem gate_coeff (lower higher : R[X]) (offsets : R × R)
    (j : ℕ) (hj : j ≠ 0) :
    (gate lower higher offsets).coeff j =
      (baseline lower higher).coeff j + offsets.1 * higher.coeff j +
        lower.coeff j * offsets.2 := by
  simp only [gate, baseline, add_mul, mul_add, coeff_add, coeff_C_mul,
    coeff_mul_C, coeff_C, hj, ite_false, zero_mul, add_zero]

omit [CharP R 2] in
theorem rows_eq (lower higher : R[X]) (dl dh : ℕ)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) (offsets : R × R) :
    rows lower higher dl dh offsets =
      ((baseline lower higher).coeff dh + offsets.1,
       ((baseline lower higher).coeff dl + offsets.1 * higher.coeff dl) + offsets.2) := by
  have hdl : dl ≠ 0 := by omega
  have hdh : dh ≠ 0 := by omega
  have hlzero : lower.coeff dh = 0 :=
    coeff_eq_zero_of_natDegree_lt (hl.natDegree_eq ▸ hlt)
  have hlone : lower.coeff dl = 1 := by
    rw [← hl.natDegree_eq]; exact hl.monic.coeff_natDegree
  have hhone : higher.coeff dh = 1 := by
    rw [← hh.natDegree_eq]; exact hh.monic.coeff_natDegree
  simp only [rows, gate_coeff lower higher offsets dh hdh,
    gate_coeff lower higher offsets dl hdl, hlzero, hlone, hhone,
    mul_one, one_mul, zero_mul, add_zero]

theorem recover_rows (lower higher : R[X]) (dl dh : ℕ)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) (offsets : R × R) :
    recover lower higher dl dh (rows lower higher dl dh offsets) = offsets := by
  rw [rows_eq lower higher dl dh hl hh hpos hlt]
  simp only [recover, cancel_tail]

theorem rows_recover (lower higher : R[X]) (dl dh : ℕ)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) (q : R × R) :
    rows lower higher dl dh (recover lower higher dl dh q) = q := by
  rw [rows_eq lower higher dl dh hl hh hpos hlt]
  simp only [recover]
  apply Prod.ext
  · change (baseline lower higher).coeff dh +
      (q.1 + (baseline lower higher).coeff dh) = q.1
    rw [← add_assoc, cancel_tail]
  · change ((baseline lower higher).coeff dl +
      (q.1 + (baseline lower higher).coeff dh) * higher.coeff dl) +
      (q.2 + ((baseline lower higher).coeff dl +
      (q.1 + (baseline lower higher).coeff dh) * higher.coeff dl)) = q.2
    rw [← add_assoc, cancel_tail]

/-- The actual selected gate rows, with the supplied two-step inverse. -/
noncomputable def equiv (lower higher : R[X]) (dl dh : ℕ)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) : (R × R) ≃ (R × R) where
  toFun := rows lower higher dl dh
  invFun := recover lower higher dl dh
  left_inv := recover_rows lower higher dl dh hl hh hpos hlt
  right_inv := rows_recover lower higher dl dh hl hh hpos hlt

end FastPoly.Char2UnequalOffsets
