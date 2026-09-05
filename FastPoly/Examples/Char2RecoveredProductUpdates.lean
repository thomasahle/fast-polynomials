import FastPoly.Examples.Char2UnequalOffsets
import Mathlib.Tactic.Ring

/-!
# Local updates of a product reconstructed from its two selected rows

The lower and higher factors stay opaque. These are finite differences of the
supplied two-offset inverse, not an expansion through any earlier circuit gate.
The high-row shift compensates the already selected low row; a low-row shift
has exactly the shifted lower factor as its named slope.
-/

namespace FastPoly.Char2RecoveredProductUpdates

set_option maxHeartbeats 20000

open Polynomial Char2UnequalOffsets

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def recoveredGate (lower higher : R[X]) (dl dh : ℕ) (q : R × R) : R[X] :=
  gate lower higher (recover lower higher dl dh q)

omit [CharP R 2] in
theorem recover_high (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R) :
    recover lower higher dl dh (q.1 + δ, q.2) =
      ((recover lower higher dl dh q).1 + δ,
       (recover lower higher dl dh q).2 + δ * higher.coeff dl) := by
  simp only [recover]
  apply Prod.ext <;> ring

omit [CharP R 2] in
theorem recover_low (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R) :
    recover lower higher dl dh (q.1, q.2 + δ) =
      ((recover lower higher dl dh q).1,
       (recover lower higher dl dh q).2 + δ) := by
  simp only [recover]
  apply Prod.ext
  · rfl
  · ring

/-- The low-row pivot has the previously reconstructed lower factor as slope. -/
noncomputable def lowSlope (lower higher : R[X]) (dl dh : ℕ) (q : R × R) : R[X] :=
  lower + C (recover lower higher dl dh q).1

/-- The high-row pivot includes the correction preserving the low row. -/
noncomputable def highSlope (lower higher : R[X]) (dl dh : ℕ) (q : R × R) : R[X] :=
  (higher + C (recover lower higher dl dh q).2) +
    C (higher.coeff dl) * lowSlope lower higher dl dh q

omit [CharP R 2] in
theorem high_update (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R) :
    recoveredGate lower higher dl dh (q.1 + δ, q.2) =
      recoveredGate lower higher dl dh q + C δ * highSlope lower higher dl dh q +
        C (δ ^ 2 * higher.coeff dl) := by
  rw [recoveredGate, recover_high]
  simp only [gate, recoveredGate, highSlope, lowSlope, map_add, map_mul, map_pow]
  ring

omit [CharP R 2] in
theorem low_update (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R) :
    recoveredGate lower higher dl dh (q.1, q.2 + δ) =
      recoveredGate lower higher dl dh q + C δ * lowSlope lower higher dl dh q := by
  rw [recoveredGate, recover_low]
  simp only [gate, recoveredGate, lowSlope, map_add]
  ring

omit [CharP R 2] in
theorem coeff_above (lower higher : R[X]) (dl dh : ℕ) (q : R × R)
    (j : ℕ) (hpos : 0 < j) (hl : lower.natDegree < j) (hh : higher.natDegree < j) :
    (recoveredGate lower higher dl dh q).coeff j = (baseline lower higher).coeff j := by
  have hj : j ≠ 0 := by omega
  have hlzero : lower.coeff j = 0 := coeff_eq_zero_of_natDegree_lt hl
  have hhzero : higher.coeff j = 0 := coeff_eq_zero_of_natDegree_lt hh
  simp only [recoveredGate, gate_coeff lower higher _ j hj, hlzero, hhzero,
    mul_zero, zero_mul, add_zero]

omit [CharP R 2] in
theorem high_update_above (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R)
    (j : ℕ) (hpos : 0 < j) (hl : lower.natDegree < j) (hh : higher.natDegree < j) :
    (recoveredGate lower higher dl dh (q.1 + δ, q.2)).coeff j =
      (recoveredGate lower higher dl dh q).coeff j := by
  rw [coeff_above lower higher dl dh _ j hpos hl hh,
    coeff_above lower higher dl dh q j hpos hl hh]

omit [CharP R 2] in
theorem low_update_above (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R)
    (j : ℕ) (hpos : 0 < j) (hl : lower.natDegree < j) :
    (recoveredGate lower higher dl dh (q.1, q.2 + δ)).coeff j =
      (recoveredGate lower higher dl dh q).coeff j := by
  have hj : j ≠ 0 := by omega
  have hlzero : lower.coeff j = 0 := coeff_eq_zero_of_natDegree_lt hl
  rw [low_update]
  simp only [coeff_add, coeff_C_mul, lowSlope, coeff_C, hj, ite_false,
    hlzero, add_zero, mul_zero]

theorem high_row (lower higher : R[X]) (dl dh : ℕ) (q : R × R)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) :
    (recoveredGate lower higher dl dh q).coeff dh = q.1 :=
  congrArg Prod.fst (rows_recover lower higher dl dh hl hh hpos hlt q)

theorem low_row (lower higher : R[X]) (dl dh : ℕ) (q : R × R)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) :
    (recoveredGate lower higher dl dh q).coeff dl = q.2 :=
  congrArg Prod.snd (rows_recover lower higher dl dh hl hh hpos hlt q)

theorem high_update_low_row (lower higher : R[X]) (dl dh : ℕ) (q : R × R) (δ : R)
    (hl : IsMonicOfDegree lower dl) (hh : IsMonicOfDegree higher dh)
    (hpos : 0 < dl) (hlt : dl < dh) :
    (recoveredGate lower higher dl dh (q.1 + δ, q.2)).coeff dl =
      (recoveredGate lower higher dl dh q).coeff dl := by
  rw [low_row lower higher dl dh _ hl hh hpos hlt,
    low_row lower higher dl dh q hl hh hpos hlt]

end FastPoly.Char2RecoveredProductUpdates
