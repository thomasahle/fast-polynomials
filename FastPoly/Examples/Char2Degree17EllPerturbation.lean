import FastPoly.Examples.Char2Degree17TerminalPivots

/-!
# The local ell-gate perturbation for degree seventeen's Q9 pivot

The cubic input changes by `delta * X`. The supplied two-row inverse
compensates its offsets by `delta` and `delta * (tau + 1)`. The resulting
quintic slope is monic; the remaining correction has degree at most one.
Both input polynomials remain opaque throughout.
-/

namespace FastPoly.Char2Degree17EllPerturbation

set_option maxHeartbeats 20000

open Polynomial Char2UnequalOffsets Char2RecoveredProductUpdates
open Char2Degree17Wires Char2Degree17TerminalPivots

variable {R : Type*} [CommRing R] [CharP R 2]

theorem baseline_shift (p t : R[X]) (δ : R) (j : ℕ) :
    (baseline (p + C δ * X) t).coeff (j + 1) =
      (baseline p t).coeff (j + 1) + δ * t.coeff j := by
  simp only [baseline, add_mul, mul_assoc, coeff_add, coeff_C_mul, coeff_X_mul]

theorem recovered_offsets_shift (p t : R[X]) (q : R × R) (δ τ : R)
    (ht3 : t.coeff 3 = 1) (ht2 : t.coeff 2 = τ) :
    recover (p + C δ * X) t 3 4 q =
      ((recover p t 3 4 q).1 + δ,
       (recover p t 3 4 q).2 + δ * (τ + 1)) := by
  have h4 := baseline_shift p t δ 3
  have h3 := baseline_shift p t δ 2
  simp only [ht3, ht2, mul_one] at h4 h3
  simp only [recover, h4, h3, ht3, mul_one]
  apply Prod.ext <;> ring

noncomputable def slope (p t : R[X]) (q : R × R) (τ : R) : R[X] :=
  (X + 1) * (t + C (recover p t 3 4 q).2) +
    C (τ + 1) * (p + C (recover p t 3 4 q).1)

noncomputable def remainder (δ τ : R) : R[X] := C (δ ^ 2 * (τ + 1)) * (X + 1)

/-- The exact factor-level finite difference, including the low correction. -/
theorem gate_shift (p t : R[X]) (q : R × R) (δ τ : R)
    (ht3 : t.coeff 3 = 1) (ht2 : t.coeff 2 = τ) :
    recoveredGate (p + C δ * X) t 3 4 q =
      recoveredGate p t 3 4 q + C δ * slope p t q τ + remainder δ τ := by
  rw [recoveredGate, recovered_offsets_shift p t q δ τ ht3 ht2]
  simp only [recoveredGate, gate, slope, remainder, map_add, map_mul, map_pow, map_one]
  ring

variable [Nontrivial R]

theorem x_add_one_monic : IsMonicOfDegree ((X : R[X]) + 1) 1 := by
  simpa only [map_one] using isMonicOfDegree_X_add_one (1 : R)

theorem slope_monic (p t : R[X]) (q : R × R) (τ : R)
    (hp : IsMonicOfDegree p 3) (ht : IsMonicOfDegree t 4) :
    IsMonicOfDegree (slope p t q τ) 5 := by
  have hp' := shifted_monic hp (by omega) (recover p t 3 4 q).1
  have ht' := shifted_monic ht (by omega) (recover p t 3 4 q).2
  have hlow : (C (τ + 1) * (p + C (recover p t 3 4 q).1)).natDegree < 5 := by
    have hb := natDegree_C_mul_le (τ + 1) (p + C (recover p t 3 4 q).1)
    rw [hp'.natDegree_eq] at hb
    omega
  exact (x_add_one_monic.mul ht').add_right hlow

theorem remainder_degree (δ τ : R) : (remainder (R := R) δ τ).natDegree ≤ 1 := by
  exact (natDegree_C_mul_le _ _).trans x_add_one_monic.natDegree_eq.le

/-- The same supplied decoder now exposes Q9 as a unit pivot in row five. -/
theorem gate_change (p t : R[X]) (q : R × R) (δ τ : R)
    (hp : IsMonicOfDegree p 3) (ht : IsMonicOfDegree t 4)
    (ht3 : t.coeff 3 = 1) (ht2 : t.coeff 2 = τ) :
    TopChange (recoveredGate p t 3 4 q)
      (recoveredGate (p + C δ * X) t 3 4 q) 5 δ := by
  have hs := slope_monic p t q τ hp ht
  have hs5 : (slope p t q τ).coeff 5 = 1 := by
    rw [← hs.natDegree_eq]
    exact hs.monic.coeff_natDegree
  have hr5 : (remainder (R := R) δ τ).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt ((remainder_degree δ τ).trans_lt (by omega))
  constructor
  · rw [gate_shift p t q δ τ ht3 ht2, coeff_add, coeff_add, coeff_C_mul,
      hs5, hr5, mul_one, add_zero]
  · intro j hj
    have hsj : (slope p t q τ).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt (hs.natDegree_eq ▸ hj)
    have hrj : (remainder (R := R) δ τ).coeff j = 0 :=
      coeff_eq_zero_of_natDegree_lt ((remainder_degree δ τ).trans_lt (by omega))
    rw [gate_shift p t q δ τ ht3 ht2, coeff_add, coeff_add, coeff_C_mul,
      hsj, hrj, mul_zero, add_zero, add_zero]

end FastPoly.Char2Degree17EllPerturbation
