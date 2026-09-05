import FastPoly.Examples.Char2Degree17Q9Pivot

/-!
# The supplied sextic cancellation behind degree seventeen's Q8 pivot

All earlier wires are opaque polynomials. Two shared-factor cancellations
give `(X+u)*B+(u+v)=S6`. This shows that the row-seven compensation is zero
when Q8 changes: the last gate's first offset changes by delta, and its
second offset stays fixed. No output coefficient baseline is expanded.
-/

namespace FastPoly.Char2Degree17SexticCancellation

set_option maxHeartbeats 20000

open Polynomial Char2UnequalOffsets Char2RecoveredProductUpdates
open Char2Degree17Wires Char2Degree17TerminalPivots

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def sextic (y z t : R[X]) (a5 a6 a7 a8 : R) : R[X] :=
  (X + y + C (a7 + a5)) * (z + t + C a6) +
    C (a6 + a8) * (X + z + C a7)

theorem crown_cancel (y z t u v : R[X]) (a5 a6 a7 a8 : R)
    (hu : u = (y + z + C a5) * (z + t + C a6))
    (hv : v = (X + z + C a7) * (X + z + t + u + C a8)) :
    (X + u) * (X + z + C a7) + (u + v) = sextic y z t a5 a6 a7 a8 := by
  have hcancel : (X + u) + (X + z + t + u + C a8) = z + t + C a8 := by
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
  have hshift : (z + t + C a6) + C (a6 + a8) = z + t + C a8 := by
    simp only [map_add, add_assoc, CharTwo.add_cancel_left]
  have hsum : (y + z + C a5) + (X + z + C a7) = X + y + C (a7 + a5) := by
    simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]
  rw [hv]
  calc
    _ = u + (X + z + C a7) * ((X + u) + (X + z + t + u + C a8)) := by ring
    _ = u + (X + z + C a7) * (z + t + C a8) := by rw [hcancel]
    _ = (y + z + C a5) * (z + t + C a6) +
        (X + z + C a7) * ((z + t + C a6) + C (a6 + a8)) := by rw [hu, hshift]
    _ = ((y + z + C a5) + (X + z + C a7)) * (z + t + C a6) +
        C (a6 + a8) * (X + z + C a7) := by ring
    _ = sextic y z t a5 a6 a7 a8 := by rw [hsum]; rfl

theorem baseline_higher_shift (A H B : R[X]) (δ : R) (j : ℕ) :
    (baseline A (H + C δ * B)).coeff j =
      (baseline A H).coeff j + δ * (A * B).coeff j := by
  have he : baseline A (H + C δ * B) = baseline A H + C δ * (A * B) := by
    simp only [baseline]
    ring
  rw [he, coeff_add, coeff_C_mul]

/-- The explicit two-row inverse changes only the first last-gate offset. -/
theorem recover_higher_shift (A H B : R[X]) (q : R × R) (δ : R)
    (h10 : (A * B).coeff 10 = 1) (h7 : (A * B).coeff 7 = H.coeff 7)
    (hB7 : B.coeff 7 = 0) :
    recover A (H + C δ * B) 7 10 q =
      ((recover A H 7 10 q).1 + δ, (recover A H 7 10 q).2) := by
  have hb10 := baseline_higher_shift A H B δ 10
  have hb7 := baseline_higher_shift A H B δ 7
  simp only [h10, h7, mul_one] at hb10 hb7
  have hH7 : (H + C δ * B).coeff 7 = H.coeff 7 := by
    rw [coeff_add, coeff_C_mul, hB7, mul_zero, add_zero]
  simp only [recover, hb10, hb7, hH7]
  apply Prod.ext
  · exact (add_assoc _ _ _).symm
  · rw [← add_assoc q.1 ((baseline A H).coeff 10) δ, add_mul]
    simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

noncomputable def slope (S B : R[X]) (a b : R) : R[X] := S + C a * B + C b

theorem final_gate_shift (A H B S : R[X]) (a b δ : R) (hc : A * B + H = S) :
    gate A (H + C δ * B) (a + δ, b) =
      gate A H (a, b) + C δ * slope S B a b + C (δ ^ 2) * B := by
  rw [← hc]
  simp only [gate, slope, map_add, map_pow]
  ring

variable [Nontrivial R]

theorem sextic_monic (y z t : R[X]) (a5 a6 a7 a8 : R)
    (hy : IsMonicOfDegree y 2) (hz : IsMonicOfDegree z 3) (ht : IsMonicOfDegree t 4) :
    IsMonicOfDegree (sextic y z t a5 a6 a7 a8) 6 := by
  have hf := shifted_monic (add_monic (isMonicOfDegree_X R) hy (by omega))
    (by omega) (a7 + a5)
  have hg := shifted_monic (add_monic hz ht (by omega)) (by omega) a6
  have hb := shifted_monic (add_monic (isMonicOfDegree_X R) hz (by omega)) (by omega) a7
  have hlo : (C (a6 + a8) * (X + z + C a7)).natDegree < 6 := by
    have hle := natDegree_C_mul_le (a6 + a8) (X + z + C a7)
    rw [hb.natDegree_eq] at hle
    omega
  exact (hf.mul hg).add_right hlo

theorem slope_monic (S B : R[X]) (a b : R)
    (hS : IsMonicOfDegree S 6) (hB : IsMonicOfDegree B 3) :
    IsMonicOfDegree (slope S B a b) 6 := by
  have hlo : (C a * B).natDegree < 6 := by
    have hle := natDegree_C_mul_le a B
    rw [hB.natDegree_eq] at hle
    omega
  exact shifted_monic (hS.add_right hlo) (by omega) b

theorem reconstructed_shift (A H B S : R[X]) (q : R × R) (δ : R)
    (hA : IsMonicOfDegree A 7) (hB : IsMonicOfDegree B 3)
    (hS : IsMonicOfDegree S 6) (hc : A * B + H = S) :
    recoveredGate A (H + C δ * B) 7 10 q =
      recoveredGate A H 7 10 q +
        C δ * slope S B (recover A H 7 10 q).1 (recover A H 7 10 q).2 + C (δ ^ 2) * B := by
  have hAB : IsMonicOfDegree (A * B) 10 := hA.mul hB
  have h10 : (A * B).coeff 10 = 1 := by
    rw [← hAB.natDegree_eq]
    exact hAB.monic.coeff_natDegree
  have hS7 : S.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hS.natDegree_eq ▸ (by omega : 6 < 7))
  have hB7 : B.coeff 7 = 0 := coeff_eq_zero_of_natDegree_lt (hB.natDegree_eq ▸ (by omega : 3 < 7))
  have h7 : (A * B).coeff 7 = H.coeff 7 := by
    have he := congrArg (fun p : R[X] => p.coeff 7) hc
    change (A * B + H).coeff 7 = S.coeff 7 at he
    rw [coeff_add, hS7] at he
    exact CharTwo.add_eq_zero.mp he
  rw [recoveredGate, recover_higher_shift A H B q δ h10 h7 hB7]
  exact final_gate_shift A H B S _ _ δ hc

theorem reconstructed_change (A H B S : R[X]) (q : R × R) (δ : R)
    (hA : IsMonicOfDegree A 7) (hB : IsMonicOfDegree B 3)
    (hS : IsMonicOfDegree S 6) (hc : A * B + H = S) :
    TopChange (recoveredGate A H 7 10 q) (recoveredGate A (H + C δ * B) 7 10 q) 6 δ := by
  let s := slope S B (recover A H 7 10 q).1 (recover A H 7 10 q).2
  have hs : IsMonicOfDegree s 6 := slope_monic S B _ _ hS hB
  have hs6 : s.coeff 6 = 1 := by rw [← hs.natDegree_eq]; exact hs.monic.coeff_natDegree
  have hB6 : B.coeff 6 = 0 := coeff_eq_zero_of_natDegree_lt (hB.natDegree_eq ▸ (by omega : 3 < 6))
  have he := reconstructed_shift A H B S q δ hA hB hS hc
  change recoveredGate A (H + C δ * B) 7 10 q = recoveredGate A H 7 10 q + C δ * s + C (δ ^ 2) * B at he
  constructor
  · rw [he, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, hs6, hB6,
      mul_one, mul_zero, add_zero]
  · intro j hj
    have hsj : s.coeff j = 0 := coeff_eq_zero_of_natDegree_lt (hs.natDegree_eq ▸ hj)
    have hBj : B.coeff j = 0 := coeff_eq_zero_of_natDegree_lt
      (hB.natDegree_eq ▸ (by omega : 3 < j))
    rw [he, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul, hsj, hBj,
      mul_zero, mul_zero, add_zero, add_zero]

end FastPoly.Char2Degree17SexticCancellation
