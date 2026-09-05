import FastPoly.Examples.Char2Degree17Q8Pivot

/-!
# The reduced high frame of the existing degree-17 circuit

Above row ten the circuit is exactly `A^2*B + A*S6`, with the already
checked monic septic A, cubic B, and factored sextic S6. The omitted terms
are kept as a named degree-ten correction, not expanded into raw keys.
-/

namespace FastPoly.Char2Degree17HighFrame

set_option maxHeartbeats 20000

open Polynomial Char2UnequalOffsets Char2Degree17Wires Char2Degree17GateCoordinates
open Char2Degree17TerminalFrame Char2Degree17TerminalPivots Char2Degree17Q9Pivot
open Char2Degree17Q8Pivot

variable {R : Type*} [CommRing R] [CharP R 2]

noncomputable def A (q : Vector R) : R[X] := X + du q

noncomputable def high (q : Vector R) : R[X] := A q ^ 2 * B q + A q * S6 q

noncomputable def correction (q : Vector R) : R[X] :=
  dj q + dell q + C (aw q).1 * (du q + dv q) +
    C (aw q).2 * A q + C ((aw q).1 * (aw q).2) + C (q 16)

theorem higher_eq (q : Vector R) : du q + dv q = A q * B q + S6 q := by
  rw [← sextic_identity]
  change du q + dv q = A q * B q + (A q * B q + (du q + dv q))
  rw [CharTwo.add_cancel_left]

theorem split_product (a h b s : R[X]) (α β : R) (hh : h = a * b + s) :
    gate a h (α, β) = a ^ 2 * b + a * s + C α * h + C β * a + C (α * β) := by
  have hah : a * h = a ^ 2 * b + a * s := by rw [hh]; ring
  calc
    _ = a * h + C α * h + C β * a + C (α * β) := by
      simp only [gate, map_mul]
      ring
    _ = _ := by rw [hah]

theorem w_split (q : Vector R) :
    dw q = high q + C (aw q).1 * (du q + dv q) +
      C (aw q).2 * A q + C ((aw q).1 * (aw q).2) :=
  split_product (A q) (du q + dv q) (B q) (S6 q) (aw q).1 (aw q).2 (higher_eq q)

theorem outputQ_split (q : Vector R) : outputQ q = high q + correction q := by
  rw [outputQ_as_wires, w_split]
  simp only [correction, add_assoc, add_comm, add_left_comm]

variable [Nontrivial R]

theorem A_monic (q : Vector R) : IsMonicOfDegree (A q) 7 := frame_lowerW_monic q

theorem correction_degree (q : Vector R) : (correction q).natDegree ≤ 10 := by
  have hj : (dj q).natDegree ≤ 10 := by
    have hm : IsMonicOfDegree (dj q) 3 := by simpa only [j_keys] using j_monic (keys q)
    rw [hm.natDegree_eq]
    omega
  have hl : (dell q).natDegree ≤ 10 := by
    have hm : IsMonicOfDegree (dell q) 7 := by simpa only [ell_keys] using ell_monic (keys q)
    rw [hm.natDegree_eq]
    omega
  have hh : (C (aw q).1 * (du q + dv q)).natDegree ≤ 10 :=
    (natDegree_C_mul_le _ _).trans (frame_higherW_monic q).natDegree_eq.le
  have ha : (C (aw q).2 * A q).natDegree ≤ 10 := by
    have he := (natDegree_C_mul_le (aw q).2 (A q)).trans (A_monic q).natDegree_eq.le
    exact he.trans (by omega)
  have hab : (C ((aw q).1 * (aw q).2)).natDegree ≤ 10 := by rw [natDegree_C]; omega
  have hc : (C (q 16)).natDegree ≤ 10 := by rw [natDegree_C]; omega
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hj hl) hh) ha) hab) hc

/-- This equality concerns the actual counted circuit, not a replacement. -/
theorem outputQ_coeff_high (q : Vector R) (j : ℕ) (hj : 10 < j) :
    (outputQ q).coeff j = (high q).coeff j := by
  have hz : (correction q).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt ((correction_degree q).trans_lt hj)
  rw [outputQ_split, coeff_add, hz, add_zero]

theorem AS6_monic (q : Vector R) : IsMonicOfDegree (A q * S6 q) 13 :=
  (A_monic q).mul (S6_monic q)

theorem high_monic (q : Vector R) : IsMonicOfDegree (high q) 17 := by
  have hs : IsMonicOfDegree (A q ^ 2 * B q) 17 :=
    ((A_monic q).pow 2).mul (B_monic q)
  exact hs.add_right ((AS6_monic q).natDegree_eq ▸ (by omega : 13 < 17))

end FastPoly.Char2Degree17HighFrame
