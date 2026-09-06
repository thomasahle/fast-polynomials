import FastPoly.Examples.Char2Degree25TwentyTwoWires

/-! Bounded output corrections for the supplied q22 and q23 directions.
The q22 high cancellation is just the sum of two monic degree-seven wires.
These are raw direction certificates, not yet the final normalized rows. -/

namespace FastPoly.Char2Degree25TwentyTwoBounds

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree25Frame Char2Degree25HighFrame Char2Degree25TwentyTwoWires
open Char2Degree25RowThirteen (L P sSlope ellSlope L_monic sSlope_monic ellSlope_monic)

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem U_monic (a : ℕ → R) : IsMonicOfDegree (U a) 5 :=
  (z_add_t_monic a).add_right (C_lt _ _ (by omega))

theorem Q2_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (Q2 a d) 2 := by
  have hl : (L a + 1).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (L_monic a).natDegree_eq.le (by rw [natDegree_one]; omega)
  have hd : (C d * (L a + 1)).natDegree < 2 := by
    apply natDegree_mul_le.trans_lt
    rw [natDegree_C]
    omega
  exact ((((L_monic a).mul (isMonicOfDegree_X_add_one (a 7 + a 8))).add_left
    ((L_monic a).natDegree_eq.trans_lt (by omega))).add_right
    (C_lt _ _ (by omega))).add_right hd

theorem bracket_degree (a : ℕ → R) (d : R) : (bracket a d).natDegree ≤ 6 := by
  have hU : (C (K a) * U a).natDegree ≤ 5 := by
    apply natDegree_mul_le.trans
    rw [natDegree_C, (U_monic a).natDegree_eq]
  have hl : (sSlope a + rLeft a + X + C (a 15) + ellSlope a + C (K a) * U a).natDegree ≤ 5 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le
          (natDegree_add_le_of_degree_le
            (natDegree_add_le_of_degree_le (sSlope_monic a).natDegree_eq.le
              (rLeft_monic a).natDegree_eq.le)
            (natDegree_X_le.trans (by omega)))
          (by rw [natDegree_C]; omega))
        ((ellSlope_monic a).natDegree_eq.le.trans (by omega))) hU
  have hh : IsMonicOfDegree (hLeft a * Q2 a d) 7 :=
    (hLeft_monic a).mul (Q2_monic a d)
  have hj : IsMonicOfDegree (jLeft a * ellSlope a) 7 :=
    (jLeft_monic a).mul (ellSlope_monic a)
  have hc : (hLeft a * Q2 a d + jLeft a * ellSlope a).natDegree < 7 := by
    have he := IsMonicOfDegree.natDegree_sub_lt (by omega : 7 ≠ 0) hh hj
    rwa [CharTwo.sub_eq_add] at he
  unfold bracket
  rw [add_assoc (sSlope a + rLeft a + X + C (a 15) + ellSlope a + C (K a) * U a)]
  exact natDegree_add_le_of_degree_le (hl.trans (by omega)) (by omega)

theorem outputSlope_degree (a : ℕ → R) (d : R) : (outputSlope a d).natDegree ≤ 11 := by
  have hn : (nRight a * bracket a d).natDegree ≤ 11 := by
    apply natDegree_mul_le.trans
    rw [(nRight_monic a).natDegree_eq]
    have hb := bracket_degree a d
    omega
  exact natDegree_add_le_of_degree_le ((ellSlope_monic a).natDegree_eq.le.trans (by omega)) hn

theorem output_difference_degree (a : ℕ → R) (d : R) :
    (Char2Degree25Frame.output (shift a d) + Char2Degree25Frame.output a).natDegree ≤ 11 := by
  rw [output_change, cancel_tail]
  apply natDegree_mul_le.trans
  rw [natDegree_C]
  have h := outputSlope_degree a d
  omega

/-- The last unnormalized direction changes only raw a20. -/
def shift23 (a : ℕ → R) (d : R) : ℕ → R
  | 20 => a 20 + d
  | i => a i

noncomputable def slope23 (a : ℕ → R) : R[X] := nRight a * (ell a + C (a 21))

theorem j_change23 (a : ℕ → R) (d : R) :
    j (shift23 a d) = j a + C d * (ell a + C (a 21)) := by
  change (X + y + t a + C (a 20 + d)) * (ell a + C (a 21)) = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem nLeft_change23 (a : ℕ → R) (d : R) :
    nLeft (shift23 a d) = nLeft a + C d * (ell a + C (a 21)) := by
  change (X + t a + u a + s a + r a + g a + ell a + h a) +
    j (shift23 a d) + C (a 22) = _
  rw [j_change23]
  change _ = (X + t a + u a + s a + r a + g a + ell a + h a + j a + C (a 22)) + _
  ac_rfl

private theorem collect23 (hd nl nr c d s : R[X]) :
    hd + (nl + d * s) * nr + c = (hd + nl * nr + c) + d * (nr * s) := by ring

theorem output_change23 (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift23 a d) =
      Char2Degree25Frame.output a + C d * slope23 a := by
  change Char2Degree25Frame.head a + nLeft (shift23 a d) * nRight a + C (a 24) = _
  rw [nLeft_change23]
  exact collect23 _ _ _ _ _ _

theorem slope23_monic (a : ℕ → R) : IsMonicOfDegree (slope23 a) 11 :=
  (nRight_monic a).mul ((ell_monic a).add_right (C_lt _ _ (by omega)))

theorem output_difference_degree23 (a : ℕ → R) (d : R) :
    (Char2Degree25Frame.output (shift23 a d) + Char2Degree25Frame.output a).natDegree ≤ 11 := by
  rw [output_change23, cancel_tail]
  apply natDegree_mul_le.trans
  rw [natDegree_C, (slope23_monic a).natDegree_eq]

end FastPoly.Char2Degree25TwentyTwoBounds
