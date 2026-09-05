import FastPoly.Examples.Char2Degree23NormalizedPeel

/-! The explicit degree-seven slope after the fifteenth row-eight peel. -/

namespace FastPoly.Char2Degree23FifteenSlope

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23HighFrame Char2Degree23HighPivots

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def l (a : ℕ → R) : R[X] := X + C (a 2)
noncomputable def cubic (a : ℕ → R) : R[X] := z a + y ^ 2
noncomputable def J (a : ℕ → R) : R[X] :=
  y * C (a 2 + 1 + a 18 + a 20 + a 2 ^ 2) +
    C (a 4 + a 5) * (l a + 1) + C (a 2 ^ 2) * X + C (a 2 ^ 2 * (a 18 + a 20))
noncomputable def tail (a : ℕ → R) : R[X] :=
  z a * J a + (l a) ^ 2 * C (a 3) ^ 2 +
    (y + C (a 4) + C (a 5)) * l a * C (a 3) +
    (C (a 5) * y + C (a 4) * C (a 5)) +
    (C (a 20) * (X + y + C (a 18))) * (l a) ^ 2 +
    (y + C (a 9) + C (a 11) + C (a 13))
noncomputable def peeled (a : ℕ → R) : R[X] := z a * cubic a + tail a
noncomputable def rawSlope (a : ℕ → R) : R[X] :=
  u a + C (a 13) + (D a + 1) * (y + C (a 9) + C (a 11))
def rowEight (a : ℕ → R) : R := a 2 ^ 2 + a 9 + a 11

private theorem C_le (c : R) (n : ℕ) : (C c).natDegree ≤ n := by
  rw [natDegree_C]; exact Nat.zero_le _

private theorem product_cancel (Y X A B : R[X]) :
    (Y + A) * (X + Y + B) + Y ^ 2 = Y * X + (Y * B + A * X + A * Y + A * B) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem cubic_eq (a : ℕ → R) :
    cubic a = y * X + (y * C (a 1) + C (a 0) * X + C (a 0) * y + C (a 0) * C (a 1)) :=
  product_cancel y X (C (a 0)) (C (a 1))

theorem cubic_monic (a : ℕ → R) : IsMonicOfDegree (cubic a) 3 := by
  have h1 : (y * C (a 1)).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [y_monic.natDegree_eq, natDegree_C]
  have h2 : (C (a 0) * X).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [natDegree_C]; exact Nat.zero_add _ ▸ natDegree_X_le.trans (by omega)
  have h3 : (C (a 0) * y).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [natDegree_C, y_monic.natDegree_eq]
  have h4 : (C (a 0) * C (a 1)).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [natDegree_C, natDegree_C]; omega
  rw [cubic_eq]
  exact (y_monic.mul (isMonicOfDegree_X R)).add_right
    ((natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le h1 h2) h3) h4).trans_lt (by omega))

theorem l_square (a : ℕ → R) : (l a) ^ 2 = y + C (a 2 ^ 2) := by
  change (X + C (a 2)) ^ 2 = _
  rw [CharTwo.add_sq, ← map_pow]
  rw [pow_two]
  rfl

private theorem j_cancel (x Y b c e f : R[X]) :
    (Y + c) * (x + b + 1) + (Y + b ^ 2) * (x + Y + e + f) =
      Y ^ 2 + (Y * (b + 1 + e + f + b ^ 2) + c * (x + b + 1) +
        b ^ 2 * x + b ^ 2 * (e + f)) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem J_eq (a : ℕ → R) :
    (y + C (a 4) + C (a 5)) * (l a + 1) +
      (l a) ^ 2 * (X + y + C (a 18) + C (a 20)) = y ^ 2 + J a := by
  rw [l_square]
  have hs : y + C (a 4) + C (a 5) = y + C (a 4 + a 5) := by rw [map_add, add_assoc]
  rw [hs]
  change (y + C (a 4 + a 5)) * (X + C (a 2) + 1) +
    (y + C (a 2 ^ 2)) * (X + y + C (a 18) + C (a 20)) = _
  rw [map_pow, j_cancel]
  simp only [J, l, map_add, map_mul, map_one, map_pow]

private theorem pair_expand (h Y b c : R[X]) :
    (h + Y + b) * (h + c) = h ^ 2 + (Y + b + c) * h + (c * Y + b * c) := by ring

private theorem frame_expand (z b c d : R[X]) :
    (z + c) * (b + z + d) = z ^ 2 + z * (b + d + c) + c * (b + d) := by ring

private theorem square_frame (z l B A c e f : R[X]) :
    (((l + 1) * z + l * c) ^ 2 + B * ((l + 1) * z + l * c) + e) +
      (z ^ 2 + z * A + f) * l ^ 2 =
    z * (z + (B * (l + 1) + l ^ 2 * A)) + (l ^ 2 * c ^ 2 + B * l * c + e + f * l ^ 2) := by
  rw [CharTwo.add_sq, mul_pow, mul_pow, CharTwo.add_sq]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem u_frame (a : ℕ → R) :
    u a + D a * (l a) ^ 2 =
      z a * (z a + y ^ 2 + J a) +
        ((l a) ^ 2 * C (a 3) ^ 2 + (y + C (a 4) + C (a 5)) * l a * C (a 3) +
          (C (a 5) * y + C (a 4) * C (a 5)) +
          (C (a 20) * (X + y + C (a 18))) * (l a) ^ 2) := by
  rw [Char2Degree23HighFrame.u_eq]
  change (h a + y + C (a 4)) * (h a + C (a 5)) +
    ((z a + C (a 20)) * (X + y + z a + C (a 18))) * (l a) ^ 2 = _
  have hh : h a = (l a + 1) * z a + l a * C (a 3) := h_eq a
  rw [pair_expand, frame_expand, hh, square_frame, J_eq]
  rw [add_assoc (z a) (y ^ 2) (J a)]

private theorem row_cancel (u d Y b c e f : R[X]) :
    (u + f + (d + 1) * (Y + c + e)) + d * (b + c + e) =
      (u + d * (Y + b)) + (Y + c + e + f) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

private theorem assemble (z Y j t1 t2 t3 t4 s : R[X]) :
    (z * (z + Y + j) + (t1 + t2 + t3 + t4)) + s =
      z * (z + Y) + (z * j + t1 + t2 + t3 + t4 + s) := by ring

theorem rawSlope_eq (a : ℕ → R) : rawSlope a + D a * C (rowEight a) = peeled a := by
  unfold rawSlope rowEight
  rw [map_add, map_add, row_cancel, ← l_square, u_frame]
  unfold peeled cubic tail
  exact assemble _ _ _ _ _ _ _ _

theorem J_degree (a : ℕ → R) : (J a).natDegree ≤ 2 := by
  have h1 : (y * C (a 2 + 1 + a 18 + a 20 + a 2 ^ 2)).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [y_monic.natDegree_eq, natDegree_C]
  have hl : (l a + 1).natDegree ≤ 1 := natDegree_add_le_of_degree_le
    (isMonicOfDegree_X_add_one (a 2)).natDegree_eq.le (by rw [natDegree_one]; omega)
  have h2 : (C (a 4 + a 5) * (l a + 1)).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [natDegree_C]; omega
  have h3 : (C (a 2 ^ 2) * X).natDegree ≤ 2 := by
    apply natDegree_mul_le.trans; rw [natDegree_C]; have hx := (natDegree_X_le (R := R)); omega
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h2) h3) (C_le _ _)

theorem tail_degree (a : ℕ → R) : (tail a).natDegree ≤ 6 := by
  have hz := (z_monic a).natDegree_eq.le
  have hy := (y_monic (R := R)).natDegree_eq.le
  have hl := (isMonicOfDegree_X_add_one (a 2)).natDegree_eq.le
  have hl2 : ((l a) ^ 2).natDegree ≤ 2 := by
    rw [l_square]; exact natDegree_add_le_of_degree_le hy (C_le _ _)
  have hb : (y + C (a 4) + C (a 5)).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hy (C_le _ _)) (C_le _ _)
  have hc3 : (C (a 3) ^ 2).natDegree ≤ 0 := by rw [← map_pow, natDegree_C]
  have hxy : (X + y + C (a 18)).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le x_add_y_monic.natDegree_eq.le (C_le _ _)
  have h1 : (z a * J a).natDegree ≤ 6 :=
    natDegree_mul_le.trans (Nat.add_le_add hz (J_degree a))
  have h2 : ((l a) ^ 2 * C (a 3) ^ 2).natDegree ≤ 6 :=
    (natDegree_mul_le.trans (Nat.add_le_add hl2 hc3)).trans (by omega)
  have h3 : ((y + C (a 4) + C (a 5)) * l a * C (a 3)).natDegree ≤ 6 := by
    have hp := natDegree_mul_le.trans (Nat.add_le_add hb hl)
    exact (natDegree_mul_le.trans (Nat.add_le_add hp (C_le _ 0))).trans (by omega)
  have h4 : (C (a 5) * y + C (a 4) * C (a 5)).natDegree ≤ 6 := by
    exact natDegree_add_le_of_degree_le
      ((natDegree_mul_le.trans (Nat.add_le_add (C_le _ 0) hy)).trans (by omega))
      ((natDegree_mul_le.trans (Nat.add_le_add (C_le _ 0) (C_le _ 0))).trans (by omega))
  have h5 : ((C (a 20) * (X + y + C (a 18))) * (l a) ^ 2).natDegree ≤ 6 := by
    have hp : (C (a 20) * (X + y + C (a 18))).natDegree ≤ 2 :=
      natDegree_mul_le.trans (Nat.add_le_add (C_le (a 20) 0) hxy)
    exact (natDegree_mul_le.trans (Nat.add_le_add hp hl2)).trans (by omega)
  have h6 : (y + C (a 9) + C (a 11) + C (a 13)).natDegree ≤ 6 :=
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le hy (C_le _ _)) (C_le _ _)) (C_le _ _)).trans (by omega)
  exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le h1 h2) h3) h4) h5) h6

theorem peeled_monic (a : ℕ → R) : IsMonicOfDegree (peeled a) 7 :=
  ((z_monic a).mul (cubic_monic a)).add_right ((tail_degree a).trans_lt (by omega))

end FastPoly.Char2Degree23FifteenSlope
