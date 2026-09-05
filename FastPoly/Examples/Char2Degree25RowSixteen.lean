import FastPoly.Examples.Char2Degree25HighFrame
import FastPoly.Examples.Char2Degree19InnerTail

/-! The existing degree-25 raw row-sixteen pivot, simultaneously translating
a12 and a23. The final two-factor difference is exact; its degree-sixteen
leading term comes from the explicit linear cancellation rLeft+nRight.
This is one raw pivot, not a claim of a full normalized decoder. -/
namespace FastPoly.Char2Degree25RowSixteen

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift (a : ℕ → R) (delta : R) : ℕ → R
  | 12 => a 12 + delta
  | 23 => a 23 + delta
  | i => a i

theorem z_shift (a : ℕ → R) (delta : R) : z (shift a delta) = z a := rfl
theorem t_shift (a : ℕ → R) (delta : R) : t (shift a delta) = t a := rfl
theorem u_shift (a : ℕ → R) (delta : R) : u (shift a delta) = u a := rfl
theorem v_shift (a : ℕ → R) (delta : R) : v (shift a delta) = v a := rfl
theorem w_shift (a : ℕ → R) (delta : R) : w (shift a delta) = w a := rfl
theorem s_shift (a : ℕ → R) (delta : R) : s (shift a delta) = s a := rfl
theorem g_shift (a : ℕ → R) (delta : R) : g (shift a delta) = g a := rfl
theorem ell_shift (a : ℕ → R) (delta : R) : ell (shift a delta) = ell a := rfl
theorem j_shift (a : ℕ → R) (delta : R) : j (shift a delta) = j a := rfl
theorem hLeft_shift (a : ℕ → R) (delta : R) : hLeft (shift a delta) = hLeft a := rfl
theorem head_shift (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.head (shift a delta) = Char2Degree25Frame.head a := rfl

noncomputable def U (a : ℕ → R) : R[X] := u a + C (a 13)
noncomputable def M (a : ℕ → R) : R[X] := (1 + hLeft a) * U a
noncomputable def linear (a : ℕ → R) (delta : R) : R[X] := X + C (a 12 + a 23 + delta)
noncomputable def right (a : ℕ → R) (delta : R) : R[X] := nRight a + C delta
noncomputable def slope (a : ℕ → R) (delta : R) : R[X] := nLeft a + right a delta * M a
noncomputable def lower (a : ℕ → R) (delta : R) : R[X] :=
  hLeft a * hTail a + small a + right a delta * u a +
    right a delta * (1 + hLeft a) * C (a 13)

theorem r_shift (a : ℕ → R) (delta : R) :
    r (shift a delta) = r a + C delta * U a := by
  change (X + t a + C (a 12 + delta)) * (u a + C (a 13)) = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem hRight_shift (a : ℕ → R) (delta : R) :
    hRight (shift a delta) = hRight a + C delta * U a := by
  change X + y + z (shift a delta) + u (shift a delta) + v (shift a delta) +
    w (shift a delta) + r (shift a delta) + C (a 19) = _
  rw [z_shift, u_shift, v_shift, w_shift, r_shift]
  change X + y + z a + u a + v a + w a + (r a + C delta * U a) + C (a 19) = _
  unfold hRight
  ac_rfl

theorem h_shift (a : ℕ → R) (delta : R) :
    h (shift a delta) = h a + C delta * (hLeft a * U a) := by
  rw [h, hLeft_shift, hRight_shift, mul_add]
  change h a + hLeft a * (C delta * U a) = _
  rw [mul_left_comm]

private theorem collect_left (base r g ell h j c d u hl : R[X]) :
    base + (r + d * u) + g + ell + (h + d * (hl * u)) + j + c =
      (base + r + g + ell + h + j + c) + d * ((1 + hl) * u) := by ring

theorem nLeft_shift (a : ℕ → R) (delta : R) :
    nLeft (shift a delta) = nLeft a + C delta * M a := by
  unfold nLeft
  rw [t_shift, u_shift, s_shift, r_shift, g_shift, ell_shift, h_shift, j_shift]
  change X + t a + u a + s a + (r a + C delta * U a) +
      g a + ell a + (h a + C delta * (hLeft a * U a)) + j a + C (a 22) =
    (X + t a + u a + s a + r a + g a + ell a + h a + j a + C (a 22)) + C delta * M a
  exact collect_left (X + t a + u a + s a) (r a) (g a) (ell a) (h a)
    (j a) (C (a 22)) (C delta) (U a) (hLeft a)

theorem nRight_shift (a : ℕ → R) (delta : R) :
    nRight (shift a delta) = nRight a + C delta := by
  change t a + C (a 23 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

private theorem final_product (l r m d : R[X]) :
    (l + d * m) * (r + d) = l * r + d * (l + (r + d) * m) := by ring

theorem n_shift (a : ℕ → R) (delta : R) :
    n (shift a delta) = n a + C delta * slope a delta := by
  rw [n, nLeft_shift, nRight_shift, final_product]
  rfl

theorem output_shift (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift a delta) =
      Char2Degree25Frame.output a + C delta * slope a delta := by
  change Char2Degree25Frame.head (shift a delta) + n (shift a delta) + C (a 24) = _
  rw [head_shift, n_shift]
  change Char2Degree25Frame.head a + (n a + C delta * slope a delta) + C (a 24) = _
  unfold Char2Degree25Frame.output
  ac_rfl

theorem linear_cancel (a : ℕ → R) (delta : R) :
    rLeft a + right a delta = linear a delta := by
  change (X + t a + C (a 12)) + ((t a + C (a 23)) + C delta) = X + C (a 12 + a 23 + delta)
  simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

private theorem slope_collect (hl rl u ht sm nr c : R[X]) :
    (hl * (rl * u) + hl * ht + sm) + nr * ((1 + hl) * (u + c)) =
      hl * u * (rl + nr) + (hl * ht + sm + nr * u + nr * (1 + hl) * c) := by ring

theorem slope_split (a : ℕ → R) (delta : R) :
    slope a delta = hLeft a * u a * linear a delta + lower a delta := by
  change nLeft a + right a delta * ((1 + hLeft a) * (u a + C (a 13))) = _
  rw [nLeft_split, h_split, slope_collect, linear_cancel]
  rfl

private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem right_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (right a delta) 5 :=
  (nRight_monic a).add_right (C_lt _ _ (by omega))

theorem one_hLeft_monic (a : ℕ → R) : IsMonicOfDegree (1 + hLeft a) 5 :=
  (hLeft_monic a).add_left (by rw [natDegree_one]; omega)

theorem lower_degree (a : ℕ → R) (delta : R) : (lower a delta).natDegree ≤ 15 := by
  have hh : (hLeft a * hTail a).natDegree ≤ 15 :=
    ((hLeft_monic a).mul (hTail_monic a)).natDegree_eq.le
  have hs : (small a).natDegree ≤ 15 := (small_degree a).trans (by omega)
  have hu : (right a delta * u a).natDegree ≤ 15 :=
    ((right_monic a delta).mul (u_monic a)).natDegree_eq.le
  have hc : (right a delta * (1 + hLeft a) * C (a 13)).natDegree ≤ 15 := by
    apply natDegree_mul_le.trans
    rw [((right_monic a delta).mul (one_hLeft_monic a)).natDegree_eq, natDegree_C]
    omega
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le hh hs) hu) hc

theorem slope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (slope a delta) 16 := by
  have hl : IsMonicOfDegree (linear a delta) 1 := isMonicOfDegree_X_add_one _
  have hh : IsMonicOfDegree (hLeft a * u a * linear a delta) 16 :=
    ((hLeft_monic a).mul (u_monic a)).mul hl
  rw [slope_split]
  exact hh.add_right ((lower_degree a delta).trans_lt (by omega))

/-- The actual raw paired increment has unit slope in row sixteen and
preserves every higher coefficient. -/
theorem shift_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift a delta)) 16 delta := by
  apply unit_difference_of_split _ _ (slope a delta) 16 delta 0 (by omega)
    (slope_monic a delta)
  simpa only [map_zero, add_zero] using output_shift a delta

end FastPoly.Char2Degree25RowSixteen
