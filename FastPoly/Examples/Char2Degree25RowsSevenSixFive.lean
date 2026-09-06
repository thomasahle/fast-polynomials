import FastPoly.Examples.Char2Degree25Frame
import FastPoly.Examples.Char2Degree19InnerTail

/-! Three raw unit pivots in the supplied degree-25 ordering.
The row-seven g/h slopes cancel to a quadratic, the row-six j/h/s slopes
cancel to a linear polynomial, and row five is the final-factor offset.
These are exact raw changes, not normalized completeness claims. -/
namespace FastPoly.Char2Degree25RowsSevenSixFive

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift7 (a : ℕ → R) (delta : R) : ℕ → R
  | 15 => a 15 + delta
  | 19 => a 19 + delta
  | i => a i

def shift6 (a : ℕ → R) (delta : R) : ℕ → R
  | 11 => a 11 + delta
  | 19 => a 19 + delta
  | 21 => a 21 + delta
  | i => a i

def shift5 (a : ℕ → R) (delta : R) : ℕ → R
  | 22 => a 22 + delta
  | i => a i

noncomputable def gLeft (a : ℕ → R) : R[X] := z a + t a + C (a 14)
noncomputable def sLeft (a : ℕ → R) : R[X] := z a + C (a 10)
noncomputable def factor7 (a : ℕ → R) : R[X] := y + C (a 18 + a 14)
noncomputable def factor6 (a : ℕ → R) : R[X] := X + C (a 20 + a 18 + a 10)
noncomputable def slope7 (a : ℕ → R) : R[X] := nRight a * factor7 a
noncomputable def slope6 (a : ℕ → R) : R[X] := nRight a * factor6 a

theorem g_shift7 (a : ℕ → R) (delta : R) :
    g (shift7 a delta) = g a + C delta * gLeft a := by
  change gLeft a * (X + u a + C (a 15 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (gLeft a) (C delta)]
  rfl

theorem h_shift7 (a : ℕ → R) (delta : R) :
    h (shift7 a delta) = h a + C delta * hLeft a := by
  change hLeft a * (X + y + z a + u a + v a + w a + r a + C (a 19 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (hLeft a) (C delta)]
  rfl

theorem h_shift6 (a : ℕ → R) (delta : R) :
    h (shift6 a delta) = h a + C delta * hLeft a := by
  change hLeft a * (X + y + z a + u a + v a + w a + r a + C (a 19 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (hLeft a) (C delta)]
  rfl

theorem s_shift6 (a : ℕ → R) (delta : R) :
    s (shift6 a delta) = s a + C delta * sLeft a := by
  change sLeft a * (v a + C (a 11 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (sLeft a) (C delta)]
  rfl

theorem j_shift6 (a : ℕ → R) (delta : R) :
    j (shift6 a delta) = j a + C delta * jLeft a := by
  change jLeft a * (ell a + C (a 21 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (jLeft a) (C delta)]
  rfl

private theorem quadratic_cancel (y z t a b : R[X]) :
    (z + t + a) + (y + z + t + b) = y + (b + a) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem factor7_eq (a : ℕ → R) : gLeft a + hLeft a = factor7 a := by
  change (z a + t a + C (a 14)) + (y + z a + t a + C (a 18)) = _
  rw [factor7, map_add]
  exact quadratic_cancel _ _ _ _ _

private theorem linear_cancel (x y z t a b c : R[X]) :
    (z + c) + (y + z + t + b) + (x + y + t + a) = x + ((a + b) + c) := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem factor6_eq (a : ℕ → R) : sLeft a + hLeft a + jLeft a = factor6 a := by
  change (z a + C (a 10)) + (y + z a + t a + C (a 18)) +
    (X + y + t a + C (a 20)) = _
  rw [factor6, map_add, map_add]
  exact linear_cancel _ _ _ _ _ _ _

private theorem collect_two (x g ell h j c d gs hs : R[X]) :
    x + (g + d * gs) + ell + (h + d * hs) + j + c =
      (x + g + ell + h + j + c) + d * (gs + hs) := by ring

theorem nLeft_shift7 (a : ℕ → R) (delta : R) :
    nLeft (shift7 a delta) = nLeft a + C delta * factor7 a := by
  change X + t a + u a + s a + r a + g (shift7 a delta) + ell a +
    h (shift7 a delta) + j a + C (a 22) = _
  rw [g_shift7, h_shift7, collect_two, factor7_eq]
  rfl

private theorem collect_three (x s r g ell h j c d ss hs js : R[X]) :
    x + (s + d * ss) + r + g + ell + (h + d * hs) + (j + d * js) + c =
      (x + s + r + g + ell + h + j + c) + d * (ss + hs + js) := by ring

theorem nLeft_shift6 (a : ℕ → R) (delta : R) :
    nLeft (shift6 a delta) = nLeft a + C delta * factor6 a := by
  change X + t a + u a + s (shift6 a delta) + r a + g a + ell a +
    h (shift6 a delta) + j (shift6 a delta) + C (a 22) = _
  rw [s_shift6, h_shift6, j_shift6, collect_three, factor6_eq]
  rfl

theorem nLeft_shift5 (a : ℕ → R) (delta : R) :
    nLeft (shift5 a delta) = nLeft a + C delta := by
  change X + t a + u a + s a + r a + g a + ell a + h a + j a + C (a 22 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

private theorem collect_output (head nl nr c d f : R[X]) :
    head + (nl + d * f) * nr + c =
      (head + nl * nr + c) + d * (nr * f) := by ring

private theorem collect_constant (head nl nr c d : R[X]) :
    head + (nl + d) * nr + c = (head + nl * nr + c) + d * nr := by ring

theorem output_shift7 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift7 a delta) =
      Char2Degree25Frame.output a + C delta * slope7 a := by
  change Char2Degree25Frame.head a + nLeft (shift7 a delta) * nRight a + C (a 24) = _
  rw [nLeft_shift7]
  exact collect_output _ _ _ _ _ _

theorem output_shift6 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift6 a delta) =
      Char2Degree25Frame.output a + C delta * slope6 a := by
  change Char2Degree25Frame.head a + nLeft (shift6 a delta) * nRight a + C (a 24) = _
  rw [nLeft_shift6]
  exact collect_output _ _ _ _ _ _

theorem output_shift5 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift5 a delta) =
      Char2Degree25Frame.output a + C delta * nRight a := by
  change Char2Degree25Frame.head a + nLeft (shift5 a delta) * nRight a + C (a 24) = _
  rw [nLeft_shift5]
  exact collect_constant _ _ _ _ _

theorem factor7_monic (a : ℕ → R) : IsMonicOfDegree (factor7 a) 2 :=
  y_monic.add_right (by rw [natDegree_C]; omega)

theorem factor6_monic (a : ℕ → R) : IsMonicOfDegree (factor6 a) 1 :=
  isMonicOfDegree_X_add_one _

theorem slope7_monic (a : ℕ → R) : IsMonicOfDegree (slope7 a) 7 :=
  (nRight_monic a).mul (factor7_monic a)

theorem slope6_monic (a : ℕ → R) : IsMonicOfDegree (slope6 a) 6 :=
  (nRight_monic a).mul (factor6_monic a)

theorem shift7_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift7 a delta)) 7 delta := by
  apply unit_difference_of_split _ _ (slope7 a) 7 delta 0 (by omega) (slope7_monic a)
  simpa only [map_zero, add_zero] using output_shift7 a delta

theorem shift6_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift6 a delta)) 6 delta := by
  apply unit_difference_of_split _ _ (slope6 a) 6 delta 0 (by omega) (slope6_monic a)
  simpa only [map_zero, add_zero] using output_shift6 a delta

theorem shift5_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift5 a delta)) 5 delta := by
  apply unit_difference_of_split _ _ (nRight a) 5 delta 0 (by omega) (nRight_monic a)
  simpa only [map_zero, add_zero] using output_shift5 a delta

end FastPoly.Char2Degree25RowsSevenSixFive
