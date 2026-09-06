import FastPoly.Examples.Char2Degree25Frame
import FastPoly.Examples.Char2Degree19InnerTail

/-! Two literal affine raw pivots of the existing degree-25 circuit.
Only the s gate and final n product change. The a10 slope includes its
unchanged a11 offset, so these are exact output identities, not just
leading-row approximations. -/
namespace FastPoly.Char2Degree25RowsTenNine

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift10 (a : ℕ → R) (delta : R) : ℕ → R
  | 10 => a 10 + delta
  | i => a i

def shift11 (a : ℕ → R) (delta : R) : ℕ → R
  | 11 => a 11 + delta
  | i => a i

noncomputable def sLeft (a : ℕ → R) : R[X] := z a + C (a 10)
noncomputable def sRight (a : ℕ → R) : R[X] := v a + C (a 11)
noncomputable def slope10 (a : ℕ → R) : R[X] := nRight a * sRight a
noncomputable def slope9 (a : ℕ → R) : R[X] := nRight a * sLeft a

theorem s_shift10 (a : ℕ → R) (delta : R) :
    s (shift10 a delta) = s a + C delta * sRight a := by
  change (z a + C (a 10 + delta)) * sRight a = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem s_shift11 (a : ℕ → R) (delta : R) :
    s (shift11 a delta) = s a + C delta * sLeft a := by
  change sLeft a * (v a + C (a 11 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (sLeft a) (C delta)]
  rfl

private theorem collect_left (x s r g ell h j c d f : R[X]) :
    x + (s + d * f) + r + g + ell + h + j + c =
      (x + s + r + g + ell + h + j + c) + d * f := by ring

theorem nLeft_shift10 (a : ℕ → R) (delta : R) :
    nLeft (shift10 a delta) = nLeft a + C delta * sRight a := by
  change X + t a + u a + s (shift10 a delta) + r a + g a +
    ell a + h a + j a + C (a 22) = _
  rw [s_shift10]
  exact collect_left _ _ _ _ _ _ _ _ _ _

theorem nLeft_shift11 (a : ℕ → R) (delta : R) :
    nLeft (shift11 a delta) = nLeft a + C delta * sLeft a := by
  change X + t a + u a + s (shift11 a delta) + r a + g a +
    ell a + h a + j a + C (a 22) = _
  rw [s_shift11]
  exact collect_left _ _ _ _ _ _ _ _ _ _

private theorem collect_output (head nl nr c d f : R[X]) :
    head + (nl + d * f) * nr + c =
      (head + nl * nr + c) + d * (nr * f) := by ring

theorem output_shift10 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift10 a delta) =
      Char2Degree25Frame.output a + C delta * slope10 a := by
  change Char2Degree25Frame.head a + nLeft (shift10 a delta) * nRight a + C (a 24) = _
  rw [nLeft_shift10]
  exact collect_output _ _ _ _ _ _

theorem output_shift11 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift11 a delta) =
      Char2Degree25Frame.output a + C delta * slope9 a := by
  change Char2Degree25Frame.head a + nLeft (shift11 a delta) * nRight a + C (a 24) = _
  rw [nLeft_shift11]
  exact collect_output _ _ _ _ _ _

private theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem slope10_monic (a : ℕ → R) : IsMonicOfDegree (slope10 a) 10 :=
  (nRight_monic a).mul ((v_monic a).add_right (C_lt _ _ (by omega)))

theorem slope9_monic (a : ℕ → R) : IsMonicOfDegree (slope9 a) 9 :=
  (nRight_monic a).mul ((z_monic a).add_right (C_lt _ _ (by omega)))

theorem shift10_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift10 a delta)) 10 delta := by
  apply unit_difference_of_split _ _ (slope10 a) 10 delta 0 (by omega) (slope10_monic a)
  simpa only [map_zero, add_zero] using output_shift10 a delta

theorem shift11_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift11 a delta)) 9 delta := by
  apply unit_difference_of_split _ _ (slope9 a) 9 delta 0 (by omega) (slope9_monic a)
  simpa only [map_zero, add_zero] using output_shift11 a delta

end FastPoly.Char2Degree25RowsTenNine
