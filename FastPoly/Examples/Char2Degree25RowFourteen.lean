import FastPoly.Examples.Char2Degree25RowFifteen

/-! The supplied raw a9 pivot: the column is nRight*hLeft*wLeft. -/

namespace FastPoly.Char2Degree25RowFourteen

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23Cancellations Char2Degree23MiddleFrame Char2Degree25Frame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift (a : ℕ → R) (d : R) : ℕ → R
  | 9 => a 9 + d
  | i => a i

noncomputable def slope (a : ℕ → R) : R[X] := nRight a * (hLeft a * wLeft a)

theorem w_change (a : ℕ → R) (d : R) : w (shift a d) = w a + C d * wLeft a := by
  change wLeft a * (y + v a + C (a 9 + d)) = _
  rw [add_constant, mul_add, mul_comm _ (C d)]
  rfl

private theorem shift_one (p w r c d s : R[X]) :
    p + (w + d * s) + r + c = (p + w + r + c) + d * s := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem hRight_change (a : ℕ → R) (d : R) : hRight (shift a d) = hRight a + C d * wLeft a := by
  change (X + y + z a + u a + v a) + w (shift a d) + r a + C (a 19) = _
  rw [w_change]
  exact shift_one _ _ _ _ _ _

private theorem product_right (p q d s : R[X]) : p * (q + d * s) = p * q + d * (p * s) := by ring

theorem h_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.h (shift a d) = Char2Degree25Frame.h a + C d * (hLeft a * wLeft a) := by
  change hLeft a * hRight (shift a d) = _
  rw [hRight_change]
  exact product_right _ _ _ _

theorem nLeft_change (a : ℕ → R) (d : R) :
    nLeft (shift a d) = nLeft a + C d * (hLeft a * wLeft a) := by
  change (X + t a + u a + s a + r a + g a + ell a) +
    Char2Degree25Frame.h (shift a d) + j a + C (a 22) = _
  rw [h_change]
  exact shift_one _ _ _ _ _ _

private theorem product_left (p q d s : R[X]) : (p + d * s) * q = p * q + d * (q * s) := by ring

theorem n_change (a : ℕ → R) (d : R) : n (shift a d) = n a + C d * slope a := by
  change nLeft (shift a d) * nRight a = _
  rw [nLeft_change]
  exact product_left _ _ _ _

private theorem output_transport (p n c d s : R[X]) :
    p + (n + d * s) + c = (p + n + c) + d * s := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem output_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift a d) = Char2Degree25Frame.output a + C d * slope a := by
  change Char2Degree25Frame.head a + n (shift a d) + C (a 24) = _
  rw [n_change]
  exact output_transport _ _ _ _ _

theorem slope_monic (a : ℕ → R) : IsMonicOfDegree (slope a) 14 :=
  (nRight_monic a).mul ((hLeft_monic a).mul (wLeft_monic a))

theorem unit (a : ℕ → R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift a d)) 14 d := by
  rw [output_change]
  exact Char2Degree21Frame.difference_scaled d (slope_monic a)

end FastPoly.Char2Degree25RowFourteen
