import FastPoly.Examples.Char2Degree25HighFrame
import FastPoly.Examples.Char2Degree23MiddleFrame

/-! The supplied raw a7 pivot: its named affine slope is monic of degree15. -/

namespace FastPoly.Char2Degree25RowFifteen

open Polynomial Char2Decoder Char2Degree23RowEight Char2Degree23Frame
  Char2Degree23Cancellations Char2Degree23MiddleFrame Char2Degree25Frame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift (a : ℕ → R) (d : R) : ℕ → R
  | 7 => a 7 + d
  | i => a i

noncomputable def vSlope (a : ℕ → R) : R[X] := X + C (a 6)
noncomputable def wSlope (a : ℕ → R) : R[X] := wLeft a * vSlope a
noncomputable def sSlope (a : ℕ → R) : R[X] := (z a + C (a 10)) * vSlope a
noncomputable def ellSlope (a : ℕ → R) : R[X] := ellLinear a * vSlope a
noncomputable def hSlope (a : ℕ → R) : R[X] := hLeft a * (vSlope a + wSlope a)
noncomputable def jSlope (a : ℕ → R) : R[X] := jLeft a * ellSlope a
noncomputable def innerSlope (a : ℕ → R) : R[X] := sSlope a + ellSlope a + hSlope a + jSlope a
noncomputable def slope (a : ℕ → R) : R[X] := nRight a * innerSlope a + ellSlope a

theorem v_change (a : ℕ → R) (d : R) : v (shift a d) = v a + C d * vSlope a :=
  v_offset7 a d

private theorem shift_one (x v c d s : R[X]) :
    x + (v + d * s) + c = (x + v + c) + d * s := by
  simp only [add_assoc, add_comm, add_left_comm]

private theorem product_right (p q d s : R[X]) : p * (q + d * s) = p * q + d * (p * s) := by ring

theorem w_change (a : ℕ → R) (d : R) : w (shift a d) = w a + C d * wSlope a := by
  change wLeft a * (y + v (shift a d) + C (a 9)) = _
  rw [v_change, shift_one]
  exact product_right _ _ _ _

theorem s_change (a : ℕ → R) (d : R) : s (shift a d) = s a + C d * sSlope a := by
  change (z a + C (a 10)) * (v (shift a d) + C (a 11)) = _
  rw [v_change, add_right_comm (v a) (C d * vSlope a) (C (a 11))]
  exact product_right _ _ _ _

theorem ell_change (a : ℕ → R) (d : R) : ell (shift a d) = ell a + C d * ellSlope a := by
  change ellLinear a * (z a + v (shift a d) + C (a 17)) = _
  rw [v_change, shift_one]
  exact product_right _ _ _ _

private theorem shift_pair (p v w r c d s t : R[X]) :
    p + (v + d * s) + (w + d * t) + r + c = (p + v + w + r + c) + d * (s + t) := by ring

theorem hRight_change (a : ℕ → R) (d : R) :
    hRight (shift a d) = hRight a + C d * (vSlope a + wSlope a) := by
  change (X + y + z a + u a) + v (shift a d) + w (shift a d) + r a + C (a 19) = _
  rw [v_change, w_change]
  exact shift_pair _ _ _ _ _ _ _ _

theorem h_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.h (shift a d) = Char2Degree25Frame.h a + C d * hSlope a := by
  change hLeft a * hRight (shift a d) = _
  rw [hRight_change]
  exact product_right _ _ _ _

theorem j_change (a : ℕ → R) (d : R) : j (shift a d) = j a + C d * jSlope a := by
  change jLeft a * (ell (shift a d) + C (a 21)) = _
  rw [ell_change, add_right_comm (ell a) (C d * ellSlope a) (C (a 21))]
  exact product_right _ _ _ _

private theorem shift_four (p s r g e h j c d ds de dh dj : R[X]) :
    p + (s + d * ds) + r + g + (e + d * de) + (h + d * dh) + (j + d * dj) + c =
      (p + s + r + g + e + h + j + c) + d * (ds + de + dh + dj) := by ring

theorem nLeft_change (a : ℕ → R) (d : R) : nLeft (shift a d) = nLeft a + C d * innerSlope a := by
  change (X + t a + u a) + s (shift a d) + r a + g a + ell (shift a d) +
    Char2Degree25Frame.h (shift a d) + j (shift a d) + C (a 22) = _
  rw [s_change, ell_change, h_change, j_change]
  exact shift_four _ _ _ _ _ _ _ _ _ _ _ _ _

private theorem product_left (p q d s : R[X]) : (p + d * s) * q = p * q + d * (q * s) := by ring

theorem n_change (a : ℕ → R) (d : R) : n (shift a d) = n a + C d * (nRight a * innerSlope a) := by
  change nLeft (shift a d) * nRight a = _
  rw [nLeft_change]
  exact product_left _ _ _ _

private theorem output_transport (p e n c d s t : R[X]) :
    (p + (e + d * s)) + (n + d * t) + c = (p + e + n + c) + d * (t + s) := by ring

theorem output_change (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift a d) = Char2Degree25Frame.output a + C d * slope a := by
  change ((y + z a + u a) + ell (shift a d)) + n (shift a d) + C (a 24) = _
  rw [ell_change, n_change]
  exact output_transport _ _ _ _ _ _ _

theorem vSlope_monic (a : ℕ → R) : IsMonicOfDegree (vSlope a) 1 :=
  isMonicOfDegree_X_add_one (a 6)

theorem wSlope_monic (a : ℕ → R) : IsMonicOfDegree (wSlope a) 5 :=
  (wLeft_monic a).mul (vSlope_monic a)

theorem sSlope_monic (a : ℕ → R) : IsMonicOfDegree (sSlope a) 5 := by
  have hc : (C (a 10)).natDegree < 4 := by rw [natDegree_C]; omega
  exact ((z_monic a).add_right hc).mul (vSlope_monic a)

theorem ellSlope_monic (a : ℕ → R) : IsMonicOfDegree (ellSlope a) 2 :=
  (isMonicOfDegree_X_add_one (a 16)).mul (vSlope_monic a)

theorem hSlope_monic (a : ℕ → R) : IsMonicOfDegree (hSlope a) 10 :=
  (hLeft_monic a).mul ((wSlope_monic a).add_left ((vSlope_monic a).natDegree_eq.trans_lt (by omega)))

theorem jSlope_monic (a : ℕ → R) : IsMonicOfDegree (jSlope a) 7 :=
  (jLeft_monic a).mul (ellSlope_monic a)

theorem innerSlope_monic (a : ℕ → R) : IsMonicOfDegree (innerSlope a) 10 := by
  have hl : (sSlope a + ellSlope a).natDegree < 10 :=
    ((sSlope_monic a).add_right ((ellSlope_monic a).natDegree_eq.trans_lt (by omega))).natDegree_eq.trans_lt
      (by omega)
  exact ((hSlope_monic a).add_left hl).add_right ((jSlope_monic a).natDegree_eq.trans_lt (by omega))

theorem slope_monic (a : ℕ → R) : IsMonicOfDegree (slope a) 15 :=
  ((nRight_monic a).mul (innerSlope_monic a)).add_right ((ellSlope_monic a).natDegree_eq.trans_lt (by omega))

theorem unit (a : ℕ → R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift a d)) 15 d := by
  rw [output_change]
  exact Char2Degree21Frame.difference_scaled d (slope_monic a)

end FastPoly.Char2Degree25RowFifteen
