import FastPoly.Examples.Char2Degree25HighPivots

/-! The independent raw-a6 pivot in row eighteen of the existing circuit.
Its degree-four v slope propagates through named w/s/ell/h/j/n gates.
The h branch gives the unique degree-thirteen change in nLeft. -/

namespace FastPoly.Char2Degree25RowEighteen

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift6 (a : ℕ → R) (delta : R) : ℕ → R
  | 6 => a 6 + delta
  | j => a j

noncomputable def vSlope (a : ℕ → R) : R[X] := y + z a + C (a 7)
noncomputable def wLeft (a : ℕ → R) : R[X] := X + y + z a + C (a 8)
noncomputable def sLeft (a : ℕ → R) : R[X] := z a + C (a 10)
noncomputable def ellLeft (a : ℕ → R) : R[X] := X + C (a 16)
noncomputable def wSlope (a : ℕ → R) : R[X] := wLeft a * vSlope a
noncomputable def sSlope (a : ℕ → R) : R[X] := sLeft a * vSlope a
noncomputable def ellSlope (a : ℕ → R) : R[X] := ellLeft a * vSlope a
noncomputable def hSlope (a : ℕ → R) : R[X] := hLeft a * (vSlope a + wSlope a)
noncomputable def jSlope (a : ℕ → R) : R[X] := jLeft a * ellSlope a
noncomputable def leftSlope (a : ℕ → R) : R[X] := sSlope a + ellSlope a + hSlope a + jSlope a
noncomputable def outputSlope (a : ℕ → R) : R[X] := ellSlope a + nRight a * leftSlope a

theorem v_shift6 (a : ℕ → R) (delta : R) :
    v (shift6 a delta) = v a + C delta * vSlope a := by
  change (X + C (a 6 + delta)) * vSlope a = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

private theorem wire_change (l x v c d f : R[X]) :
    l * (x + (v + d * f) + c) = l * (x + v + c) + d * (l * f) := by ring
private theorem wire_change_plain (l v c d f : R[X]) :
    l * ((v + d * f) + c) = l * (v + c) + d * (l * f) := by ring

theorem w_shift6 (a : ℕ → R) (delta : R) :
    w (shift6 a delta) = w a + C delta * wSlope a := by
  change wLeft a * (y + v (shift6 a delta) + C (a 9)) = _
  rw [v_shift6]
  exact wire_change (wLeft a) y (v a) (C (a 9)) (C delta) (vSlope a)

theorem s_shift6 (a : ℕ → R) (delta : R) :
    s (shift6 a delta) = s a + C delta * sSlope a := by
  change sLeft a * (v (shift6 a delta) + C (a 11)) = _
  rw [v_shift6]
  exact wire_change_plain (sLeft a) (v a) (C (a 11)) (C delta) (vSlope a)

theorem ell_shift6 (a : ℕ → R) (delta : R) :
    ell (shift6 a delta) = ell a + C delta * ellSlope a := by
  change ellLeft a * (z a + v (shift6 a delta) + C (a 17)) = _
  rw [v_shift6]
  exact wire_change (ellLeft a) (z a) (v a) (C (a 17)) (C delta) (vSlope a)

private theorem collect_right (x v w r c d f g : R[X]) :
    x + (v + d * f) + (w + d * g) + r + c =
      (x + v + w + r + c) + d * (f + g) := by ring

theorem hRight_shift6 (a : ℕ → R) (delta : R) :
    hRight (shift6 a delta) = hRight a + C delta * (vSlope a + wSlope a) := by
  change X + y + z a + u a + v (shift6 a delta) + w (shift6 a delta) + r a + C (a 19) = _
  rw [v_shift6, w_shift6]
  exact collect_right (X + y + z a + u a) (v a) (w a) (r a) (C (a 19))
    (C delta) (vSlope a) (wSlope a)

private theorem product_right_change (a b d c : R[X]) :
    a * (b + d * c) = a * b + d * (a * c) := by ring

theorem h_shift6 (a : ℕ → R) (delta : R) :
    h (shift6 a delta) = h a + C delta * hSlope a := by
  change hLeft a * hRight (shift6 a delta) = _
  rw [hRight_shift6]
  exact product_right_change (hLeft a) (hRight a) (C delta) (vSlope a + wSlope a)

theorem j_shift6 (a : ℕ → R) (delta : R) :
    j (shift6 a delta) = j a + C delta * jSlope a := by
  change jLeft a * (ell (shift6 a delta) + C (a 21)) = _
  rw [ell_shift6]
  exact wire_change_plain (jLeft a) (ell a) (C (a 21)) (C delta) (ellSlope a)

private theorem collect_left (x s r g ell h j c d f0 f1 f2 f3 : R[X]) :
    x + (s + d * f0) + r + g + (ell + d * f1) + (h + d * f2) + (j + d * f3) + c =
      (x + s + r + g + ell + h + j + c) + d * (f0 + f1 + f2 + f3) := by ring

theorem nLeft_shift6 (a : ℕ → R) (delta : R) :
    nLeft (shift6 a delta) = nLeft a + C delta * leftSlope a := by
  change X + t a + u a + s (shift6 a delta) + r a + g a + ell (shift6 a delta) +
    h (shift6 a delta) + j (shift6 a delta) + C (a 22) = _
  rw [s_shift6, ell_shift6, h_shift6, j_shift6]
  exact collect_left (X + t a + u a) (s a) (r a) (g a) (ell a) (h a) (j a) (C (a 22))
    (C delta) (sSlope a) (ellSlope a) (hSlope a) (jSlope a)

private theorem product_left_change (a b d c : R[X]) :
    (a + d * c) * b = a * b + d * (b * c) := by ring

theorem n_shift6 (a : ℕ → R) (delta : R) :
    n (shift6 a delta) = n a + C delta * (nRight a * leftSlope a) := by
  change nLeft (shift6 a delta) * nRight a = _
  rw [nLeft_shift6]
  exact product_left_change (nLeft a) (nRight a) (C delta) (leftSlope a)

theorem head_shift6 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.head (shift6 a delta) = Char2Degree25Frame.head a + C delta * ellSlope a := by
  change y + z a + u a + ell (shift6 a delta) = _
  rw [ell_shift6, ← add_assoc]
  rfl

private theorem collect_output (h n c d f g : R[X]) :
    (h + d * f) + (n + d * g) + c = (h + n + c) + d * (f + g) := by ring

theorem output_shift6 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift6 a delta) =
      Char2Degree25Frame.output a + C delta * outputSlope a := by
  change Char2Degree25Frame.head (shift6 a delta) + n (shift6 a delta) + C (a 24) = _
  rw [head_shift6, n_shift6]
  exact collect_output (Char2Degree25Frame.head a) (n a) (C (a 24)) (C delta)
    (ellSlope a) (nRight a * leftSlope a)

theorem vSlope_monic (a : ℕ → R) : IsMonicOfDegree (vSlope a) 4 :=
  (y_add_z_monic a).add_right (by rw [natDegree_C]; omega)
theorem wLeft_monic (a : ℕ → R) : IsMonicOfDegree (wLeft a) 4 :=
  ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).add_right
    (by rw [natDegree_C]; omega)
theorem sLeft_monic (a : ℕ → R) : IsMonicOfDegree (sLeft a) 4 :=
  (z_monic a).add_right (by rw [natDegree_C]; omega)
theorem ellLeft_monic (a : ℕ → R) : IsMonicOfDegree (ellLeft a) 1 :=
  isMonicOfDegree_X_add_one (a 16)
theorem wSlope_monic (a : ℕ → R) : IsMonicOfDegree (wSlope a) 8 :=
  (wLeft_monic a).mul (vSlope_monic a)
theorem sSlope_monic (a : ℕ → R) : IsMonicOfDegree (sSlope a) 8 :=
  (sLeft_monic a).mul (vSlope_monic a)
theorem ellSlope_monic (a : ℕ → R) : IsMonicOfDegree (ellSlope a) 5 :=
  (ellLeft_monic a).mul (vSlope_monic a)
theorem hSlope_monic (a : ℕ → R) : IsMonicOfDegree (hSlope a) 13 :=
  (hLeft_monic a).mul ((wSlope_monic a).add_left
    ((vSlope_monic a).natDegree_eq.trans_lt (by omega)))
theorem jSlope_monic (a : ℕ → R) : IsMonicOfDegree (jSlope a) 10 :=
  (jLeft_monic a).mul (ellSlope_monic a)
theorem leftSlope_monic (a : ℕ → R) : IsMonicOfDegree (leftSlope a) 13 :=
  ((hSlope_monic a).add_left
    (((sSlope_monic a).add_right ((ellSlope_monic a).natDegree_eq.trans_lt
      (by omega))).natDegree_eq.trans_lt (by omega))).add_right
        ((jSlope_monic a).natDegree_eq.trans_lt (by omega))
theorem outputSlope_monic (a : ℕ → R) : IsMonicOfDegree (outputSlope a) 18 :=
  ((nRight_monic a).mul (leftSlope_monic a)).add_left
    ((ellSlope_monic a).natDegree_eq.trans_lt (by omega))

theorem shift6_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift6 a delta)) 18 delta := by
  apply unit_difference_of_split (Char2Degree25Frame.output a)
    (Char2Degree25Frame.output (shift6 a delta)) (outputSlope a) 18 delta 0
    (by omega) (outputSlope_monic a)
  rw [map_zero, add_zero, output_shift6]

end FastPoly.Char2Degree25RowEighteen

