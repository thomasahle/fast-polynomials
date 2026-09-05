import FastPoly.Examples.Char2Degree25SeamFrame

/-! The supplied paired a5/a4 raw pivot in row seventeen.
The two quintic u factors change together, leaving a monic quadratic slope.
The remaining proof propagates this exact named change through r/g/h/n. -/

namespace FastPoly.Char2Degree25RowSeventeen

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift7 (a : ℕ → R) (delta : R) : ℕ → R
  | 4 => a 4 + delta
  | 5 => a 5 + delta
  | j => a j

noncomputable def uSlope (a : ℕ → R) (delta : R) : R[X] := y + C (a 4 + a 5 + delta)
noncomputable def rSlope (a : ℕ → R) (delta : R) : R[X] := rLeft a * uSlope a delta
noncomputable def gSlope (a : ℕ → R) (delta : R) : R[X] :=
  Char2Degree25SeamFrame.seamGLeft a * uSlope a delta
noncomputable def hSlope (a : ℕ → R) (delta : R) : R[X] :=
  hLeft a * (uSlope a delta + rSlope a delta)
noncomputable def leftSlope (a : ℕ → R) (delta : R) : R[X] :=
  uSlope a delta + rSlope a delta + gSlope a delta + hSlope a delta
noncomputable def outputSlope (a : ℕ → R) (delta : R) : R[X] :=
  uSlope a delta + nRight a * leftSlope a delta

private theorem paired_u (y z t a b d : R[X]) :
    (y + z + t + (a + d)) * (z + t + (b + d)) =
      (y + z + t + a) * (z + t + b) + d * (y + (a + b + d)) := by
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem u_shift7 (a : ℕ → R) (delta : R) :
    u (shift7 a delta) = u a + C delta * uSlope a delta := by
  change (y + z a + t a + C (a 4 + delta)) * (z a + t a + C (a 5 + delta)) = _
  unfold u uSlope
  simp only [map_add]
  exact paired_u y (z a) (t a) (C (a 4)) (C (a 5)) (C delta)

private theorem plain_change (l u c d f : R[X]) :
    l * ((u + d * f) + c) = l * (u + c) + d * (l * f) := by ring

theorem r_shift7 (a : ℕ → R) (delta : R) :
    r (shift7 a delta) = r a + C delta * rSlope a delta := by
  change rLeft a * (u (shift7 a delta) + C (a 13)) = _
  rw [u_shift7]
  exact plain_change (rLeft a) (u a) (C (a 13)) (C delta) (uSlope a delta)

private theorem middle_change (l x u c d f : R[X]) :
    l * (x + (u + d * f) + c) = l * (x + u + c) + d * (l * f) := by ring

theorem g_shift7 (a : ℕ → R) (delta : R) :
    g (shift7 a delta) = g a + C delta * gSlope a delta := by
  change Char2Degree25SeamFrame.seamGLeft a * (X + u (shift7 a delta) + C (a 15)) = _
  rw [u_shift7]
  exact middle_change (Char2Degree25SeamFrame.seamGLeft a) X (u a)
    (C (a 15)) (C delta) (uSlope a delta)

private theorem collect_right (x u v w r c d f g : R[X]) :
    x + (u + d * f) + v + w + (r + d * g) + c =
      (x + u + v + w + r + c) + d * (f + g) := by ring

theorem hRight_shift7 (a : ℕ → R) (delta : R) :
    hRight (shift7 a delta) = hRight a + C delta * (uSlope a delta + rSlope a delta) := by
  change X + y + z a + u (shift7 a delta) + v a + w a + r (shift7 a delta) + C (a 19) = _
  rw [u_shift7, r_shift7]
  exact collect_right (X + y + z a) (u a) (v a) (w a) (r a) (C (a 19))
    (C delta) (uSlope a delta) (rSlope a delta)

private theorem product_right_change (a b d c : R[X]) :
    a * (b + d * c) = a * b + d * (a * c) := by ring

theorem h_shift7 (a : ℕ → R) (delta : R) :
    h (shift7 a delta) = h a + C delta * hSlope a delta := by
  change hLeft a * hRight (shift7 a delta) = _
  rw [hRight_shift7]
  exact product_right_change (hLeft a) (hRight a) (C delta) (uSlope a delta + rSlope a delta)

private theorem collect_left (x u s r g ell h j c d f0 f1 f2 f3 : R[X]) :
    x + (u + d * f0) + s + (r + d * f1) + (g + d * f2) + ell + (h + d * f3) + j + c =
      (x + u + s + r + g + ell + h + j + c) + d * (f0 + f1 + f2 + f3) := by ring

theorem nLeft_shift7 (a : ℕ → R) (delta : R) :
    nLeft (shift7 a delta) = nLeft a + C delta * leftSlope a delta := by
  change X + t a + u (shift7 a delta) + s a + r (shift7 a delta) +
    g (shift7 a delta) + ell a + h (shift7 a delta) + j a + C (a 22) = _
  rw [u_shift7, r_shift7, g_shift7, h_shift7]
  exact collect_left (X + t a) (u a) (s a) (r a) (g a) (ell a) (h a) (j a)
    (C (a 22)) (C delta) (uSlope a delta) (rSlope a delta) (gSlope a delta) (hSlope a delta)

private theorem product_left_change (a b d c : R[X]) :
    (a + d * c) * b = a * b + d * (b * c) := by ring

theorem n_shift7 (a : ℕ → R) (delta : R) :
    n (shift7 a delta) = n a + C delta * (nRight a * leftSlope a delta) := by
  change nLeft (shift7 a delta) * nRight a = _
  rw [nLeft_shift7]
  exact product_left_change (nLeft a) (nRight a) (C delta) (leftSlope a delta)

private theorem collect_head (x u e d f : R[X]) :
    x + (u + d * f) + e = (x + u + e) + d * f := by ac_rfl

theorem head_shift7 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.head (shift7 a delta) =
      Char2Degree25Frame.head a + C delta * uSlope a delta := by
  change y + z a + u (shift7 a delta) + ell a = _
  rw [u_shift7]
  exact collect_head (y + z a) (u a) (ell a) (C delta) (uSlope a delta)

private theorem collect_output (h n c d f g : R[X]) :
    (h + d * f) + (n + d * g) + c = (h + n + c) + d * (f + g) := by ring

theorem output_shift7 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift7 a delta) =
      Char2Degree25Frame.output a + C delta * outputSlope a delta := by
  change Char2Degree25Frame.head (shift7 a delta) + n (shift7 a delta) + C (a 24) = _
  rw [head_shift7, n_shift7]
  exact collect_output (Char2Degree25Frame.head a) (n a) (C (a 24)) (C delta)
    (uSlope a delta) (nRight a * leftSlope a delta)

theorem uSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (uSlope a delta) 2 :=
  y_monic.add_right (by rw [natDegree_C]; omega)
theorem rSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (rSlope a delta) 7 :=
  (rLeft_monic a).mul (uSlope_monic a delta)
theorem gSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (gSlope a delta) 7 :=
  (Char2Degree25SeamFrame.seamGLeft_monic a).mul (uSlope_monic a delta)
theorem hSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (hSlope a delta) 12 :=
  (hLeft_monic a).mul ((rSlope_monic a delta).add_left
    ((uSlope_monic a delta).natDegree_eq.trans_lt (by omega)))
theorem leftSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (leftSlope a delta) 12 := by
  have hl : (uSlope a delta + rSlope a delta + gSlope a delta).natDegree ≤ 7 :=
    natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le ((uSlope_monic a delta).natDegree_eq.le.trans (by omega))
        (rSlope_monic a delta).natDegree_eq.le) (gSlope_monic a delta).natDegree_eq.le
  exact (hSlope_monic a delta).add_left (hl.trans_lt (by omega))
theorem outputSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (outputSlope a delta) 17 :=
  ((nRight_monic a).mul (leftSlope_monic a delta)).add_left
    ((uSlope_monic a delta).natDegree_eq.trans_lt (by omega))

theorem shift7_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift7 a delta)) 17 delta := by
  apply unit_difference_of_split (Char2Degree25Frame.output a)
    (Char2Degree25Frame.output (shift7 a delta)) (outputSlope a delta) 17 delta 0
    (by omega) (outputSlope_monic a delta)
  rw [map_zero, add_zero, output_shift7]

end FastPoly.Char2Degree25RowSeventeen

