import FastPoly.Examples.Char2Degree25HighPivots

/-! The supplied paired a12/a4 seam pivot in row nineteen.
Its apparent degree-fifteen r change cancels to a named degree-nine slope.
The proof follows the actual u, r, g, h, n gates; no output coefficient or
normalized-coordinate coverage is claimed beyond this raw unit step. -/

namespace FastPoly.Char2Degree25SeamFrame

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree25HighDifference Char2Degree19InnerTail

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift5 (a : ℕ → R) (delta : R) : ℕ → R
  | 4 => a 4 + delta
  | 12 => a 12 + delta
  | j => a j

noncomputable def seamFactor (a : ℕ → R) (delta : R) : R[X] :=
  X + y + z a + C (a 4 + a 12 + delta)
noncomputable def rSlope (a : ℕ → R) (delta : R) : R[X] :=
  seamFactor a delta * uRight a + C (a 13)
noncomputable def seamGLeft (a : ℕ → R) : R[X] := z a + t a + C (a 14)
noncomputable def hSlope (a : ℕ → R) (delta : R) : R[X] :=
  hLeft a * (uRight a + rSlope a delta)
noncomputable def leftSlope (a : ℕ → R) (delta : R) : R[X] :=
  uRight a + rSlope a delta + seamGLeft a * uRight a + hSlope a delta
noncomputable def outputSlope (a : ℕ → R) (delta : R) : R[X] :=
  uRight a + nRight a * leftSlope a delta

theorem u_shift5 (a : ℕ → R) (delta : R) :
    u (shift5 a delta) = u a + C delta * uRight a := by
  change (y + z a + t a + C (a 4 + delta)) * uRight a = _
  rw [map_add, ← add_assoc, add_mul]
  rfl

theorem rLeft_shift5 (a : ℕ → R) (delta : R) :
    rLeft (shift5 a delta) = rLeft a + C delta := by
  change X + t a + C (a 12 + delta) = _
  rw [map_add, ← add_assoc]
  rfl

theorem seam_sum (a : ℕ → R) (delta : R) :
    uLeft a + rLeft a + C delta = seamFactor a delta := by
  unfold uLeft rLeft seamFactor
  simp only [map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

private theorem r_change (r l v c d : R[X]) :
    (r + d) * (l * v + d * v + c) =
      r * (l * v + c) + d * ((l + r + d) * v + c) := by ring

theorem r_shift5 (a : ℕ → R) (delta : R) :
    r (shift5 a delta) = r a + C delta * rSlope a delta := by
  change rLeft (shift5 a delta) * (u (shift5 a delta) + C (a 13)) = _
  rw [rLeft_shift5, u_shift5]
  change (rLeft a + C delta) * (uLeft a * uRight a + C delta * uRight a + C (a 13)) = _
  rw [r_change, seam_sum]
  rfl

private theorem middle_change (l x u c d f : R[X]) :
    l * (x + (u + d * f) + c) = l * (x + u + c) + d * (l * f) := by ring

theorem g_shift5 (a : ℕ → R) (delta : R) :
    g (shift5 a delta) = g a + C delta * (seamGLeft a * uRight a) := by
  change seamGLeft a * (X + u (shift5 a delta) + C (a 15)) = _
  rw [u_shift5]
  exact middle_change (seamGLeft a) X (u a) (C (a 15)) (C delta) (uRight a)

private theorem collect_right (x u v w r c d f g : R[X]) :
    x + (u + d * f) + v + w + (r + d * g) + c =
      (x + u + v + w + r + c) + d * (f + g) := by ring

theorem hRight_shift5 (a : ℕ → R) (delta : R) :
    hRight (shift5 a delta) = hRight a + C delta * (uRight a + rSlope a delta) := by
  change X + y + z a + u (shift5 a delta) + v a + w a + r (shift5 a delta) + C (a 19) = _
  rw [u_shift5, r_shift5]
  exact collect_right (X + y + z a) (u a) (v a) (w a) (r a) (C (a 19))
    (C delta) (uRight a) (rSlope a delta)

private theorem product_right_change (a b d c : R[X]) :
    a * (b + d * c) = a * b + d * (a * c) := by ring

theorem h_shift5 (a : ℕ → R) (delta : R) :
    h (shift5 a delta) = h a + C delta * hSlope a delta := by
  change hLeft a * hRight (shift5 a delta) = _
  rw [hRight_shift5]
  exact product_right_change (hLeft a) (hRight a) (C delta) (uRight a + rSlope a delta)

private theorem collect_left (x u s r g ell h j c d f0 f1 f2 f3 : R[X]) :
    x + (u + d * f0) + s + (r + d * f1) + (g + d * f2) + ell + (h + d * f3) + j + c =
      (x + u + s + r + g + ell + h + j + c) + d * (f0 + f1 + f2 + f3) := by ring

theorem nLeft_shift5 (a : ℕ → R) (delta : R) :
    nLeft (shift5 a delta) = nLeft a + C delta * leftSlope a delta := by
  change X + t a + u (shift5 a delta) + s a + r (shift5 a delta) +
    g (shift5 a delta) + ell a + h (shift5 a delta) + j a + C (a 22) = _
  rw [u_shift5, r_shift5, g_shift5, h_shift5]
  exact collect_left (X + t a) (u a) (s a) (r a) (g a) (ell a) (h a) (j a)
    (C (a 22)) (C delta) (uRight a) (rSlope a delta) (seamGLeft a * uRight a) (hSlope a delta)

private theorem product_left_change (a b d c : R[X]) :
    (a + d * c) * b = a * b + d * (b * c) := by ring

theorem n_shift5 (a : ℕ → R) (delta : R) :
    n (shift5 a delta) = n a + C delta * (nRight a * leftSlope a delta) := by
  change nLeft (shift5 a delta) * nRight a = _
  rw [nLeft_shift5]
  exact product_left_change (nLeft a) (nRight a) (C delta) (leftSlope a delta)

private theorem collect_head (x u e d f : R[X]) :
    x + (u + d * f) + e = (x + u + e) + d * f := by ac_rfl

theorem head_shift5 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.head (shift5 a delta) = Char2Degree25Frame.head a + C delta * uRight a := by
  change y + z a + u (shift5 a delta) + ell a = _
  rw [u_shift5]
  exact collect_head (y + z a) (u a) (ell a) (C delta) (uRight a)

private theorem collect_output (h n c d f g : R[X]) :
    (h + d * f) + (n + d * g) + c = (h + n + c) + d * (f + g) := by ring

theorem output_shift5 (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift5 a delta) =
      Char2Degree25Frame.output a + C delta * outputSlope a delta := by
  change Char2Degree25Frame.head (shift5 a delta) + n (shift5 a delta) + C (a 24) = _
  rw [head_shift5, n_shift5]
  exact collect_output (Char2Degree25Frame.head a) (n a) (C (a 24)) (C delta)
    (uRight a) (nRight a * leftSlope a delta)

theorem seamFactor_monic (a : ℕ → R) (delta : R) :
    IsMonicOfDegree (seamFactor a delta) 4 :=
  ((z_monic a).add_left (x_add_y_monic.natDegree_eq.trans_lt (by omega))).add_right
    (by rw [natDegree_C]; omega)

theorem rSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (rSlope a delta) 9 :=
  ((seamFactor_monic a delta).mul (uRight_monic a)).add_right (by rw [natDegree_C]; omega)

theorem seamGLeft_monic (a : ℕ → R) : IsMonicOfDegree (seamGLeft a) 5 :=
  (z_add_t_monic a).add_right (by rw [natDegree_C]; omega)

theorem hSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (hSlope a delta) 14 :=
  (hLeft_monic a).mul ((rSlope_monic a delta).add_left
    ((uRight_monic a).natDegree_eq.trans_lt (by omega)))

theorem leftSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (leftSlope a delta) 14 := by
  have hl : IsMonicOfDegree (uRight a + rSlope a delta + seamGLeft a * uRight a) 10 :=
    ((seamGLeft_monic a).mul (uRight_monic a)).add_left
      (((rSlope_monic a delta).add_left ((uRight_monic a).natDegree_eq.trans_lt
        (by omega))).natDegree_eq.trans_lt (by omega))
  exact (hSlope_monic a delta).add_left (hl.natDegree_eq.trans_lt (by omega))

theorem outputSlope_monic (a : ℕ → R) (delta : R) : IsMonicOfDegree (outputSlope a delta) 19 :=
  ((nRight_monic a).mul (leftSlope_monic a delta)).add_left
    ((uRight_monic a).natDegree_eq.trans_lt (by omega))

theorem shift5_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift5 a delta)) 19 delta := by
  apply unit_difference_of_split (Char2Degree25Frame.output a)
    (Char2Degree25Frame.output (shift5 a delta)) (outputSlope a delta) 19 delta 0
    (by omega) (outputSlope_monic a delta)
  rw [map_zero, add_zero, output_shift5]

end FastPoly.Char2Degree25SeamFrame

