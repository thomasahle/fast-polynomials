import FastPoly.Examples.Char2Degree25HighFrame
import FastPoly.Examples.Char2Degree19InnerTail

/-! The existing raw row-thirteen shift: a7,a13 increase by delta and
a9 increases by (a2+a6)*delta. A named cubic cancellation makes the
h-branch slope monic of degree eight. -/
namespace FastPoly.Char2Degree25RowThirteen

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree25HighFrame Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def B (a : ℕ → R) : R := a 2 + a 6
def shift (a : ℕ → R) (delta : R) : ℕ → R
  | 7 => a 7 + delta
  | 9 => a 9 + B a * delta
  | 13 => a 13 + delta
  | i => a i

noncomputable def L (a : ℕ → R) : R[X] := X + C (a 6)
noncomputable def P (a : ℕ → R) : R[X] := X + y + z a + C (a 8)
noncomputable def sSlope (a : ℕ → R) : R[X] := (z a + C (a 10)) * L a
noncomputable def ellSlope (a : ℕ → R) : R[X] := (X + C (a 16)) * L a
noncomputable def inner (a : ℕ → R) : R[X] := L a + P a * (L a + C (B a)) + rLeft a
noncomputable def hSlope (a : ℕ → R) : R[X] := hLeft a * inner a
noncomputable def jSlope (a : ℕ → R) : R[X] := jLeft a * ellSlope a
noncomputable def leftSlope (a : ℕ → R) : R[X] :=
  sSlope a + rLeft a + ellSlope a + hSlope a + jSlope a
noncomputable def outputSlope (a : ℕ → R) : R[X] :=
  ellSlope a + nRight a * leftSlope a

theorem product_change (l p c d s : R[X]) :
    l * ((p + d * s) + c) = l * (p + c) + d * (l * s) := by ring

theorem product_change_middle (l z p c d s : R[X]) :
    l * (z + (p + d * s) + c) = l * (z + p + c) + d * (l * s) := by ring

theorem product_change_plain (l p d s : R[X]) :
    l * (p + d * s) = l * p + d * (l * s) := by ring

theorem v_shift (a : ℕ → R) (delta : R) :
    v (shift a delta) = v a + C delta * L a := by
  change L a * (y + z a + C (a 7 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (L a) (C delta)]
  rfl

private theorem w_collect (p y v c d l b : R[X]) :
    p * (y + (v + d * l) + (c + b * d)) =
      p * (y + v + c) + d * (p * (l + b)) := by ring

theorem w_shift (a : ℕ → R) (delta : R) :
    w (shift a delta) = w a + C delta * (P a * (L a + C (B a))) := by
  change P a * (y + v (shift a delta) + C (a 9 + B a * delta)) = _
  rw [v_shift, map_add, map_mul]
  exact w_collect _ _ _ _ _ _ _

theorem s_shift (a : ℕ → R) (delta : R) :
    s (shift a delta) = s a + C delta * sSlope a := by
  change (z a + C (a 10)) * (v (shift a delta) + C (a 11)) = _
  rw [v_shift]
  exact product_change _ _ _ _ _

theorem r_shift (a : ℕ → R) (delta : R) :
    r (shift a delta) = r a + C delta * rLeft a := by
  change rLeft a * (u a + C (a 13 + delta)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (rLeft a) (C delta)]
  rfl

theorem ell_shift (a : ℕ → R) (delta : R) :
    ell (shift a delta) = ell a + C delta * ellSlope a := by
  change (X + C (a 16)) * (z a + v (shift a delta) + C (a 17)) = _
  rw [v_shift]
  exact product_change_middle _ _ _ _ _ _

theorem collect_hRight (x v w r c d l ws rs : R[X]) :
    x + (v + d * l) + (w + d * ws) + (r + d * rs) + c =
      (x + v + w + r + c) + d * (l + ws + rs) := by ring

theorem hRight_shift (a : ℕ → R) (delta : R) :
    hRight (shift a delta) = hRight a + C delta * inner a := by
  change X + y + z a + u a + v (shift a delta) + w (shift a delta) +
    r (shift a delta) + C (a 19) = _
  rw [v_shift, w_shift, r_shift]
  exact collect_hRight _ _ _ _ _ _ _ _ _

theorem h_shift (a : ℕ → R) (delta : R) :
    h (shift a delta) = h a + C delta * hSlope a := by
  change hLeft a * hRight (shift a delta) = _
  rw [hRight_shift]
  exact product_change_plain _ _ _ _

theorem j_shift (a : ℕ → R) (delta : R) :
    j (shift a delta) = j a + C delta * jSlope a := by
  change jLeft a * (ell (shift a delta) + C (a 21)) = _
  rw [ell_shift]
  exact product_change _ _ _ _ _

theorem collect_nLeft (x s r g ell h j c d ss rs es hs js : R[X]) :
    x + (s + d * ss) + (r + d * rs) + g + (ell + d * es) +
      (h + d * hs) + (j + d * js) + c =
      (x + s + r + g + ell + h + j + c) + d * (ss + rs + es + hs + js) := by ring

theorem nLeft_shift (a : ℕ → R) (delta : R) :
    nLeft (shift a delta) = nLeft a + C delta * leftSlope a := by
  change X + t a + u a + s (shift a delta) + r (shift a delta) + g a +
    ell (shift a delta) + h (shift a delta) + j (shift a delta) + C (a 22) = _
  rw [s_shift, r_shift, ell_shift, h_shift, j_shift]
  exact collect_nLeft _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem collect_output (head ell nl nr c d es ls : R[X]) :
    head + (ell + d * es) + (nl + d * ls) * nr + c =
      (head + ell + nl * nr + c) + d * (es + nr * ls) := by ring

theorem output_shift (a : ℕ → R) (delta : R) :
    Char2Degree25Frame.output (shift a delta) =
      Char2Degree25Frame.output a + C delta * outputSlope a := by
  change y + z a + u a + ell (shift a delta) +
    nLeft (shift a delta) * nRight a + C (a 24) = _
  rw [ell_shift, nLeft_shift]
  exact collect_output _ _ _ _ _ _ _ _

theorem L_add_B (a : ℕ → R) : L a + C (B a) = X + C (a 2) := by
  simp only [L, B, map_add, add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

private theorem cubic_cancel (x y z a b c e f : R[X]) :
    (x + b) + (x + y + z + c) * (x + a) + (x + (x + a) * (z + e) + f) =
      (x + a) * (x + y + (e + c)) + (b + f) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem inner_eq (a : ℕ → R) : inner a =
    (X + C (a 2)) * (X + y + C (a 3 + a 8)) + C (a 6 + a 12) := by
  rw [inner, L_add_B]
  change (X + C (a 6)) + (X + y + z a + C (a 8)) * (X + C (a 2)) +
    (X + (X + C (a 2)) * (z a + C (a 3)) + C (a 12)) = _
  rw [map_add, map_add]
  exact cubic_cancel _ _ _ _ _ _ _ _

theorem C_lt (c : R) (n : ℕ) (hn : 0 < n) : (C c).natDegree < n := by
  rw [natDegree_C]
  exact hn

theorem L_monic (a : ℕ → R) : IsMonicOfDegree (L a) 1 := isMonicOfDegree_X_add_one _
theorem sSlope_monic (a : ℕ → R) : IsMonicOfDegree (sSlope a) 5 :=
  ((z_monic a).add_right (C_lt _ _ (by omega))).mul (L_monic a)
theorem ellSlope_monic (a : ℕ → R) : IsMonicOfDegree (ellSlope a) 2 :=
  (isMonicOfDegree_X_add_one (a 16)).mul (L_monic a)
theorem jSlope_monic (a : ℕ → R) : IsMonicOfDegree (jSlope a) 7 :=
  (jLeft_monic a).mul (ellSlope_monic a)

theorem inner_monic (a : ℕ → R) : IsMonicOfDegree (inner a) 3 := by
  rw [inner_eq]
  exact ((isMonicOfDegree_X_add_one (a 2)).mul
    (x_add_y_monic.add_right (C_lt _ _ (by omega)))).add_right (C_lt _ _ (by omega))

theorem hSlope_monic (a : ℕ → R) : IsMonicOfDegree (hSlope a) 8 :=
  (hLeft_monic a).mul (inner_monic a)

theorem leftSlope_monic (a : ℕ → R) : IsMonicOfDegree (leftSlope a) 8 := by
  have hl : (sSlope a + rLeft a + ellSlope a).natDegree < 8 :=
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le (sSlope_monic a).natDegree_eq.le
        (rLeft_monic a).natDegree_eq.le)
      ((ellSlope_monic a).natDegree_eq.le.trans (by omega))).trans_lt (by omega)
  exact ((hSlope_monic a).add_left hl).add_right ((jSlope_monic a).natDegree_eq.trans_lt (by omega))

theorem outputSlope_monic (a : ℕ → R) : IsMonicOfDegree (outputSlope a) 13 :=
  ((nRight_monic a).mul (leftSlope_monic a)).add_left
    ((ellSlope_monic a).natDegree_eq.trans_lt (by omega))

theorem shift_unit (a : ℕ → R) (delta : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift a delta)) 13 delta := by
  apply unit_difference_of_split _ _ (outputSlope a) 13 delta 0 (by omega) (outputSlope_monic a)
  simpa only [map_zero, add_zero] using output_shift a delta

end FastPoly.Char2Degree25RowThirteen
