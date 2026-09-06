import FastPoly.Examples.Char2Degree25RowThirteen
import FastPoly.Examples.Char2Degree25RowsTenNine

/-! The supplied row-eight direction changes a15 and cancels its two
leading rows with a10 and a11. Its remaining column is explicitly cubic
before multiplication by nRight; the quadratic offset term is retained. -/
namespace FastPoly.Char2Degree25RowEight

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def b (a : ℕ → R) : R := a 2 + a 6 + 1
def shift (a : ℕ → R) (d : R) : ℕ → R
  | 10 => a 10 + d
  | 11 => a 11 + b a * d
  | 15 => a 15 + d
  | i => a i

noncomputable def E (a : ℕ → R) : R[X] := z a + t a + C (a 14)
noncomputable def sSlope (a : ℕ → R) (d : R) : R[X] :=
  v a + C (a 11) + C (b a) * (z a + C (a 10)) + C (b a * d)
noncomputable def cubic (a : ℕ → R) (d : R) : R[X] :=
  (X + C (a 6)) * y + (X + C (a 2)) * C (a 3) +
  (X + C (a 6)) * C (a 7) + C (a 14) + C (a 11) +
  C (b a * (a 10 + d))
noncomputable def slope (a : ℕ → R) (d : R) : R[X] := nRight a * cubic a d

private theorem product_both (p q d b : R[X]) :
    (p + d) * (q + b * d) = p * q + d * (q + b * p + b * d) := by ring

theorem s_shift (a : ℕ → R) (d : R) :
    s (shift a d) = s a + C d * sSlope a d := by
  change (z a + C (a 10 + d)) * (v a + C (a 11 + b a * d)) = _
  rw [map_add, map_add, map_mul]
  simp only [← add_assoc]
  rw [product_both]
  rw [← map_mul]
  rfl

theorem g_shift (a : ℕ → R) (d : R) :
    g (shift a d) = g a + C d * E a := by
  change E a * (X + u a + C (a 15 + d)) = _
  rw [map_add, ← add_assoc, mul_add, mul_comm (E a) (C d)]
  rfl

private theorem cubic_cancel (x y z a c e f k l d : R[X]) :
    z + (x + a) * (z + e) + k +
      ((x + c) * (y + z + f) + l + (a + c + 1) * (z + d)) =
    (x + c) * y + (x + a) * e + (x + c) * f + k + l + (a + c + 1) * d := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem inner_eq (a : ℕ → R) (d : R) : E a + sSlope a d = cubic a d := by
  change (z a + (X + C (a 2)) * (z a + C (a 3)) + C (a 14)) +
    ((X + C (a 6)) * (y + z a + C (a 7)) + C (a 11) +
      C (b a) * (z a + C (a 10)) + C (b a * d)) = _
  have hc := cubic_cancel (X : R[X]) y (z a) (C (a 2)) (C (a 6))
    (C (a 3)) (C (a 7)) (C (a 14)) (C (a 11)) (C (a 10))
  have hb : C (b a) = C (a 2) + C (a 6) + 1 := by
    simp only [b, map_add, map_one]
  rw [hb, ← add_assoc, hc]
  simp only [cubic, map_mul, map_add, hb, mul_add, add_assoc]

private theorem collect_left (x s r g e h j c d ss gs : R[X]) :
    x + (s + d * ss) + r + (g + d * gs) + e + h + j + c =
    (x + s + r + g + e + h + j + c) + d * (gs + ss) := by ring

theorem nLeft_shift (a : ℕ → R) (d : R) :
    nLeft (shift a d) = nLeft a + C d * cubic a d := by
  change X + t a + u a + s (shift a d) + r a + g (shift a d) +
    ell a + h a + j a + C (a 22) = _
  rw [s_shift, g_shift, collect_left, inner_eq]
  rfl

private theorem collect_output (head nl nr c d f : R[X]) :
    head + (nl + d * f) * nr + c = (head + nl * nr + c) + d * (nr * f) := by ring

theorem output_shift (a : ℕ → R) (d : R) :
    Char2Degree25Frame.output (shift a d) = Char2Degree25Frame.output a + C d * slope a d := by
  change Char2Degree25Frame.head a + nLeft (shift a d) * nRight a + C (a 24) = _
  rw [nLeft_shift]
  exact collect_output _ _ _ _ _ _

theorem cubic_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (cubic a d) 3 := by
  have hl (k c : R) : ((X + C k) * C c).natDegree < 3 :=
    (natDegree_mul_le.trans (Nat.add_le_add
      (isMonicOfDegree_X_add_one k).natDegree_eq.le (natDegree_C c).le)).trans_lt (by omega)
  have hc (c : R) : (C c).natDegree < 3 := by rw [natDegree_C]; omega
  exact (((((isMonicOfDegree_X_add_one (a 6)).mul y_monic).add_right (hl _ _)).add_right
    (hl _ _)).add_right (hc _)).add_right (hc _) |>.add_right (hc _)

theorem slope_monic (a : ℕ → R) (d : R) : IsMonicOfDegree (slope a d) 8 :=
  (nRight_monic a).mul (cubic_monic a d)

theorem shift_unit (a : ℕ → R) (d : R) :
    UnitDifference (Char2Degree25Frame.output a)
      (Char2Degree25Frame.output (shift a d)) 8 d := by
  apply unit_difference_of_split _ _ (slope a d) 8 d 0 (by omega) (slope_monic a d)
  simpa only [map_zero, add_zero] using output_shift a d

end FastPoly.Char2Degree25RowEight
