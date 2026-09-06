import FastPoly.Examples.Char2Degree25TwentyTwoBounds
import FastPoly.Examples.Char2Degree21Frame

/-! The supplied terminal head remainders, with their explicit quotients.
The correction parameters k and e remain free, named scalars. Actual raw-key
tracking and the preceding high-row peel are separate obligations. -/

namespace FastPoly.Char2Degree25TerminalHead

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
  Char2Degree19InnerTail
open Char2Degree25TwentyTwoWires (U E)
open Char2Degree25RowThirteen (L ellSlope L_monic ellSlope_monic)

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def B (a : ℕ → R) : R := a 2 + a 6
def alpha (a : ℕ → R) : R := a 23 + a 5
def theta (a : ℕ → R) (d : R) : R := (B a + 1) * d

noncomputable def row4Head (a : ℕ → R) (d k e : R) : R[X] :=
  C d * U a + C k * ellSlope a + C e * E a
noncomputable def row4Remainder (a : ℕ → R) (d k e : R) : R[X] :=
  C d * (z a + C (alpha a)) + C k * ellSlope a + C e * E a

noncomputable def cubic (a : ℕ → R) : R[X] := v a + t a + C (B a) * z a
noncomputable def row3Tail (a : ℕ → R) (d k e : R) : R[X] :=
  C (theta a d * alpha a) + C (d * (a 17 + a 23)) +
    (E a + C d) * (C k * L a + C e)
noncomputable def row3Head (a : ℕ → R) (d k e : R) : R[X] :=
  C (theta a d) * U a + C d * (z a + v a + C (a 17)) +
    (E a + C d) * (C k * L a + C e)
noncomputable def row3Remainder (a : ℕ → R) (d k e : R) : R[X] :=
  C d * cubic a + row3Tail a d k e

noncomputable def row2Remainder (a : ℕ → R) (d e : R) : R[X] :=
  C d * ellSlope a + C e * E a
noncomputable def row1Remainder (a : ℕ → R) (d : R) : R[X] := C d * E a

private theorem row4_collect (d z t c5 c23 low : R[X]) :
    d * (z + t + c5) + low =
      (d * (z + (c23 + c5)) + low) + (t + c23) * d := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

/-- The row-four quotient is the literal constant d. -/
theorem row4_split (a : ℕ → R) (d k e : R) :
    row4Head a d k e = row4Remainder a d k e + nRight a * C d := by
  unfold row4Head row4Remainder U nRight alpha
  rw [map_add]
  have he := row4_collect (C d) (z a) (t a) (C (a 5)) (C (a 23))
    (C k * ellSlope a + C e * E a)
  simpa only [add_assoc] using he

private theorem cubic_collect (x y z c2 c6 c3 c7 : R[X]) :
    (x + c6) * (y + z + c7) + (x + c2) * (z + c3) + (c2 + c6) * z =
      (x + c6) * y + c7 * (x + c6) + c3 * (x + c2) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

/-- Cancel the shared z column before reading the monic cubic. -/
theorem cubic_eq (a : ℕ → R) :
    cubic a = L a * y + C (a 7) * L a + C (a 3) * (X + C (a 2)) := by
  unfold cubic B
  rw [map_add]
  exact cubic_collect X y (z a) (C (a 2)) (C (a 6)) (C (a 3)) (C (a 7))

private theorem row3_collect (b d z t v c5 c23 c17 low : R[X]) :
    ((b + 1) * d) * (z + t + c5) + d * (z + v + c17) + low =
      d * (v + t + b * z) +
        (((b + 1) * d) * (c23 + c5) + d * (c17 + c23) + low) +
        (t + c23) * ((b + 1) * d + d) := by
  have ht : (b + 1) * d + d = b * d := by
    rw [add_mul, one_mul, CharTwo.add_cancel_right]
  rw [ht]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

/-- The row-three quotient is theta+d, with theta=(B+1)d as supplied. -/
theorem row3_split (a : ℕ → R) (d k e : R) :
    row3Head a d k e = row3Remainder a d k e + nRight a * C (theta a d + d) := by
  unfold row3Head row3Remainder row3Tail theta alpha cubic U nRight
  simp only [map_add, map_mul, map_one]
  exact row3_collect (C (B a)) (C d) (z a) (t a) (v a)
    (C (a 5)) (C (a 23)) (C (a 17)) ((E a + C d) * (C k * L a + C e))

private theorem Cmul_degree (c : R) {p : R[X]} {n : ℕ} (hp : p.natDegree ≤ n) :
    (C c * p).natDegree ≤ n := by
  apply natDegree_mul_le.trans
  rw [natDegree_C, zero_add]
  exact hp

theorem E_monic (a : ℕ → R) : IsMonicOfDegree (E a) 1 :=
  isMonicOfDegree_X_add_one _

theorem cubic_monic (a : ℕ → R) : IsMonicOfDegree (cubic a) 3 := by
  rw [cubic_eq]
  have h7 : (C (a 7) * L a).natDegree < 3 :=
    (Cmul_degree _ (L_monic a).natDegree_eq.le).trans_lt (by omega)
  have h3 : (C (a 3) * (X + C (a 2))).natDegree < 3 :=
    (Cmul_degree _ (isMonicOfDegree_X_add_one (a 2)).natDegree_eq.le).trans_lt (by omega)
  exact (((L_monic a).mul y_monic).add_right h7).add_right h3

theorem row3Tail_degree (a : ℕ → R) (d k e : R) : (row3Tail a d k e).natDegree ≤ 2 := by
  have he : (E a + C d).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (E_monic a).natDegree_eq.le (by rw [natDegree_C]; omega)
  have hk : (C k * L a + C e).natDegree ≤ 1 :=
    natDegree_add_le_of_degree_le (Cmul_degree _ (L_monic a).natDegree_eq.le)
      (by rw [natDegree_C]; omega)
  have hp : ((E a + C d) * (C k * L a + C e)).natDegree ≤ 2 :=
    natDegree_mul_le.trans (Nat.add_le_add he hk)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (by rw [natDegree_C]; omega)
      (by rw [natDegree_C]; omega)) hp

private theorem scaled_low_unit {p low : R[X]} {r : ℕ} (d : R)
    (hp : IsMonicOfDegree p r) (hl : low.natDegree < r) :
    UnitDifference 0 (C d * p + low) r d := by
  have hs := Char2Degree21Frame.difference_scaled (p := (0 : R[X])) d hp
  have hlow : (low + (0 : R[X])).natDegree < r := by rwa [add_zero]
  have hu := Char2Degree21Frame.difference_add_lower hs hlow
  simpa only [zero_add, add_zero] using hu

theorem row4_unit (a : ℕ → R) (d k e : R) :
    UnitDifference 0 (row4Remainder a d k e) 4 d := by
  have hs : IsMonicOfDegree (z a + C (alpha a)) 4 :=
    (z_monic a).add_right (by rw [natDegree_C]; omega)
  have hk : (C k * ellSlope a).natDegree ≤ 2 := Cmul_degree _ (ellSlope_monic a).natDegree_eq.le
  have he : (C e * E a).natDegree ≤ 2 :=
    (Cmul_degree _ (E_monic a).natDegree_eq.le).trans (by omega)
  have hl : (C k * ellSlope a + C e * E a).natDegree < 4 :=
    (natDegree_add_le_of_degree_le hk he).trans_lt (by omega)
  have hu := scaled_low_unit d hs hl
  simpa only [row4Remainder, add_assoc] using hu

theorem row3_unit (a : ℕ → R) (d k e : R) :
    UnitDifference 0 (row3Remainder a d k e) 3 d :=
  scaled_low_unit d (cubic_monic a) ((row3Tail_degree a d k e).trans_lt (by omega))

theorem row2_unit (a : ℕ → R) (d e : R) :
    UnitDifference 0 (row2Remainder a d e) 2 d :=
  scaled_low_unit d (ellSlope_monic a)
    ((Cmul_degree _ (E_monic a).natDegree_eq.le).trans_lt (by omega))

theorem row1_unit (a : ℕ → R) (d : R) :
    UnitDifference 0 (row1Remainder a d) 1 d := by
  have hu := Char2Degree21Frame.difference_scaled (p := (0 : R[X])) d (E_monic a)
  simpa only [zero_add, row1Remainder] using hu

end FastPoly.Char2Degree25TerminalHead
