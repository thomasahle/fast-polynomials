import FastPoly.Examples.Char2Degree25TerminalHead
import FastPoly.Examples.Char2MonicRemainder

/-! Exact small head differences, with every changed offset supplied.
Only the original z,t,u,v,ell definitions relevant to the head are used.
The final nLeft product stays opaque and supplies the explicit quotient. -/
namespace FastPoly.Char2Degree25HeadChange

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
open Char2Degree25TwentyTwoWires (U E)
open Char2Degree25RowThirteen (L)
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

structure SameBase (a b : ℕ → R) : Prop where
  h0 : b 0 = a 0
  h1 : b 1 = a 1
  h2 : b 2 = a 2
  h3 : b 3 = a 3
  h5 : b 5 = a 5
  h6 : b 6 = a 6

variable {a b : ℕ → R}
theorem SameBase.z_eq (h : SameBase a b) : z b = z a := by
  simp only [z, h.h0, h.h1]
theorem SameBase.t_eq (h : SameBase a b) : t b = t a := by
  simp only [t, h.h2, h.h3, h.z_eq]

theorem SameBase.u_change (h : SameBase a b) (d4 : R) (h4 : b 4 = a 4 + d4) :
    u b = u a + C d4 * U a := by
  unfold u
  rw [h.z_eq, h.t_eq, h4, h.h5, map_add, ← add_assoc, add_mul]
  rfl
theorem SameBase.v_change (h : SameBase a b) (k : R) (h7 : b 7 = a 7 + k) :
    v b = v a + C k * L a := by
  unfold v
  rw [h.h6, h.z_eq, h7, map_add, ← add_assoc, mul_add, mul_comm _ (C k)]
  rfl

private theorem product_change (E p d k e : R[X]) :
    (E + d) * (p + k + e) = E * p + d * p + (E + d) * (k + e) := by ring

theorem SameBase.ell_change (h : SameBase a b) (k d e : R)
    (h7 : b 7 = a 7 + k) (h16 : b 16 = a 16 + d) (h17 : b 17 = a 17 + e) :
    ell b = ell a + C d * (z a + v a + C (a 17)) +
      (E a + C d) * (C k * L a + C e) := by
  unfold ell
  rw [h16, h.z_eq, h.v_change k h7, h17, map_add, map_add]
  have hr : z a + (v a + C k * L a) + (C (a 17) + C e) =
      (z a + v a + C (a 17)) + C k * L a + C e := by ac_rfl
  rw [hr, ← add_assoc (X : R[X]) (C (a 16)) (C d), product_change]
  rfl

private theorem collect_head (h u ell d4 U d zvel E k L e : R[X]) :
    (h + (u + d4 * U) + (ell + d * zvel + (E + d) * (k * L + e))) + (h + u + ell) =
      d4 * U + d * zvel + (E + d) * (k * L + e) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

theorem SameBase.head_change (h : SameBase a b) (d4 k d e : R)
    (h4 : b 4 = a 4 + d4) (h7 : b 7 = a 7 + k)
    (h16 : b 16 = a 16 + d) (h17 : b 17 = a 17 + e) :
    Char2Degree25Frame.head b + Char2Degree25Frame.head a =
      C d4 * U a + C d * (z a + v a + C (a 17)) +
        (E a + C d) * (C k * L a + C e) := by
  unfold Char2Degree25Frame.head
  rw [h.z_eq, h.u_change d4 h4, h.ell_change k d e h7 h16 h17]
  exact collect_head _ _ _ _ _ _ _ _ _ _ _

private theorem collect_output (h h' N q q' c : R[X]) :
    (h' + q' * N + c) + (h + q * N + c) = (h' + h) + N * (q' + q) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_mul, add_zero, zero_add]

theorem output_difference (hN : nRight b = nRight a) (h24 : b 24 = a 24) :
    Char2Degree25Frame.output b + Char2Degree25Frame.output a =
      (Char2Degree25Frame.head b + Char2Degree25Frame.head a) +
        nRight a * (nLeft b + nLeft a) := by
  unfold Char2Degree25Frame.output n
  rw [hN, h24]
  exact collect_output _ _ _ _ _ _

end FastPoly.Char2Degree25HeadChange
