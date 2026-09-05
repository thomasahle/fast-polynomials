import FastPoly.Examples.Char2Degree23SixteenFrame
import FastPoly.Examples.Char2Degree23TwentyCoordinates

/-! The supplied sixteenth key update, followed by its explicit row-eight peel. -/

namespace FastPoly.Char2Degree23SixteenKeys

open Polynomial Char2Decoder Char2Degree23Coordinates Char2Degree23RowEight
  Char2Degree23HighKeys Char2Degree23LowKeys Char2Degree23MiddleKeys

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def kappaQ (q : Vector R) (d : R) : R := q 7 * d + d ^ 2
def sigmaQ (q : Vector R) (d : R) : R := kappaQ q d ^ 2 + gamma q * kappaQ q d + d

theorem kappa_rawKeys (q : Vector R) (d : R) :
    Char2Degree23SixteenWires.kappa (rawKeys q) d = kappaQ q d := by
  unfold Char2Degree23SixteenWires.kappa
  rw [top14, top5]
  change ((q 7 + q 16) + q 16) * d + d ^ 2 = _
  rw [CharTwo.add_cancel_right]
  rfl

theorem sigma_rawKeys (q : Vector R) (d : R) :
    Char2Degree23SixteenWires.sigma (rawKeys q) d = sigmaQ q d := by
  unfold Char2Degree23SixteenWires.sigma sigmaQ
  rw [kappa_rawKeys]
  change kappaQ q d ^ 2 + Char2Degree23TwentyCoordinates.gammaRaw (rawKeys q) * kappaQ q d + d = _
  rw [Char2Degree23TwentyCoordinates.gammaRaw_rawKeys]

theorem B_rawKeys (q : Vector R) : Char2Degree23SixteenWires.B (rawKeys q) = q 0 + q 8 :=
  Char2Degree23TwentyCoordinates.B_rawKeys q

theorem A_rawKeys (q : Vector R) : Char2Degree23SixteenWires.A (rawKeys q) = q 0 + q 8 + 1 := by
  unfold Char2Degree23SixteenWires.A
  rw [B_rawKeys]

theorem eta16 (q : Vector R) (d : R) : eta (increment q 16 d) = eta q + kappaQ q d := by
  change q 7 * (q 16 + d) + (q 16 + d) ^ 2 + q 20 = _
  rw [CharTwo.add_sq, mul_add]
  unfold Char2Degree23Coordinates.eta kappaQ
  simp only [add_assoc, add_comm, add_left_comm]

private theorem rho_change (b e x y d : R) :
    b * (e + (y * d + d ^ 2)) + y * (x + d) + (x + d) ^ 2 =
      (b * e + y * x + x ^ 2) + (b + 1) * (y * d + d ^ 2) := by
  rw [CharTwo.add_sq]
  ring

theorem rho16 (q : Vector R) (d : R) :
    rho (increment q 16 d) = rho q + (q 0 + q 8 + 1) * kappaQ q d := by
  unfold rho
  rw [eta16]
  exact rho_change (q 0 + q 8) (eta q) (q 16) (q 7) d

private theorem fourth (x d : R) : (x + d) ^ 4 = x ^ 4 + d ^ 4 := by
  rw [show (4 : ℕ) = 2 * 2 by omega, pow_mul, CharTwo.add_sq, CharTwo.add_sq, ← pow_mul, ← pow_mul]

private theorem tau_change (x y g z w t d : R) :
    (x + d) ^ 4 + (g + y ^ 2) * (x + d) ^ 2 + (y * g + 1) * (x + d) +
      z ^ 2 + g * z + w + t =
    (x ^ 4 + (g + y ^ 2) * x ^ 2 + (y * g + 1) * x + z ^ 2 + g * z + w + t) +
      ((y * d + d ^ 2) ^ 2 + g * (y * d + d ^ 2) + d) := by
  rw [fourth, CharTwo.add_sq, CharTwo.add_sq]
  ring

theorem tau16 (q : Vector R) (d : R) : tau (increment q 16 d) = tau q + sigmaQ q d := by
  unfold tau
  exact tau_change (q 16) (q 7) (gamma q) (q 20) (q 18) (q 21) d

theorem a11_16 (q : Vector R) (d : R) : a11 (increment q 16 d) = a11 q + sigmaQ q d := by
  unfold a11
  rw [tau16]
  change q 13 + (tau q + sigmaQ q d) = _
  rw [← add_assoc]

private theorem paired_change (a b c e f d k s : R) :
    a + ((b + k) + (c + d) + (e + s) + (f + d)) = (a + (b + c + e + f)) + (k + s) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem a12_16 (q : Vector R) (d : R) : a12 (increment q 16 d) = a12 q + d := by
  change q 15 + (q 16 + d) = (q 15 + q 16) + d
  rw [add_assoc]

theorem a10_16 (q : Vector R) (d : R) :
    a10 (increment q 16 d) = a10 q + ((q 0 + q 8 + 1) * kappaQ q d + sigmaQ q d) := by
  unfold a10
  rw [rho16, a11_16, a12_16]
  exact paired_change (q 12) (rho q) (q 16) (a11 q) (a12 q) d
    ((q 0 + q 8 + 1) * kappaQ q d) (sigmaQ q d)

private theorem two_changes (a b c e f k s : R) :
    a + ((b + k) + (c + s) + e + f) = (a + (b + c + e + f)) + (k + s) := by ring

theorem a9_16 (q : Vector R) (d : R) :
    a9 (increment q 16 d) = a9 q + ((q 0 + q 8 + 1) * kappaQ q d + sigmaQ q d) := by
  unfold a9
  rw [rho16, a11_16]
  exact two_changes _ _ _ _ _ _ _

private theorem a8_change (a e f h b k s : R) :
    a + (e + k) + (f + ((b + 1) * k + s)) + h = (a + e + f + h) + (b * k + s) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem a8_16 (q : Vector R) (d : R) :
    a8 (increment q 16 d) = a8 q + ((q 0 + q 8) * kappaQ q d + sigmaQ q d) := by
  rw [Char2Degree23TwentyCoordinates.a8_eta, Char2Degree23TwentyCoordinates.a8_eta, eta16, a10_16]
  exact a8_change (q 9) (eta q) (a10 q) (q 18) (q 0 + q 8) (kappaQ q d) (sigmaQ q d)

theorem slots16 (q : Vector R) (d : R) :
    SameRaw (Char2Degree23SixteenWires.shift16 (rawKeys q) d) (rawKeys (increment q 16 d)) := by
  constructor <;>
    simp only [Char2Degree23SixteenWires.shift16, kappa_rawKeys, sigma_rawKeys, A_rawKeys, B_rawKeys] <;>
    rw [rawKeys_core _ _ (by omega) (by omega), rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_16 q d).symm | exact (a9_16 q d).symm |
    exact (a10_16 q d).symm | exact (a11_16 q d).symm | exact (a12_16 q d).symm |
    (change (q 11 + eta q) + kappaQ q d = q 11 + eta (increment q 16 d);
      rw [eta16, add_assoc]) |
    (change (q 7 + q 16) + d = q 7 + (q 16 + d); rw [add_assoc])

theorem increment16_change (q : Vector R) (d : R) :
    output (rawKeys (increment q 16 d)) = output (rawKeys q) + Char2Degree23SixteenFrame.low (rawKeys q) d :=
  Char2Degree23NormalizedPeel.increment (by omega) (slots16 q d) rfl
    (Char2Degree23SixteenFrame.raw_difference (rawKeys q) d)
    (Char2Degree23SixteenFrame.low_degree (rawKeys q) d)

theorem increment16_unit (q : Vector R) (d : R) :
    Char2Degree19InnerTail.UnitDifference (output (rawKeys q))
      (output (rawKeys (increment q 16 d))) 6 d := by
  exact Char2Degree19InnerChanges.unit_difference_of_lower _ _ _ _ _ d
    (Char2Degree23SixteenFrame.sixSlope_monic (rawKeys q))
    (Char2Degree23SixteenFrame.residual_degree (rawKeys q) d) (increment16_change q d)

end FastPoly.Char2Degree23SixteenKeys
