import FastPoly.Examples.Char2Degree23HighKeys

/-! Named scalar updates for the six supplied middle key coordinates. -/

namespace FastPoly.Char2Degree23MiddleCoordinates

open Char2Degree23Coordinates Char2Degree23HighKeys

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2]

private theorem tau_linear (g d x y z w t : R) :
    x ^ 4 + ((g + d) + y ^ 2) * x ^ 2 + (y * (g + d) + 1) * x +
      z ^ 2 + (g + d) * z + w + t =
    (x ^ 4 + (g + y ^ 2) * x ^ 2 + (y * g + 1) * x + z ^ 2 + g * z + w + t) +
      d * (y * x + x ^ 2 + z) := by ring

theorem gamma8 (q : Vector R) (d : R) : gamma (increment q 8 d) = gamma q + d := by
  dsimp [gamma, increment, Function.update]
  simp only [add_assoc, add_comm, add_left_comm]

theorem gamma9 (q : Vector R) (d : R) : gamma (increment q 9 d) = gamma q + d := by
  dsimp [gamma, increment, Function.update]
  simp only [add_assoc, add_comm, add_left_comm]

theorem gamma11 (q : Vector R) (d : R) : gamma (increment q 11 d) = gamma q + d := by
  dsimp [gamma, increment, Function.update]
  simp only [add_assoc, add_comm, add_left_comm]

theorem rho8 (q : Vector R) (d : R) : rho (increment q 8 d) = rho q + d * eta q := by
  change (q 0 + (q 8 + d)) * eta q + q 7 * q 16 + q 16 ^ 2 = _
  rw [← add_assoc, add_mul]
  change ((q 0 + q 8) * eta q + d * eta q) + q 7 * q 16 + q 16 ^ 2 = _
  unfold rho
  simp only [add_assoc, add_comm, add_left_comm]

theorem tau8 (q : Vector R) (d : R) : tau (increment q 8 d) = tau q + d * eta q := by
  unfold tau
  rw [gamma8]
  exact tau_linear (gamma q) d (q 16) (q 7) (q 20) (q 18) (q 21)

theorem tau9 (q : Vector R) (d : R) : tau (increment q 9 d) = tau q + d * eta q := by
  unfold tau
  rw [gamma9]
  exact tau_linear (gamma q) d (q 16) (q 7) (q 20) (q 18) (q 21)

theorem tau11 (q : Vector R) (d : R) : tau (increment q 11 d) = tau q + d * eta q := by
  unfold tau
  rw [gamma11]
  exact tau_linear (gamma q) d (q 16) (q 7) (q 20) (q 18) (q 21)

theorem a11_8 (q : Vector R) (d : R) : a11 (increment q 8 d) = a11 q + d * eta q := by
  unfold a11
  rw [tau8]
  change q 13 + (tau q + d * eta q) = _
  rw [← add_assoc]

theorem a10_8 (q : Vector R) (d : R) : a10 (increment q 8 d) = a10 q := by
  unfold a10
  rw [rho8, a11_8]
  change q 12 + ((rho q + d * eta q) + q 16 + (a11 q + d * eta q) + a12 q) = _
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem a9_8 (q : Vector R) (d : R) : a9 (increment q 8 d) = a9 q := by
  unfold a9
  rw [rho8, a11_8]
  change q 10 + ((rho q + d * eta q) + (a11 q + d * eta q) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem a8_8 (q : Vector R) (d : R) : a8 (increment q 8 d) = a8 q := by
  unfold a8
  rw [a10_8]
  rfl

theorem a11_9 (q : Vector R) (d : R) : a11 (increment q 9 d) = a11 q + d * eta q := by
  unfold a11
  rw [tau9]
  change q 13 + (tau q + d * eta q) = _
  rw [← add_assoc]

theorem a10_9 (q : Vector R) (d : R) : a10 (increment q 9 d) = a10 q + d * eta q := by
  unfold a10
  rw [a11_9]
  change q 12 + (rho q + q 16 + (a11 q + d * eta q) + a12 q) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a9_9 (q : Vector R) (d : R) : a9 (increment q 9 d) = a9 q + d * eta q := by
  unfold a9
  rw [a11_9]
  change q 10 + (rho q + (a11 q + d * eta q) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a8_9 (q : Vector R) (d : R) : a8 (increment q 9 d) = (a8 q + d * eta q) + d := by
  unfold a8
  rw [a10_9]
  change (q 9 + d) + (q 16 ^ 2 + q 7 * q 16 + (a10 q + d * eta q) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a11_11 (q : Vector R) (d : R) : a11 (increment q 11 d) = a11 q + d * eta q := by
  unfold a11
  rw [tau11]
  change q 13 + (tau q + d * eta q) = _
  rw [← add_assoc]

theorem a10_11 (q : Vector R) (d : R) : a10 (increment q 11 d) = a10 q + d * eta q := by
  unfold a10
  rw [a11_11]
  change q 12 + (rho q + q 16 + (a11 q + d * eta q) + a12 q) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a9_11 (q : Vector R) (d : R) : a9 (increment q 11 d) = a9 q + d * eta q := by
  unfold a9
  rw [a11_11]
  change q 10 + (rho q + (a11 q + d * eta q) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a8_11 (q : Vector R) (d : R) : a8 (increment q 11 d) = a8 q + d * eta q := by
  unfold a8
  rw [a10_11]
  change q 9 + (q 16 ^ 2 + q 7 * q 16 + (a10 q + d * eta q) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a9_10 (q : Vector R) (d : R) : a9 (increment q 10 d) = a9 q + d := by
  change (q 10 + d) + (rho q + a11 q + q 20 + q 18) = _
  unfold a9
  simp only [add_assoc, add_comm, add_left_comm]

theorem a10_12 (q : Vector R) (d : R) : a10 (increment q 12 d) = a10 q + d := by
  change (q 12 + d) + (rho q + q 16 + a11 q + a12 q) = _
  unfold a10
  simp only [add_assoc, add_comm, add_left_comm]

theorem a8_12 (q : Vector R) (d : R) : a8 (increment q 12 d) = a8 q + d := by
  unfold a8
  rw [a10_12]
  change q 9 + (q 16 ^ 2 + q 7 * q 16 + (a10 q + d) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a11_13 (q : Vector R) (d : R) : a11 (increment q 13 d) = a11 q + d := by
  change (q 13 + d) + tau q = _
  unfold a11
  simp only [add_assoc, add_comm, add_left_comm]

theorem a10_13 (q : Vector R) (d : R) : a10 (increment q 13 d) = a10 q + d := by
  unfold a10
  rw [a11_13]
  change q 12 + (rho q + q 16 + (a11 q + d) + a12 q) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a9_13 (q : Vector R) (d : R) : a9 (increment q 13 d) = a9 q + d := by
  unfold a9
  rw [a11_13]
  change q 10 + (rho q + (a11 q + d) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

theorem a8_13 (q : Vector R) (d : R) : a8 (increment q 13 d) = a8 q + d := by
  unfold a8
  rw [a10_13]
  change q 9 + (q 16 ^ 2 + q 7 * q 16 + (a10 q + d) + q 20 + q 18) = _
  simp only [add_assoc, add_comm, add_left_comm]

end FastPoly.Char2Degree23MiddleCoordinates
