import FastPoly.Examples.Char2Degree23MiddleKeys

/-!
# The supplied q20 key update, with its scalar corrections kept named

This is a direct replay of the inverse's eta/rho/tau formulas. The raw
linear coefficient B and the shared gamma correction are explicitly
identified with normalized coordinates; both are reused by q16.
-/

namespace FastPoly.Char2Degree23TwentyCoordinates

open Char2Degree23Coordinates Char2Degree23HighKeys Char2Degree23LowKeys
  Char2Degree23MiddleKeys

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def B (a : ℕ → R) : R := a 2 + a 6
def gammaRaw (a : ℕ → R) : R := a 2 + a 3 + a 6 + a 7 + a 8 + a 10 + a 16 + 1
def sigma (a : ℕ → R) (d : R) : R := d ^ 2 + gammaRaw a * d
def sigmaQ (q : Vector R) (d : R) : R := d ^ 2 + gamma q * d

def shift20 (a : ℕ → R) (d : R) : ℕ → R
  | 7 => a 7 + d
  | 8 => a 8 + ((B a + 1) * d + sigma a d)
  | 9 => a 9 + ((B a + 1) * d + sigma a d)
  | 10 => a 10 + (B a * d + sigma a d)
  | 11 => a 11 + sigma a d
  | 15 => a 15 + d
  | i => a i

theorem B_rawKeys (q : Vector R) : B (rawKeys q) = q 0 + q 8 := by
  unfold B
  rw [rawKeys_core _ 2 (by omega) (by omega), rawKeys_core _ 6 (by omega) (by omega)]
  rfl

theorem a8_eta (q : Vector R) : a8 q = q 9 + eta q + a10 q + q 18 := by
  unfold a8 eta
  ac_rfl

private theorem gamma_cancel (a b c e f g h j : R) :
    a + b + c + (e + h) + (f + h + j + g) + j + g + 1 =
      a + b + c + f + e + 1 := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]

theorem gammaRaw_rawKeys (q : Vector R) : gammaRaw (rawKeys q) = gamma q := by
  unfold gammaRaw
  rw [rawKeys_core _ 2 (by omega) (by omega), rawKeys_core _ 3 (by omega) (by omega),
    rawKeys_core _ 6 (by omega) (by omega), rawKeys_core _ 7 (by omega) (by omega),
    rawKeys_core _ 8 (by omega) (by omega), rawKeys_core _ 10 (by omega) (by omega),
    rawKeys_core _ 16 (by omega) (by omega)]
  change q 0 + (q 3 + (q 5 + q 6)) + q 8 + (q 11 + eta q) + a8 q + a10 q + q 18 + 1 = _
  rw [a8_eta, gamma_cancel]
  unfold gamma
  ac_rfl

theorem sigma_rawKeys (q : Vector R) (d : R) : sigma (rawKeys q) d = sigmaQ q d := by
  unfold sigma sigmaQ
  rw [gammaRaw_rawKeys]

theorem eta20 (q : Vector R) (d : R) : eta (increment q 20 d) = eta q + d := by
  change q 7 * q 16 + q 16 ^ 2 + (q 20 + d) = _
  rw [← add_assoc]
  rfl

private theorem rho_linear (b e k d : R) : b * (e + d) + k = (b * e + k) + b * d := by ring

theorem rho20 (q : Vector R) (d : R) :
    rho (increment q 20 d) = rho q + (q 0 + q 8) * d := by
  unfold rho
  rw [eta20]
  change (q 0 + q 8) * (eta q + d) + q 7 * q 16 + q 16 ^ 2 = _
  ring

private theorem tau_change (base t g w c d : R) :
    base + (t + d) ^ 2 + g * (t + d) + w + c =
      (base + t ^ 2 + g * t + w + c) + (d ^ 2 + g * d) := by
  rw [CharTwo.add_sq]
  ring

theorem tau20 (q : Vector R) (d : R) : tau (increment q 20 d) = tau q + sigmaQ q d := by
  unfold tau
  change q 16 ^ 4 + (gamma q + q 7 ^ 2) * q 16 ^ 2 +
    (q 7 * gamma q + 1) * q 16 + (q 20 + d) ^ 2 +
    gamma q * (q 20 + d) + q 18 + q 21 = _
  exact tau_change _ _ _ _ _ _

theorem a11_20 (q : Vector R) (d : R) : a11 (increment q 20 d) = a11 q + sigmaQ q d := by
  unfold a11
  rw [tau20]
  change q 13 + (tau q + sigmaQ q d) = _
  rw [← add_assoc]

theorem a10_20 (q : Vector R) (d : R) :
    a10 (increment q 20 d) = a10 q + ((q 0 + q 8) * d + sigmaQ q d) := by
  unfold a10
  rw [rho20, a11_20]
  change q 12 + ((rho q + (q 0 + q 8) * d) + q 16 + (a11 q + sigmaQ q d) + a12 q) = _
  ac_rfl

private theorem plus_unit (a b c e f g d s : R) :
    a + ((b + g * d) + (c + s) + (e + d) + f) =
      (a + (b + c + e + f)) + ((g + 1) * d + s) := by ring

theorem a9_20 (q : Vector R) (d : R) :
    a9 (increment q 20 d) = a9 q + (((q 0 + q 8) + 1) * d + sigmaQ q d) := by
  unfold a9
  rw [rho20, a11_20]
  change q 10 + ((rho q + (q 0 + q 8) * d) + (a11 q + sigmaQ q d) + (q 20 + d) + q 18) = _
  exact plus_unit _ _ _ _ _ _ _ _

theorem a8_20 (q : Vector R) (d : R) :
    a8 (increment q 20 d) = a8 q + (((q 0 + q 8) + 1) * d + sigmaQ q d) := by
  rw [a8_eta, a8_eta, eta20, a10_20]
  change q 9 + (eta q + d) + (a10 q + ((q 0 + q 8) * d + sigmaQ q d)) + q 18 = _
  ring

theorem slots20 (q : Vector R) (d : R) :
    SameRaw (shift20 (rawKeys q) d) (rawKeys (increment q 20 d)) := by
  constructor <;> simp only [shift20, B_rawKeys, sigma_rawKeys] <;>
    rw [rawKeys_core _ _ (by omega) (by omega), rawKeys_core _ _ (by omega) (by omega)]
  all_goals first | rfl | exact (a8_20 q d).symm | exact (a9_20 q d).symm |
    exact (a10_20 q d).symm | exact (a11_20 q d).symm |
    (change (q 11 + eta q) + d = q 11 + eta (increment q 20 d);
      rw [eta20, add_assoc])

end FastPoly.Char2Degree23TwentyCoordinates

