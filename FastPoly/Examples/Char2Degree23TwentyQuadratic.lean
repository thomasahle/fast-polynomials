import FastPoly.Examples.Char2Degree23TwentyCoordinates

/-!
# The monic quadratic remaining in the supplied q20 decoder step

The common high column cancels with ell to a named affine polynomial.
Its slope is exactly gammaRaw, the scalar used in the supplied sigma
correction. These are local wire identities, not a circuit expansion.
-/

namespace FastPoly.Char2Degree23TwentyQuadratic

open Polynomial Char2Degree23TwentyCoordinates Char2Degree23MiddleFrame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

noncomputable def L (a : ℕ → R) : R[X] := X + C (a 6)
noncomputable def affineRest (a : ℕ → R) : R[X] :=
  (X + C (a 2)) * C (a 3) + C (a 14) +
    C (B a + 1) * (X + C (a 8 + a 9)) + C (B a * a 11)
noncomputable def M (a : ℕ → R) : R[X] :=
  L a * (X + C (a 7 + a 8 + a 10)) + affineRest a
def xi (a : ℕ → R) : R :=
  a 6 * (a 7 + a 8 + a 10) + a 2 * a 3 + a 14 +
    (B a + 1) * (a 8 + a 9) + B a * a 11 + a 16 * a 6

theorem M_expanded (a : ℕ → R) :
    M a = L a * (X + C (a 7) + C (a 8) + C (a 10)) +
      (X + C (a 2)) * C (a 3) + C (a 14) +
      C (B a + 1) * (X + C (a 8) + C (a 9)) + C (B a) * C (a 11) := by
  simp only [M, affineRest, map_add, map_mul, add_assoc]

private theorem three_eq_one : (3 : R) = 1 := by
  calc
    (3 : R) = 1 + (1 + 1) := by ring
    _ = 1 := by rw [CharTwo.add_self_eq_zero, add_zero]

private theorem cancel_quadratics (x a b c d e f g h j t : R) :
    ((x + c) * (x + d + e + f) +
      ((x + a) * b + g + (a + c + 1) * (x + e + h) + (a + c) * j)) +
      (x + t) * (x + c) =
    (a + b + c + d + e + f + t + 1) * x +
      (c * (d + e + f) + a * b + g + (a + c + 1) * (e + h) + (a + c) * j + t * c) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, three_eq_one, mul_zero, mul_one, add_zero, zero_add]

theorem M_add_ell (a : ℕ → R) :
    M a + ellLinear a * L a = C (gammaRaw a) * X + C (xi a) := by
  unfold M affineRest L ellLinear gammaRaw xi B
  simp only [map_add, map_mul, map_one]
  have he := cancel_quadratics (X : R[X]) (C (a 2)) (C (a 3)) (C (a 6))
    (C (a 7)) (C (a 8)) (C (a 10)) (C (a 14)) (C (a 9)) (C (a 11)) (C (a 16))
  simpa only [add_assoc] using he

theorem L_monic (a : ℕ → R) : IsMonicOfDegree (L a) 1 :=
  isMonicOfDegree_X_add_one (a 6)

private theorem C_le (c : R) : (C c).natDegree ≤ 1 := by rw [natDegree_C]; omega

theorem affineRest_degree (a : ℕ → R) : (affineRest a).natDegree ≤ 1 := by
  have h1 : ((X + C (a 2)) * C (a 3)).natDegree ≤ 1 := by
    apply natDegree_mul_le.trans
    rw [(isMonicOfDegree_X_add_one (a 2)).natDegree_eq, natDegree_C]
  have h2 : (C (B a + 1) * (X + C (a 8 + a 9))).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans (isMonicOfDegree_X_add_one (a 8 + a 9)).natDegree_eq.le
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le h1 (C_le _)) h2) (C_le _)

theorem M_monic (a : ℕ → R) : IsMonicOfDegree (M a) 2 :=
  ((L_monic a).mul (isMonicOfDegree_X_add_one (a 7 + a 8 + a 10))).add_right
    ((affineRest_degree a).trans_lt (by omega))

end FastPoly.Char2Degree23TwentyQuadratic
