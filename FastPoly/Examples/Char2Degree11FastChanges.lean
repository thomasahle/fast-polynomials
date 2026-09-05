import FastPoly.Examples.Char2Degree11FastSignature

/-! Local changes of the supplied five-coefficient signature.
The final product B*J is never opened; scalar identities below prove the
actual unit slopes, not just a Jacobian certificate. -/

namespace FastPoly.Char2Degree11Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

def increment (q : Keys R) (i : Fin 11) (delta : R) : Keys R :=
  Function.update q i (q i + delta)

/-- The entire possible difference of two supplied J wires. -/
noncomputable def lower4 (c4 c3 c2 c1 c0 : R) : R[X] :=
  C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

theorem lower4_degree (c4 c3 c2 c1 c0 : R) :
    (lower4 c4 c3 c2 c1 c0).natDegree ≤ 4 := by
  have h4 : (C c4 * X ^ 4 : R[X]).natDegree ≤ 4 := natDegree_C_mul_X_pow_le _ _
  have h3 : (C c3 * X ^ 3 : R[X]).natDegree ≤ 4 :=
    (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have h2 : (C c2 * X ^ 2 : R[X]).natDegree ≤ 4 :=
    (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have h1 : (C c1 * X : R[X]).natDegree ≤ 4 :=
    (Char2Degree15Fast.mul_bound (natDegree_C c1).le natDegree_X_le).trans (by omega)
  have h0 : (C c0 : R[X]).natDegree ≤ 4 := (natDegree_C c0).le.trans (by omega)
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le h4 h3) h2) h1) h0

private theorem signature_difference (a4 a3 a2 a1 a0 b4 b3 b2 b1 b0 : R) :
    signature b4 b3 b2 b1 b0 + signature a4 a3 a2 a1 a0 =
      lower4 (b4 + a4) (b3 + a3) (b2 + a2) (b1 + a1) (b0 + a0) := by
  unfold signature lower4
  simp only [map_add]
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

/-- The fixed X^8, X^6, X^5 terms cancel, independently of the keys. -/
theorem J_difference_degree (q q' : Keys R) : (J q' + J q).natDegree ≤ 4 := by
  rw [J_signature, J_signature, signature_difference]
  exact lower4_degree ..

private theorem signature_change (a4 a3 a2 a1 a0 d4 d3 d2 d1 d0 delta : R) :
    signature (a4 + delta * d4) (a3 + delta * d3) (a2 + delta * d2)
      (a1 + delta * d1) (a0 + delta * d0) =
    signature a4 a3 a2 a1 a0 + C delta * lower4 d4 d3 d2 d1 d0 := by
  unfold signature lower4
  simp only [map_add, map_mul]
  ring

theorem J_change (q q' : Keys R) (delta d4 d3 d2 d1 d0 : R)
    (h4 : k4 q' = k4 q + delta * d4)
    (h3 : k3 q' = k3 q + delta * d3)
    (h2 : k2 q' = k2 q + delta * d2)
    (h1 : k1 q' = k1 q + delta * d1)
    (h0 : k0 q' = k0 q + delta * d0) :
    J q' = J q + C delta * lower4 d4 d3 d2 d1 d0 := by
  rw [J_signature q', h4, h3, h2, h1, h0, signature_change, ← J_signature q]

private theorem k4_increment3 (q : Keys R) (delta : R) :
    k4 (increment q 3 delta) = k4 q + delta * (1) := by
  change (1 + q 0 + (q 3 + delta) + q 0 ^ 2) = (1 + q 0 + q 3 + q 0 ^ 2) + delta * (1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k3_increment3 (q : Keys R) (delta : R) :
    k3 (increment q 3 delta) = k3 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k2_increment3 (q : Keys R) (delta : R) :
    k2 (increment q 3 delta) = k2 q + delta * (1 + q 0) := by
  change ((q 3 + delta) + q 4 + q 5 + q 0 * q 1 + q 0 * ((q 3 + delta) + q 4) + q 1 ^ 2) = (q 3 + q 4 + q 5 + q 0 * q 1 + q 0 * (q 3 + q 4) + q 1 ^ 2) + delta * (1 + q 0)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k1_increment3 (q : Keys R) (delta : R) :
    k1 (increment q 3 delta) = k1 q + delta * (q 1) := by
  change (q 6 + q 1 * ((q 3 + delta) + q 4)) = (q 6 + q 1 * (q 3 + q 4)) + delta * (q 1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k0_increment3 (q : Keys R) (delta : R) :
    k0 (increment q 3 delta) = k0 q + delta * (q 5 + q 0 * q 1) := by
  change (q 7 + ((q 3 + delta) + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 + q 0 * q 1 * ((q 3 + delta) + q 4) + (q 0 * q 1) ^ 2) = (q 7 + (q 3 + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) + delta * (q 5 + q 0 * q 1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k4_increment4 (q : Keys R) (delta : R) :
    k4 (increment q 4 delta) = k4 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k3_increment4 (q : Keys R) (delta : R) :
    k3 (increment q 4 delta) = k3 q + delta * (1) := by
  change (q 1 + (q 4 + delta)) = (q 1 + q 4) + delta * (1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k2_increment4 (q : Keys R) (delta : R) :
    k2 (increment q 4 delta) = k2 q + delta * (1 + q 0) := by
  change (q 3 + (q 4 + delta) + q 5 + q 0 * q 1 + q 0 * (q 3 + (q 4 + delta)) + q 1 ^ 2) = (q 3 + q 4 + q 5 + q 0 * q 1 + q 0 * (q 3 + q 4) + q 1 ^ 2) + delta * (1 + q 0)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k1_increment4 (q : Keys R) (delta : R) :
    k1 (increment q 4 delta) = k1 q + delta * (q 1) := by
  change (q 6 + q 1 * (q 3 + (q 4 + delta))) = (q 6 + q 1 * (q 3 + q 4)) + delta * (q 1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k0_increment4 (q : Keys R) (delta : R) :
    k0 (increment q 4 delta) = k0 q + delta * (q 5 + q 6 + q 0 * q 1) := by
  change (q 7 + (q 3 + (q 4 + delta)) * q 5 + (q 4 + delta) * q 6 + q 5 ^ 2 + q 0 * q 1 * (q 3 + (q 4 + delta)) + (q 0 * q 1) ^ 2) = (q 7 + (q 3 + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) + delta * (q 5 + q 6 + q 0 * q 1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k4_increment5 (q : Keys R) (delta : R) :
    k4 (increment q 5 delta) = k4 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k3_increment5 (q : Keys R) (delta : R) :
    k3 (increment q 5 delta) = k3 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k2_increment5 (q : Keys R) (delta : R) :
    k2 (increment q 5 delta) = k2 q + delta * (1) := by
  change (q 3 + q 4 + (q 5 + delta) + q 0 * q 1 + q 0 * (q 3 + q 4) + q 1 ^ 2) = (q 3 + q 4 + q 5 + q 0 * q 1 + q 0 * (q 3 + q 4) + q 1 ^ 2) + delta * (1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k1_increment5 (q : Keys R) (delta : R) :
    k1 (increment q 5 delta) = k1 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k0_increment5 (q : Keys R) (delta : R) :
    k0 (increment q 5 delta) = k0 q + delta * (q 3 + q 4 + delta) := by
  change (q 7 + (q 3 + q 4) * (q 5 + delta) + q 4 * q 6 + (q 5 + delta) ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) = (q 7 + (q 3 + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) + delta * (q 3 + q 4 + delta)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k4_increment6 (q : Keys R) (delta : R) :
    k4 (increment q 6 delta) = k4 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k3_increment6 (q : Keys R) (delta : R) :
    k3 (increment q 6 delta) = k3 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k2_increment6 (q : Keys R) (delta : R) :
    k2 (increment q 6 delta) = k2 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k1_increment6 (q : Keys R) (delta : R) :
    k1 (increment q 6 delta) = k1 q + delta * (1) := by
  change ((q 6 + delta) + q 1 * (q 3 + q 4)) = (q 6 + q 1 * (q 3 + q 4)) + delta * (1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k0_increment6 (q : Keys R) (delta : R) :
    k0 (increment q 6 delta) = k0 q + delta * (q 4) := by
  change (q 7 + (q 3 + q 4) * q 5 + q 4 * (q 6 + delta) + q 5 ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) = (q 7 + (q 3 + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) + delta * (q 4)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

private theorem k4_increment7 (q : Keys R) (delta : R) :
    k4 (increment q 7 delta) = k4 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k3_increment7 (q : Keys R) (delta : R) :
    k3 (increment q 7 delta) = k3 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k2_increment7 (q : Keys R) (delta : R) :
    k2 (increment q 7 delta) = k2 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k1_increment7 (q : Keys R) (delta : R) :
    k1 (increment q 7 delta) = k1 q + delta * (0) := by
  simp only [mul_zero, add_zero]
  rfl

private theorem k0_increment7 (q : Keys R) (delta : R) :
    k0 (increment q 7 delta) = k0 q + delta * (1) := by
  change ((q 7 + delta) + (q 3 + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) = (q 7 + (q 3 + q 4) * q 5 + q 4 * q 6 + q 5 ^ 2 + q 0 * q 1 * (q 3 + q 4) + (q 0 * q 1) ^ 2) + delta * (1)
  ring_nf <;> simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

noncomputable def slope3 (q : Keys R) : R[X] :=
  X ^ 4 + C (1 + q 0) * X ^ 2 + C (q 1) * X + C (q 5 + q 0 * q 1)
noncomputable def slope4 (q : Keys R) : R[X] :=
  X ^ 3 + C (1 + q 0) * X ^ 2 + C (q 1) * X + C (q 5 + q 6 + q 0 * q 1)
noncomputable def slope5 (q : Keys R) (delta : R) : R[X] :=
  X ^ 2 + C (q 3 + q 4 + delta)
noncomputable def slope6 (q : Keys R) : R[X] := X + C (q 4)

theorem J_increment3 (q : Keys R) (delta : R) :
    J (increment q 3 delta) = J q + C delta * (slope3 q) := by
  have h := J_change q (increment q 3 delta) delta
    (1) (0) (1 + q 0) (q 1) (q 5 + q 0 * q 1)
    (k4_increment3 q delta) (k3_increment3 q delta) (k2_increment3 q delta)
    (k1_increment3 q delta) (k0_increment3 q delta)
  simpa only [lower4, slope3, map_zero, map_one, zero_mul, one_mul, add_zero, zero_add] using h

theorem J_increment4 (q : Keys R) (delta : R) :
    J (increment q 4 delta) = J q + C delta * (slope4 q) := by
  have h := J_change q (increment q 4 delta) delta
    (0) (1) (1 + q 0) (q 1) (q 5 + q 6 + q 0 * q 1)
    (k4_increment4 q delta) (k3_increment4 q delta) (k2_increment4 q delta)
    (k1_increment4 q delta) (k0_increment4 q delta)
  simpa only [lower4, slope4, map_zero, map_one, zero_mul, one_mul, add_zero, zero_add] using h

theorem J_increment5 (q : Keys R) (delta : R) :
    J (increment q 5 delta) = J q + C delta * (slope5 q delta) := by
  have h := J_change q (increment q 5 delta) delta
    (0) (0) (1) (0) (q 3 + q 4 + delta)
    (k4_increment5 q delta) (k3_increment5 q delta) (k2_increment5 q delta)
    (k1_increment5 q delta) (k0_increment5 q delta)
  simpa only [lower4, slope5, map_zero, map_one, zero_mul, one_mul, add_zero, zero_add] using h

theorem J_increment6 (q : Keys R) (delta : R) :
    J (increment q 6 delta) = J q + C delta * (slope6 q) := by
  have h := J_change q (increment q 6 delta) delta
    (0) (0) (0) (1) (q 4)
    (k4_increment6 q delta) (k3_increment6 q delta) (k2_increment6 q delta)
    (k1_increment6 q delta) (k0_increment6 q delta)
  simpa only [lower4, slope6, map_zero, map_one, zero_mul, one_mul, add_zero, zero_add] using h

theorem J_increment7 (q : Keys R) (delta : R) :
    J (increment q 7 delta) = J q + C delta * (1) := by
  have h := J_change q (increment q 7 delta) delta
    (0) (0) (0) (0) (1)
    (k4_increment7 q delta) (k3_increment7 q delta) (k2_increment7 q delta)
    (k1_increment7 q delta) (k0_increment7 q delta)
  simpa only [lower4, map_zero, map_one, zero_mul, one_mul, add_zero, zero_add] using h

theorem J_increment2 (q : Keys R) (delta : R) :
    J (increment q 2 delta) = J q := by
  rw [J_signature, J_signature]
  rfl

theorem J_increment8 (q : Keys R) (delta : R) :
    J (increment q 8 delta) = J q := by
  rw [J_signature, J_signature]
  rfl

theorem J_increment9 (q : Keys R) (delta : R) :
    J (increment q 9 delta) = J q := by
  rw [J_signature, J_signature]
  rfl

theorem J_increment10 (q : Keys R) (delta : R) :
    J (increment q 10 delta) = J q := by
  rw [J_signature, J_signature]
  rfl

end FastPoly.Char2Degree11Fast

