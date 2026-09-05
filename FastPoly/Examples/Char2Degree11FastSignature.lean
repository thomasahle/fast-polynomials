import FastPoly.Examples.Char2Degree11FastCore

/-! The supplied degree-eight wire's small coefficient signature.
Every ring calculation below has independent scalar or wire arguments. The
final degree-eleven product `B * J` is never expanded. -/

namespace FastPoly.Char2Degree11Fast

set_option maxHeartbeats 20000

open Polynomial

variable {R : Type*} [CommRing R] [CharP R 2]

private theorem square_head (x b d : R) :
    (x ^ 2 + b) * (x + x ^ 2 + (d + b)) =
      x ^ 4 + x ^ 3 + d * x ^ 2 + b * x + b * (d + b) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem z_form (q : Keys R) :
    z q = X ^ 4 + X ^ 3 + C (q 8) * X ^ 2 + C (q 9) * X + C (z0 q) := by
  unfold z y z0
  simp only [map_add, map_mul]
  exact square_head X (C (q 9)) (C (q 8))

private theorem cubic_head (x p r : R) :
    (x + p) * (x ^ 2 + r) = x ^ 3 + p * x ^ 2 + r * x + p * r := by ring

theorem u_form (q : Keys R) :
    u q = X ^ 3 + C (q 0) * X ^ 2 + C (q 1) * X + C (q 0 * q 1) := by
  unfold u y
  rw [map_mul]
  exact cubic_head X (C (q 0)) (C (q 1))

noncomputable def quartic (a b c : R) : R[X] :=
  X ^ 4 + C a * X ^ 2 + C b * X + C c

private theorem merge_heads (x p r b d c : R) :
    (x ^ 4 + x ^ 3 + d * x ^ 2 + b * x + c) +
      (x ^ 3 + p * x ^ 2 + r * x + p * r) =
      x ^ 4 + (d + p) * x ^ 2 + (b + r) * x + (c + p * r) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem H_form (q : Keys R) : H q = quartic (h2 q) (h1 q) (h0 q) := by
  rw [H, z_form, u_form]
  unfold quartic h2 h1 h0
  simp only [map_add, map_mul]
  exact merge_heads X (C (q 0)) (C (q 1)) (C (q 9)) (C (q 8)) (C (z0 q))

noncomputable def shape5 (c4 c3 c2 c1 c0 : R) : R[X] :=
  X ^ 5 + C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

noncomputable def shape8 (c4 c3 c2 c1 c0 : R) : R[X] :=
  X ^ 8 + X ^ 6 + C c4 * X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

private theorem shifted_quartic (x a d b c f : R) :
    (x + a) * (x ^ 4 + x ^ 3 + d * x ^ 2 + b * x + c + f) =
      x ^ 5 + (1 + a) * x ^ 4 + (d + a) * x ^ 3 + (b + a * d) * x ^ 2 +
        (c + f + a * b) * x + a * (c + f) := by ring

theorem t_form (q : Keys R) :
    t q = shape5 (1 + a2 q) (q 8 + a2 q) (q 9 + a2 q * q 8)
      (z0 q + a3 q + a2 q * q 9) (a2 q * (z0 q + a3 q)) := by
  rw [t, z_form]
  unfold shape5
  simp only [map_add, map_mul, map_one]
  exact shifted_quartic X (C (a2 q)) (C (q 8)) (C (q 9)) (C (z0 q)) (C (a3 q))

private theorem quartic_product (x a b c d e : R) :
    (x ^ 4 + a * x ^ 2 + b * x + c + d) *
      (x ^ 2 + (x ^ 4 + a * x ^ 2 + b * x + c) + e) =
      x ^ 8 + x ^ 6 + (a ^ 2 + a + (d + e)) * x ^ 4 + b * x ^ 3 +
        (b ^ 2 + c + (d + e) * a + d) * x ^ 2 + (d + e) * b * x +
          (c + d) * (c + e) := by
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero, zero_add]

theorem quartic_product_shape (a b c d e : R) :
    (quartic a b c + C d) * (X ^ 2 + quartic a b c + C e) =
      shape8 (a ^ 2 + a + (d + e)) b (b ^ 2 + c + (d + e) * a + d)
        ((d + e) * b) ((c + d) * (c + e)) := by
  unfold quartic shape8
  simp only [map_add, map_mul, map_pow]
  exact quartic_product X (C a) (C b) (C c) (C d) (C e)

theorem v_form (q : Keys R) :
    v q = shape8 (h2 q ^ 2 + h2 q + sigma q) (h1 q)
      (h1 q ^ 2 + h0 q + sigma q * h2 q + a6 q)
      (sigma q * h1 q) ((h0 q + a6 q) * (h0 q + a7 q)) := by
  rw [v, H_form]
  change (quartic (h2 q) (h1 q) (h0 q) + C (a6 q)) *
    (X ^ 2 + quartic (h2 q) (h1 q) (h0 q) + C (a7 q)) = _
  rw [quartic_product_shape, offsets_sum]

theorem row4_pivot (q : Keys R) :
    (1 + a2 q) + (h2 q ^ 2 + h2 q + sigma q) = k4 q := by
  unfold a2 h2 sigma k4
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

theorem row3_pivot (q : Keys R) : (q 8 + a2 q) + h1 q = k3 q := by
  unfold a2 h1 k3
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

private theorem pivot_two (a b c d e k : R) :
    (a + b) + (c + d + e + (k + (a + b + c + d + e))) = k := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem row2_pivot (q : Keys R) :
    (q 9 + a2 q * q 8) + (h1 q ^ 2 + h0 q + sigma q * h2 q + a6 q) = k2 q := by
  rw [a6]
  exact pivot_two (q 9) (a2 q * q 8) (h1 q ^ 2) (h0 q) (sigma q * h2 q) (k2 q)

private theorem pivot_one (a b c k : R) :
    (a + (k + (a + b + c)) + b) + c = k := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem row1_pivot (q : Keys R) :
    (z0 q + a3 q + a2 q * q 9) + sigma q * h1 q = k1 q := by
  rw [a3]
  exact pivot_one (z0 q) (a2 q * q 9) (sigma q * h1 q) (k1 q)

theorem row0_pivot (q : Keys R) :
    a2 q * (z0 q + a3 q) + (h0 q + a6 q) * (h0 q + a7 q) + a9 q = k0 q := by
  rw [a9, add_comm (k0 q), CharTwo.add_cancel_left]

/-- Only five lower coefficients vary; coefficients 7, 6, and 5 are fixed. -/
noncomputable def signature (c4 c3 c2 c1 c0 : R) : R[X] :=
  X ^ 8 + X ^ 6 + X ^ 5 + C c4 * X ^ 4 + C c3 * X ^ 3 +
    C c2 * X ^ 2 + C c1 * X + C c0

private theorem join_shapes (t4 t3 t2 t1 t0 v4 v3 v2 v1 v0 c : R) :
    shape5 t4 t3 t2 t1 t0 + shape8 v4 v3 v2 v1 v0 + C c =
      signature (t4 + v4) (t3 + v3) (t2 + v2) (t1 + v1) (t0 + v0 + c) := by
  unfold shape5 shape8 signature
  simp only [map_add]
  ring

/-- The existing nonlinear offsets install this small signature literally. -/
theorem J_signature (q : Keys R) :
    J q = signature (k4 q) (k3 q) (k2 q) (k1 q) (k0 q) := by
  rw [J, t_form, v_form, join_shapes, row4_pivot, row3_pivot,
    row2_pivot, row1_pivot, row0_pivot]

end FastPoly.Char2Degree11Fast
