import FastPoly.Examples.Char2Degree19InnerDirect

/-!
# The degree-19 crown's q8 seam pivot

The supplied q8 shift changes `a3,a7` by delta and `a15` by delta²+delta.
Its apparently higher-degree changes cancel in two named factors. The
remaining leading term is `delta * H * J` of degree seven; the remainder
has degree at most five. The algebraic lemmas below take opaque polynomial
inputs and never expand those polynomials into the nineteen original keys.
-/

namespace FastPoly.Char2Degree19InnerSeam

set_option maxHeartbeats 20000

open Polynomial Char2Decoder Char2Degree19Crown Char2Degree19InnerTail
open Char2Degree19InnerChanges Char2Degree19InnerDirect

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

def shift8 (a : ℕ → R) (delta : R) : ℕ → R
  | 3 => a 3 + delta
  | 7 => a 7 + delta
  | 15 => a 15 + (delta ^ 2 + delta)
  | j => a j

noncomputable def linear (a : ℕ → R) : R[X] := X + C (a 2)
noncomputable def quartic (a : ℕ → R) : R[X] := X + z a + C (a 6)
noncomputable def otherQuartic (a : ℕ → R) : R[X] := z a + C (a 7)
noncomputable def b0 (a : ℕ → R) : R[X] := linear a + 1
noncomputable def e (a : ℕ → R) : R[X] := C (a 6) + C (a 7) + C (a 2) + 1
noncomputable def j (a : ℕ → R) : R[X] :=
  s a + X + y + linear a * (C (a 3) + C (a 7)) +
    C (a 7) + C (a 8) + C (a 14) + C (a 15)
noncomputable def slope8 (a : ℕ → R) : R[X] := quartic a * j a

noncomputable def remainder8 (a : ℕ → R) (delta : R) : R[X] :=
  C delta ^ 2 * quartic a * (e a + C delta) +
    C delta * C (a 14) * (b0 a + C delta) +
    uCorrection a (C delta * linear a)

private theorem square_affine_update (v dv m dm q k : R[X]) :
    (v + dv) ^ 2 + (m + dm) * (v + dv) + (q + k * dm) =
      (v ^ 2 + m * v + q) + (dv ^ 2 + m * dv + dm * v + dm * dv + k * dm) := by
  rw [CharTwo.add_sq, add_mul, mul_add, mul_add]
  simp only [add_assoc, add_comm, add_left_comm]

private theorem linear_terms (m d h b₀ b a : R[X]) :
    m * (d * h) + (d * b₀) * (h * b) + a * (d * h) =
      d * (h * (m + b₀ * b + a)) := by
  simp only [mul_add]
  simp only [mul_assoc, mul_comm, mul_left_comm]

private theorem quadratic_terms (d h b b₀ : R[X]) :
    (d * h) ^ 2 + (d * d) * (h * b) + (d * b₀) * (d * h) + (d * d) * (d * h) =
      d ^ 2 * h * (h + b + b₀ + d) := by
  simp only [pow_two, mul_add]
  simp only [mul_assoc, mul_comm, mul_left_comm]

private theorem separate_terms (a s m p q r t k : R[X]) :
    a + (s + m + (p + q) + (r + t) + k) =
      (m + p + a) + ((s + q + r + t) + k) := by
  simp only [add_assoc, add_comm, add_left_comm]

private theorem seam_variation (a d h m b₀ b k : R[X]) :
    a * (d * h) + ((d * h) ^ 2 + m * (d * h) +
      (d * (b₀ + d)) * (h * b) + (d * (b₀ + d)) * (d * h) + k * (d * (b₀ + d))) =
      d * (h * (m + b₀ * b + a)) +
        (d ^ 2 * h * (h + b + b₀ + d) + d * k * (b₀ + d)) := by
  have h1 : (d * (b₀ + d)) * (h * b) = (d * b₀) * (h * b) + (d * d) * (h * b) := by
    rw [mul_add, add_mul]
  have h2 : (d * (b₀ + d)) * (d * h) = (d * b₀) * (d * h) + (d * d) * (d * h) := by
    rw [mul_add, add_mul]
  rw [h1, h2, separate_terms, linear_terms, quadratic_terms,
    mul_left_comm k d, ← mul_assoc d k (b₀ + d)]

private theorem assemble_seam (u w q c ur aw qr : R[X]) :
    (u + ur) + (w + aw) + (q + qr) + c = (u + w + q + c) + ((aw + qr) + ur) := by
  simp only [add_assoc, add_comm, add_left_comm]

/-- Four small named identities, rather than one normalization of the
combined expression. The actual crown and its coefficients remain opaque. -/
private theorem seam_algebra (u w q c h b m a b₀ k d ur : R[X]) :
    (u + ur) + (w + a * (d * h)) +
        ((h * b + d * h) ^ 2 + (m + d * (b₀ + d)) * (h * b + d * h) +
          (q + k * (d * (b₀ + d)))) + c =
      (u + w + ((h * b) ^ 2 + m * (h * b) + q) + c) +
        (d * (h * (m + b₀ * b + a)) +
          (d ^ 2 * h * (h + b + b₀ + d) + d * k * (b₀ + d) + ur)) := by
  rw [square_affine_update, assemble_seam, seam_variation]
  simp only [add_assoc]

private theorem j_cancel (l z s x y a₃ a₇ a₈ a₁₄ a₁₅ : R[X]) :
    (l * (z + a₃) + s + a₁₄ + a₁₅) + (l + 1) * (z + a₇) + (x + y + z + a₈) =
      s + x + y + l * (a₃ + a₇) + a₇ + a₈ + a₁₄ + a₁₅ := by
  simp only [mul_add, add_mul, one_mul]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

private theorem e_cancel (x z a₆ a₇ a₂ : R[X]) :
    (x + z + a₆) + (z + a₇) + (x + a₂ + 1) = a₆ + a₇ + a₂ + 1 := by
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left]

theorem j_eq (a : ℕ → R) : middle a + b0 a * otherQuartic a + wLeft a = j a :=
  j_cancel (linear a) (z a) (s a) X y (C (a 3)) (C (a 7)) (C (a 8)) (C (a 14)) (C (a 15))

theorem e_eq (a : ℕ → R) : quartic a + otherQuartic a + b0 a = e a :=
  e_cancel X (z a) (C (a 6)) (C (a 7)) (C (a 2))

theorem t_shift8 (a : ℕ → R) (delta : R) :
    t (shift8 a delta) = t a + C delta * linear a := by
  change linear a * (z a + C (a 3 + delta)) =
    linear a * (z a + C (a 3)) + C delta * linear a
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

theorem v_shift8 (a : ℕ → R) (delta : R) :
    v (shift8 a delta) = v a + C delta * quartic a := by
  change quartic a * (z a + C (a 7 + delta)) =
    quartic a * (z a + C (a 7)) + C delta * quartic a
  rw [map_add, ← add_assoc, mul_add, mul_comm _ (C delta)]

private theorem middle_increment (t s a₁₄ a₁₅ l d : R[X]) :
    (t + d * l) + s + a₁₄ + (a₁₅ + (d ^ 2 + d)) =
      (t + s + a₁₄ + a₁₅) + d * (l + 1 + d) := by
  simp only [mul_add, mul_one, pow_two]
  simp only [add_assoc, add_comm, add_left_comm]

theorem middle_shift8 (a : ℕ → R) (delta : R) :
    middle (shift8 a delta) = middle a + C delta * (b0 a + C delta) := by
  have hs : s (shift8 a delta) = s a := rfl
  have h14 : shift8 a delta 14 = a 14 := rfl
  have h15 : shift8 a delta 15 = a 15 + (delta ^ 2 + delta) := rfl
  rw [middle, t_shift8, hs, h14, h15, map_add, map_add, map_pow]
  exact middle_increment (t a) (s a) (C (a 14)) (C (a 15)) (linear a) (C delta)

private theorem low_increment (t s a₁₅ l d : R[X]) :
    (t + d * l) + s + (a₁₅ + (d ^ 2 + d)) =
      (t + s + a₁₅) + d * (l + 1 + d) := by
  simp only [mul_add, mul_one, pow_two]
  simp only [add_assoc, add_comm, add_left_comm]

theorem qLow_shift8 (a : ℕ → R) (delta : R) :
    qLow (shift8 a delta) = qLow a + C (a 14) * (C delta * (b0 a + C delta)) := by
  have hs : s (shift8 a delta) = s a := rfl
  have h14 : shift8 a delta 14 = a 14 := rfl
  have h15 : shift8 a delta 15 = a 15 + (delta ^ 2 + delta) := rfl
  rw [qLow, t_shift8, hs, h14, h15, map_add, map_add, map_pow, low_increment, mul_add]
  rfl

theorem crown_shift8 (a : ℕ → R) (delta : R) :
    crown (shift8 a delta) = crown a + (C delta * slope8 a + remainder8 a delta) := by
  have hu : u (shift8 a delta) = u a + uCorrection a (C delta * linear a) :=
    u_change_t a _ _ rfl (t_shift8 a delta) rfl rfl
  have hw : w (shift8 a delta) = w a + wLeft a * (C delta * quartic a) := by
    change wLeft a * (y + v (shift8 a delta) + C (a 9)) =
      wLeft a * (y + v a + C (a 9)) + wLeft a * (C delta * quartic a)
    rw [v_shift8, move_increment, mul_add]
  have ha : shift8 a delta 17 = a 17 := rfl
  have hv : v a = quartic a * otherQuartic a := rfl
  have hold : u a + w a + ((quartic a * otherQuartic a) ^ 2 +
      middle a * (quartic a * otherQuartic a) + qLow a) + C (a 17) = crown a := by
    rw [← hv, ← q_split]
    rfl
  rw [crown, hu, hw, q_split, v_shift8, middle_shift8, qLow_shift8, ha, hv,
    seam_algebra, hold, j_eq, e_eq]
  rfl

theorem j_monic (a : ℕ → R) : IsMonicOfDegree (j a) 3 := by
  have hc (b : R) : (C b).natDegree < 3 := by rw [natDegree_C]; omega
  have hy : (y : R[X]).natDegree < 3 := (y_monic (R := R)).natDegree_eq ▸ (by omega : 2 < 3)
  have hk : ((C (a 3) : R[X]) + C (a 7)).natDegree ≤ 0 :=
    natDegree_add_le_of_degree_le (by rw [natDegree_C]) (by rw [natDegree_C])
  have hl : (linear a * (C (a 3) + C (a 7))).natDegree < 3 := by
    have h := natDegree_mul_le (p := linear a) (q := C (a 3) + C (a 7))
    have he : (linear a).natDegree = 1 := (isMonicOfDegree_X_add_one (a 2)).natDegree_eq
    rw [he] at h
    omega
  have hs : IsMonicOfDegree (s a + X + y + linear a * (C (a 3) + C (a 7))) 3 :=
    (((s_monic a).add_right (natDegree_X_le.trans_lt (by omega))).add_right hy).add_right hl
  exact (((hs.add_right (hc _)).add_right (hc _)).add_right (hc _)).add_right (hc _)

theorem quartic_monic (a : ℕ → R) : IsMonicOfDegree (quartic a) 4 :=
  ((z_monic a).add_left (natDegree_X_le.trans_lt (by omega))).add_right
    (by rw [natDegree_C]; omega)

theorem remainder8_degree (a : ℕ → R) (delta : R) : (remainder8 a delta).natDegree ≤ 5 := by
  have hd : (C delta : R[X]).natDegree = 0 := natDegree_C delta
  have he : (e a + C delta).natDegree ≤ 0 := by
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · apply natDegree_add_le_of_degree_le
        · exact natDegree_add_le_of_degree_le (by rw [natDegree_C]) (by rw [natDegree_C])
        · rw [natDegree_C]
      · rw [natDegree_one]
    · rw [natDegree_C]
  have h1 : (C delta ^ 2 * quartic a * (e a + C delta)).natDegree ≤ 4 := by
    have hd2 : ((C delta : R[X]) ^ 2).natDegree = 0 := by rw [← map_pow, natDegree_C]
    have hx := natDegree_mul_le (p := C delta ^ 2) (q := quartic a)
    have hy := natDegree_mul_le (p := C delta ^ 2 * quartic a) (q := e a + C delta)
    rw [hd2, (quartic_monic a).natDegree_eq] at hx
    omega
  have hb : IsMonicOfDegree (b0 a + C delta) 1 :=
    ((isMonicOfDegree_X_add_one (a 2)).add_right (by rw [natDegree_one]; omega)).add_right
      (by rw [natDegree_C]; omega)
  have h2 : (C delta * C (a 14) * (b0 a + C delta)).natDegree ≤ 1 := by
    have hprod : (C delta * C (a 14)).natDegree = 0 := by rw [← map_mul, natDegree_C]
    have h := natDegree_mul_le (p := C delta * C (a 14)) (q := b0 a + C delta)
    rw [hprod, hb.natDegree_eq] at h
    exact h
  have hdl : (C delta * linear a).natDegree ≤ 1 := by
    have h := natDegree_mul_le (p := C delta) (q := linear a)
    have hl : (linear a).natDegree = 1 := (isMonicOfDegree_X_add_one (a 2)).natDegree_eq
    rw [hd, hl] at h
    exact h
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (h1.trans (by omega)) (h2.trans (by omega)))
    (uCorrection_degree a _ 1 (by omega) hdl)

theorem shift8_unit (a : ℕ → R) (delta : R) :
    UnitDifference (crown a) (crown (shift8 a delta)) 7 delta :=
  unit_difference_of_lower _ _ _ _ 7 delta ((quartic_monic a).mul (j_monic a))
    ((remainder8_degree a delta).trans_lt (by omega)) (crown_shift8 a delta)

end FastPoly.Char2Degree19InnerSeam
