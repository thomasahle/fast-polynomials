import FastPoly.Examples.Char2Degree25RowFourteen

/-! Four middle raw slots can affect only output degrees at most fifteen. -/

namespace FastPoly.Char2Degree25MiddleFrame

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree23Cancellations
  Char2Degree25Frame

set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

structure SameFixed (a b : ℕ → R) : Prop where
  h0 : a 0 = b 0
  h1 : a 1 = b 1
  h2 : a 2 = b 2
  h3 : a 3 = b 3
  h4 : a 4 = b 4
  h5 : a 5 = b 5
  h6 : a 6 = b 6
  h10 : a 10 = b 10
  h11 : a 11 = b 11
  h12 : a 12 = b 12
  h14 : a 14 = b 14
  h15 : a 15 = b 15
  h16 : a 16 = b 16
  h17 : a 17 = b 17
  h18 : a 18 = b 18
  h19 : a 19 = b 19
  h20 : a 20 = b 20
  h21 : a 21 = b 21
  h22 : a 22 = b 22
  h23 : a 23 = b 23
  h24 : a 24 = b 24

abbrev DifferenceBound (p q : R[X]) (n : ℕ) : Prop := (q + p).natDegree ≤ n

theorem DifferenceBound.mono {p q : R[X]} {m n : ℕ} (h : DifferenceBound p q m)
    (hmn : m ≤ n) : DifferenceBound p q n := h.trans hmn

theorem constant_bound (a b : R) (n : ℕ) : DifferenceBound (C a) (C b) n := by
  apply natDegree_add_le_of_degree_le <;> rw [natDegree_C] <;> omega

private theorem add_changes (p p' q q' : R[X]) :
    (p' + q') + (p + q) = (p' + p) + (q' + q) := by
  simp only [add_assoc, add_comm, add_left_comm]

theorem DifferenceBound.add {p p' q q' : R[X]} {n : ℕ}
    (hp : DifferenceBound p p' n) (hq : DifferenceBound q q' n) :
    DifferenceBound (p + q) (p' + q') n := by
  change ((p' + q') + (p + q)).natDegree ≤ n
  rw [add_changes]
  exact natDegree_add_le_of_degree_le hp hq

theorem same_bound (p : R[X]) (n : ℕ) : DifferenceBound p p n := by
  change (p + p).natDegree ≤ n
  rw [CharTwo.add_self_eq_zero, natDegree_zero]
  omega

theorem DifferenceBound.add_left {p q : R[X]} {n : ℕ}
    (h : DifferenceBound p q n) (r : R[X]) : DifferenceBound (r + p) (r + q) n :=
  (same_bound r n).add h

theorem DifferenceBound.add_right {p q : R[X]} {n : ℕ}
    (h : DifferenceBound p q n) (r : R[X]) : DifferenceBound (p + r) (q + r) n :=
  h.add (same_bound r n)

private theorem left_product (p q q' : R[X]) : p * q' + p * q = p * (q' + q) := by rw [mul_add]

theorem DifferenceBound.mul_left {p q : R[X]} {n k : ℕ}
    (h : DifferenceBound p q n) (r : R[X]) (hr : r.natDegree ≤ k) :
    DifferenceBound (r * p) (r * q) (k + n) := by
  change (r * q + r * p).natDegree ≤ k + n
  rw [left_product]
  exact natDegree_mul_le.trans (Nat.add_le_add hr h)

private theorem right_product (p p' q : R[X]) : p' * q + p * q = (p' + p) * q := by rw [add_mul]

theorem DifferenceBound.mul_right {p q : R[X]} {n k : ℕ}
    (h : DifferenceBound p q n) (r : R[X]) (hr : r.natDegree ≤ k) :
    DifferenceBound (p * r) (q * r) (n + k) := by
  change (q * r + p * r).natDegree ≤ n + k
  rw [right_product]
  exact natDegree_mul_le.trans (Nat.add_le_add h hr)

private theorem product_changes (p p' q q' : R[X]) :
    p' * q' + p * q = (p' + p) * q' + p * (q' + q) := by
  rw [add_mul, mul_add]
  simp only [add_assoc, add_comm, add_left_comm, CharTwo.add_cancel_left,
    CharTwo.add_self_eq_zero, add_zero, zero_add]

theorem DifferenceBound.mul {p p' q q' : R[X]} {m n i j : ℕ}
    (hp : DifferenceBound p p' i) (hq : DifferenceBound q q' j)
    (hpd : p.natDegree ≤ m) (hqd : q'.natDegree ≤ n) :
    DifferenceBound (p * q) (p' * q') (max (i + n) (m + j)) := by
  change (p' * q' + p * q).natDegree ≤ _
  rw [product_changes]
  exact natDegree_add_le_of_degree_le
    ((natDegree_mul_le.trans (Nat.add_le_add hp hqd)).trans (le_max_left _ _))
    ((natDegree_mul_le.trans (Nat.add_le_add hpd hq)).trans (le_max_right _ _))

theorem SameFixed.z_eq {a b : ℕ → R} (he : SameFixed a b) : z b = z a := by
  simp only [z, ← he.h0, ← he.h1]

theorem SameFixed.t_eq {a b : ℕ → R} (he : SameFixed a b) : t b = t a := by
  simp only [t, he.z_eq, ← he.h2, ← he.h3]

theorem SameFixed.u_eq {a b : ℕ → R} (he : SameFixed a b) : u b = u a := by
  simp only [u, he.z_eq, he.t_eq, ← he.h4, ← he.h5]

theorem SameFixed.g_eq {a b : ℕ → R} (he : SameFixed a b) : g b = g a := by
  simp only [g, he.z_eq, he.t_eq, he.u_eq, ← he.h14, ← he.h15]

theorem SameFixed.v_difference {a b : ℕ → R} (he : SameFixed a b) : DifferenceBound (v a) (v b) 1 := by
  change DifferenceBound ((X + C (a 6)) * (y + z a + C (a 7)))
    ((X + C (b 6)) * (y + z b + C (b 7))) 1
  rw [← he.h6, he.z_eq]
  exact ((constant_bound (a 7) (b 7) 0).add_left (y + z a)).mul_left _
    (isMonicOfDegree_X_add_one (a 6)).natDegree_eq.le

theorem SameFixed.w_difference {a b : ℕ → R} (he : SameFixed a b) : DifferenceBound (w a) (w b) 5 := by
  have hl : DifferenceBound (wLeft a) (X + y + z a + C (b 8)) 0 :=
    (constant_bound (a 8) (b 8) 0).add_left (X + y + z a)
  have hr : DifferenceBound (y + v a + C (a 9)) (y + v b + C (b 9)) 1 :=
    (he.v_difference.add_left y).add (constant_bound _ _ _)
  have hq : (y + v b + C (b 9)).natDegree ≤ 5 :=
    (((v_monic b).add_left (y_monic.natDegree_eq.trans_lt (by omega))).add_right
      (by rw [natDegree_C]; omega)).natDegree_eq.le
  change DifferenceBound (wLeft a * (y + v a + C (a 9)))
    ((X + y + z b + C (b 8)) * (y + v b + C (b 9))) 5
  rw [he.z_eq]
  exact hl.mul hr (wLeft_monic a).natDegree_eq.le hq

theorem SameFixed.s_difference {a b : ℕ → R} (he : SameFixed a b) : DifferenceBound (s a) (s b) 5 := by
  change DifferenceBound ((z a + C (a 10)) * (v a + C (a 11)))
    ((z b + C (b 10)) * (v b + C (b 11))) 5
  rw [he.z_eq, ← he.h10, ← he.h11]
  exact (he.v_difference.add_right (C (a 11))).mul_left _
    ((z_monic a).add_right (by rw [natDegree_C]; omega)).natDegree_eq.le

theorem SameFixed.r_difference {a b : ℕ → R} (he : SameFixed a b) : DifferenceBound (r a) (r b) 5 := by
  change DifferenceBound ((X + t a + C (a 12)) * (u a + C (a 13)))
    ((X + t b + C (b 12)) * (u b + C (b 13))) 5
  rw [he.t_eq, he.u_eq, ← he.h12]
  exact ((constant_bound (a 13) (b 13) 0).add_left (u a)).mul_left _
    (Char2Degree25HighFrame.rLeft_monic a).natDegree_eq.le

theorem SameFixed.ell_difference {a b : ℕ → R} (he : SameFixed a b) : DifferenceBound (ell a) (ell b) 2 := by
  change DifferenceBound ((X + C (a 16)) * (z a + v a + C (a 17)))
    ((X + C (b 16)) * (z b + v b + C (b 17))) 2
  rw [he.z_eq, ← he.h16, ← he.h17]
  exact ((he.v_difference.add_left (z a)).add_right (C (a 17))).mul_left _
    (isMonicOfDegree_X_add_one (a 16)).natDegree_eq.le

theorem SameFixed.h_difference {a b : ℕ → R} (he : SameFixed a b) :
    DifferenceBound (Char2Degree25Frame.h a) (Char2Degree25Frame.h b) 10 := by
  have hl : hLeft b = hLeft a := by simp only [hLeft, he.z_eq, he.t_eq, ← he.h18]
  have hr : DifferenceBound (hRight a) (hRight b) 5 := by
    change DifferenceBound ((X + y + z a + u a) + v a + w a + r a + C (a 19))
      ((X + y + z b + u b) + v b + w b + r b + C (b 19)) 5
    rw [he.z_eq, he.u_eq, ← he.h19]
    exact ((((he.v_difference.mono (by omega)).add_left (X + y + z a + u a)).add
      he.w_difference).add he.r_difference).add_right (C (a 19))
  change DifferenceBound (hLeft a * hRight a) (hLeft b * hRight b) 10
  rw [hl]
  exact hr.mul_left _ (hLeft_monic a).natDegree_eq.le

theorem SameFixed.j_difference {a b : ℕ → R} (he : SameFixed a b) : DifferenceBound (j a) (j b) 7 := by
  have hl : jLeft b = jLeft a := by simp only [jLeft, he.t_eq, ← he.h20]
  change DifferenceBound (jLeft a * (ell a + C (a 21))) (jLeft b * (ell b + C (b 21))) 7
  rw [hl, ← he.h21]
  exact (he.ell_difference.add_right (C (a 21))).mul_left _ (jLeft_monic a).natDegree_eq.le

theorem SameFixed.n_difference {a b : ℕ → R} (he : SameFixed a b) : DifferenceBound (n a) (n b) 15 := by
  have hr : nRight b = nRight a := by simp only [nRight, he.t_eq, ← he.h23]
  have hl : DifferenceBound (nLeft a) (nLeft b) 10 := by
    change DifferenceBound ((X + t a + u a) + s a + r a + g a + ell a +
      Char2Degree25Frame.h a + j a + C (a 22))
      ((X + t b + u b) + s b + r b + g b + ell b + Char2Degree25Frame.h b + j b + C (b 22)) 10
    rw [he.t_eq, he.u_eq, he.g_eq, ← he.h22]
    exact ((((((he.s_difference.mono (by omega)).add_left (X + t a + u a)).add
      (he.r_difference.mono (by omega))).add_right (g a)).add
      (he.ell_difference.mono (by omega))).add he.h_difference).add
      (he.j_difference.mono (by omega)) |>.add_right (C (a 22))
  change DifferenceBound (nLeft a * nRight a) (nLeft b * nRight b) 15
  rw [hr]
  exact hl.mul_right _ (nRight_monic a).natDegree_eq.le

theorem SameFixed.output_difference_degree {a b : ℕ → R} (he : SameFixed a b) :
    (Char2Degree25Frame.output b + Char2Degree25Frame.output a).natDegree ≤ 15 := by
  change DifferenceBound (((y + z a + u a) + ell a) + n a + C (a 24))
    (((y + z b + u b) + ell b) + n b + C (b 24)) 15
  rw [he.z_eq, he.u_eq, ← he.h24]
  exact (((he.ell_difference.mono (by omega)).add_left (y + z a + u a)).add
    he.n_difference).add_right (C (a 24))

end FastPoly.Char2Degree25MiddleFrame
