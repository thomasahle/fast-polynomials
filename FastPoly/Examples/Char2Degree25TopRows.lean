import FastPoly.Examples.Char2Degree25RowThirteen

/-! Small top windows of the fixed degree-25 wires. Products are read only
at their leading two rows; recursive circuit definitions stay named. -/
namespace FastPoly.Char2Degree25TopRows

open Polynomial Char2Degree23RowEight Char2Degree23Frame Char2Degree25Frame
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

/-- Only these two index pairs can contribute to the next product row. -/
theorem two_top_product {p q : R[X]} {dp dq : ℕ}
    (hp : p.natDegree ≤ dp + 1) (hq : q.natDegree ≤ dq + 1) :
    (p * q).coeff (dp + dq + 1) =
      p.coeff (dp + 1) * q.coeff dq + p.coeff dp * q.coeff (dq + 1) := by
  classical
  let a : ℕ × ℕ := (dp + 1, dq)
  let b : ℕ × ℕ := (dp, dq + 1)
  have hab : a ≠ b := by
    intro h
    have hfst := congrArg Prod.fst h
    change dp + 1 = dp at hfst
    omega
  have hs : ({a, b} : Finset (ℕ × ℕ)) ⊆ Finset.antidiagonal (dp + dq + 1) := by
    intro ij hij
    simp only [Finset.mem_insert, Finset.mem_singleton] at hij
    rcases hij with rfl | rfl <;> simp only [a, b, Finset.mem_antidiagonal] <;> omega
  have hz : ∀ ij ∈ Finset.antidiagonal (dp + dq + 1), ij ∉ ({a, b} : Finset (ℕ × ℕ)) →
      p.coeff ij.1 * q.coeff ij.2 = 0 := by
    intro ij hij hnot
    have hsum := Finset.mem_antidiagonal.mp hij
    by_cases hi : dp + 1 < ij.1
    · have hzero : p.coeff ij.1 = 0 := coeff_eq_zero_of_natDegree_lt (hp.trans_lt hi)
      rw [hzero, zero_mul]
    · by_cases hj : dq + 1 < ij.2
      · have hzero : q.coeff ij.2 = 0 := coeff_eq_zero_of_natDegree_lt (hq.trans_lt hj)
        rw [hzero, mul_zero]
      · exfalso
        apply hnot
        have he : ij = a ∨ ij = b := by
          rcases ij with ⟨i, j⟩
          dsimp only at hi hj hsum
          by_cases ha : i = dp + 1
          · left
            apply Prod.ext <;> dsimp only [a] <;> omega
          · right
            apply Prod.ext <;> dsimp only [b] <;> omega
        simpa only [Finset.mem_insert, Finset.mem_singleton] using he
  rw [coeff_mul, ← Finset.sum_subset hs hz]
  rw [Finset.sum_insert (by simpa only [Finset.mem_singleton] using hab), Finset.sum_singleton]

theorem monic_coeff {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) : p.coeff n = 1 := by
  rw [← hp.natDegree_eq]
  exact hp.monic.coeff_natDegree

theorem linear_mul_coeff (c : R) (p : R[X]) (n : ℕ) :
    ((X + C c) * p).coeff (n + 1) = p.coeff n + c * p.coeff (n + 1) := by
  rw [add_mul, coeff_add, coeff_X_mul, coeff_C_mul]

theorem y_two : (y : R[X]).coeff 2 = 1 := monic_coeff y_monic
theorem y_other (n : ℕ) (hn : n ≠ 2) : (y : R[X]).coeff n = 0 := by
  change (X * X : R[X]).coeff n = 0
  rw [← pow_two, coeff_X_pow, if_neg hn]
theorem z_four (a : ℕ → R) : (z a).coeff 4 = 1 := monic_coeff (z_monic a)
theorem z_three (a : ℕ → R) : (z a).coeff 3 = 1 := by
  have hp : (y + C (a 0)).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le y_monic.natDegree_eq.le (by rw [natDegree_C]; omega)
  have hq : (X + y + C (a 1)).natDegree ≤ 2 :=
    natDegree_add_le_of_degree_le x_add_y_monic.natDegree_eq.le (by rw [natDegree_C]; omega)
  change ((y + C (a 0)) * (X + y + C (a 1))).coeff (1 + 1 + 1) = _
  rw [two_top_product (dp := 1) (dq := 1) hp hq]
  simp only [Nat.reduceAdd, coeff_add, coeff_C_succ, y_two, y_other 1 (by omega),
    coeff_X, Nat.reduceEqDiff, if_false, if_true, zero_add, add_zero, one_mul, zero_mul]

theorem t_five (a : ℕ → R) : (t a).coeff 5 = 1 := monic_coeff (t_monic a)
theorem t_four (a : ℕ → R) : (t a).coeff 4 = a 2 + 1 := by
  change ((X + C (a 2)) * (z a + C (a 3))).coeff (3 + 1) = _
  rw [linear_mul_coeff]
  simp only [Nat.reduceAdd, coeff_add, coeff_C_succ, z_three, z_four, add_zero, mul_one]
  exact add_comm _ _

noncomputable def U (a : ℕ → R) : R[X] := z a + t a + C (a 5)
theorem U_five (a : ℕ → R) : (U a).coeff 5 = 1 := by
  have hz : (z a).coeff 5 = 0 := coeff_eq_zero_of_natDegree_lt
    ((z_monic a).natDegree_eq.trans_lt (by omega))
  simp only [U, coeff_add, hz, t_five, coeff_C_succ, zero_add, add_zero]
theorem U_four (a : ℕ → R) : (U a).coeff 4 = a 2 := by
  simp only [U, coeff_add, z_four, t_four, coeff_C_succ, add_zero]
  rw [add_comm (a 2) 1]
  exact CharTwo.add_cancel_left (1 : R) (a 2)
theorem H_five (a : ℕ → R) : (hLeft a).coeff 5 = 1 := monic_coeff (hLeft_monic a)
theorem H_four (a : ℕ → R) : (hLeft a).coeff 4 = a 2 := by
  simp only [hLeft, coeff_add, y_other 4 (by omega), z_four, t_four, coeff_C_succ,
    zero_add, add_zero]
  rw [add_comm (a 2) 1]
  exact CharTwo.add_cancel_left (1 : R) (a 2)

theorem P_four (a : ℕ → R) : (Char2Degree25RowThirteen.P a).coeff 4 = 1 := by
  simp only [Char2Degree25RowThirteen.P, coeff_add, coeff_X, y_other 4 (by omega),
    z_four, coeff_C_succ, Nat.reduceEqDiff, if_false, zero_add, add_zero]
theorem P_three (a : ℕ → R) : (Char2Degree25RowThirteen.P a).coeff 3 = 1 := by
  simp only [Char2Degree25RowThirteen.P, coeff_add, coeff_X, y_other 3 (by omega),
    z_three, coeff_C_succ, Nat.reduceEqDiff, if_false, zero_add, add_zero]
theorem Q_three (a : ℕ → R) : (Char2Degree25RowThirteen.inner a).coeff 3 = 1 :=
  monic_coeff (Char2Degree25RowThirteen.inner_monic a)
theorem Q_two (a : ℕ → R) : (Char2Degree25RowThirteen.inner a).coeff 2 = a 2 + 1 := by
  rw [Char2Degree25RowThirteen.inner_eq, coeff_add]
  rw [show 2 = 1 + 1 from rfl, linear_mul_coeff]
  simp only [Nat.reduceAdd, coeff_add, coeff_X, coeff_C_succ, y_two, y_other 1 (by omega),
    Nat.reduceEqDiff, if_false, if_true, zero_add, add_zero, mul_one]
  exact add_comm _ _

end FastPoly.Char2Degree25TopRows
