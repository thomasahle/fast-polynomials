import FastPoly.Examples.Char2Degree23Rows
import FastPoly.Examples.Char2Degree19InnerTail

/-! Reading named unit columns in degree23's explicit sheared row order. -/

namespace FastPoly.Char2Degree23RowUpdates

open Polynomial Char2Degree23Rows Char2Degree19InnerTail
set_option maxHeartbeats 20000

variable {R : Type*} [CommRing R] [CharP R 2] [Nontrivial R]

theorem regular_pivot {p q : R[X]} {i : Fin 23} {d : R}
    (hi : i ≠ 18) (h : UnitDifference p q (22 - i.val) d) :
    polynomialRows q i = polynomialRows p i + d := by
  rw [polynomialRows_other q i hi, polynomialRows_other p i hi]
  exact h.row

/-- Above an ordinary low column, even the sheared row is unchanged.
The exceptional q19 column is handled separately below. -/
theorem regular_higher {p q : R[X]} {i : Fin 23} {d : R}
    (hi : i ≠ 19) (h : UnitDifference p q (22 - i.val) d)
    (j : Fin 23) (hji : j < i) :
    polynomialRows q j = polynomialRows p j := by
  by_cases hj : j = 18
  · subst j
    have hn3 : 22 - i.val < 3 := by
      have he : i.val ≠ 19 := by intro he; apply hi; exact Fin.ext he
      change (18 : ℕ) < i.val at hji
      omega
    rw [polynomialRows_eighteen, polynomialRows_eighteen,
      h.higher 4 (by omega), h.higher 3 hn3]
  · rw [polynomialRows_other q j hj, polynomialRows_other p j hj]
    apply h.higher
    have hi' := i.isLt
    change j.val < i.val at hji
    omega

theorem before_terminal {p q : R[X]}
    (h : (q + p).natDegree ≤ 4) (j : Fin 23) (hj : j < 18) :
    polynomialRows q j = polynomialRows p j := by
  have hne : j ≠ 18 := ne_of_lt hj
  rw [polynomialRows_other q j hne, polynomialRows_other p j hne]
  have hz : (q + p).coeff (22 - j.val) = 0 :=
    coeff_eq_zero_of_natDegree_lt (h.trans_lt (by
      change j.val < 18 at hj
      omega))
  rw [coeff_add] at hz
  exact CharTwo.add_eq_zero.mp hz

/-- q19 has the same change in coefficients four and three. Its explicit
sum-row invariant is the extra fact needed for descending back-substitution. -/
theorem nineteen_higher {p q : R[X]} {d : R}
    (h : UnitDifference p q 4 d)
    (hsum : q.coeff 4 + q.coeff 3 = p.coeff 4 + p.coeff 3)
    (j : Fin 23) (hj : j < 19) :
    polynomialRows q j = polynomialRows p j := by
  by_cases he : j = 18
  · subst j
    rw [polynomialRows_eighteen, polynomialRows_eighteen]
    exact hsum
  · apply before_terminal h.difference_degree j
    have hne : j.val ≠ 18 := by intro hval; apply he; exact Fin.ext hval
    change j.val < 19 at hj
    change j.val < 18
    omega

end FastPoly.Char2Degree23RowUpdates

