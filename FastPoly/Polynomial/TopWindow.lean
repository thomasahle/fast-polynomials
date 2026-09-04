import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Top-window coefficient calculus

Finite "calculus at infinity": the top coefficients of a product with a known monic polynomial
are a unitriangular function of the top coefficients of the other factor.  Everything in the
paper's `lem:monic-division`, `lem:peel-monic-factor`, `lem:monic-from-power` reduces to the
single identity `coeff_mul_monic` below plus the triangular recovery theorem.
-/

namespace FastPoly

open Polynomial Finset

variable {A : Type*} [CommRing A]

/-- For monic `q` of degree `d` and any `p`,
`[x^{d+t}](p·q) = [x^t]p + ∑_{j<d} [x^j]q · [x^{d+t-j}]p`:
the coefficient of `p` at `t` appears with coefficient `1`, and everything else involves only
*higher* coefficients of `p`. -/
theorem coeff_mul_monic (p q : A[X]) (hq : q.Monic) (t : ℕ) :
    (p * q).coeff (q.natDegree + t) =
      p.coeff t + ∑ j ∈ range q.natDegree, q.coeff j * p.coeff (q.natDegree + t - j) := by
  set d := q.natDegree with hd
  -- split `q = X^d + q'` with `q'` supported strictly below `d`
  set q' := q - X ^ d with hq'
  have hcoeff_q' : ∀ j, d ≤ j → q'.coeff j = 0 := by
    intro j hj
    rw [hq', coeff_sub, coeff_X_pow]
    rcases hj.lt_or_eq with h | h
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [← hd]; exact h), if_neg h.ne']; simp
    · rw [← h, if_pos rfl, hd, hq.coeff_natDegree, sub_self]
  have hcoeff_q'_lt : ∀ j, j < d → q'.coeff j = q.coeff j := by
    intro j hj
    rw [hq', coeff_sub, coeff_X_pow, if_neg hj.ne, sub_zero]
  have hsplit : p * q = p * X ^ d + p * q' := by rw [← mul_add, hq']; ring
  rw [hsplit, coeff_add, add_comm d t, coeff_mul_X_pow, add_comm t d]
  congr 1
  calc (p * q').coeff (d + t)
      = ∑ k ∈ range (d + t).succ, q'.coeff k * p.coeff (d + t - k) := by
        rw [mul_comm, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = ∑ k ∈ range d, q'.coeff k * p.coeff (d + t - k) :=
        (Finset.sum_subset (Finset.range_mono (by omega)) fun j _ hj => by
          rw [hcoeff_q' j (by simpa using hj), zero_mul]).symm
    _ = ∑ j ∈ range d, q.coeff j * p.coeff (d + t - j) :=
        Finset.sum_congr rfl fun j hj => by rw [hcoeff_q'_lt j (Finset.mem_range.1 hj)]

/-- Adding a polynomial of strictly smaller `natDegree` (or zero) to a monic polynomial
preserves monicity and the degree. -/
theorem monic_add_low [Nontrivial A] {P e : A[X]} (hP : P.Monic)
    (he : e = 0 ∨ e.natDegree < P.natDegree) :
    (P + e).Monic ∧ (P + e).natDegree = P.natDegree := by
  have hdeg : e.degree < P.degree := by
    rcases eq_or_ne e 0 with rfl | hne
    · rw [degree_zero, degree_eq_natDegree hP.ne_zero]
      exact WithBot.bot_lt_coe _
    · rcases he with rfl | hlt
      · exact absurd rfl hne
      · rw [degree_eq_natDegree hne, degree_eq_natDegree hP.ne_zero]
        exact_mod_cast hlt
  refine ⟨hP.add_of_left hdeg, ?_⟩
  have hde := degree_add_eq_left_of_degree_lt hdeg
  exact natDegree_eq_of_degree_eq_some (by rw [hde, degree_eq_natDegree hP.ne_zero])
end FastPoly
