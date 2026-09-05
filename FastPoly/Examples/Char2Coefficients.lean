import FastPoly.Polynomial.MonicEvaluation

namespace FastPoly.Char2Certificate

open Polynomial
variable {F : Type*} [Field F]

/-- Reduce a polynomial identity to its finitely many possibly nonzero rows. -/
theorem bounded_ext {P Q : F[X]} {d : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d)
    (h : ∀ k, k ≤ d → P.coeff k = Q.coeff k) : P = Q := by
  ext k
  by_cases hk : k ≤ d
  · exact h k hk
  · have hp : P.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have hq : Q.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hp, hq]

end FastPoly.Char2Certificate
