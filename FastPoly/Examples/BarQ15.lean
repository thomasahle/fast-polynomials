import FastPoly.Examples.BarredPivot
import FastPoly.Polynomial.LowJet
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.Ring

/-!
Scratch development for the finite barred degree-15 gadget.

The central bookkeeping device is `JetEq n p q`, equality of the first `n`
coefficients at infinity.  Algebraically this is congruence modulo `X^n`; using
divisibility keeps all closure arguments exact and avoids expanding the full
degree-15 circuit.
-/

namespace FastPoly.BarQ15

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

private theorem mul_coeff_two (p q : A[X]) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]

private theorem mul_coeff_three (p q : A[X]) :
    (p * q).coeff 3 = p.coeff 0 * q.coeff 3 + p.coeff 1 * q.coeff 2 +
      p.coeff 2 * q.coeff 1 + p.coeff 3 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  norm_num [Finset.sum_range_succ]


/-! Parameter layout: `w,u,v,rho`, then `a₀,…,a₅`, then `b₀,…,b₄`. -/

def w (alpha : ℕ → A) : A := alpha 0
def u (alpha : ℕ → A) : A := alpha 1
def v (alpha : ℕ → A) : A := alpha 2
def rho (alpha : ℕ → A) : A := alpha 3
def a (alpha : ℕ → A) (i : ℕ) : A := alpha (4 + i)
def b (alpha : ℕ → A) (i : ℕ) : A := alpha (10 + i)

/-! The given quadratic and quartic, and the actual evaluation circuit. -/

noncomputable def H2 (r0 r1 : A) : A[X] := X ^ 2 + C r1 * X ^ 1 + C r0

noncomputable def H4 (s0 s1 s2 s3 : A) : A[X] :=
  X ^ 4 + C s3 * X ^ 3 + C s2 * X ^ 2 + C s1 * X ^ 1 + C s0

noncomputable def H8 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (H4 s0 s1 s2 s3 + (X + C (u alpha))) *
    (H4 s0 s1 s2 s3 + (H2 r0 r1 + C (v alpha))) + C (w alpha)

noncomputable def Q3 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  (X + C (a alpha 5)) * (H2 r0 r1 + C (a alpha 4)) + C (a alpha 3)

noncomputable def U0 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (H4 s0 s1 s2 s3 + C (b alpha 3)) * H8 r0 r1 s0 s1 s2 s3 alpha +
    Q3 r0 r1 alpha

noncomputable def V0 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (H4 s0 s1 s2 s3 + C (b alpha 4)) *
    (H8 r0 r1 s0 s1 s2 s3 alpha + C (rho alpha)) + C (a alpha 2)

noncomputable def C1 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (H2 r0 r1 + C (b alpha 1)) * U0 r0 r1 s0 s1 s2 s3 alpha + C (a alpha 1)

noncomputable def C2 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (H2 r0 r1 + C (b alpha 2)) * V0 r0 r1 s0 s1 s2 s3 alpha + C (a alpha 0)

noncomputable def barQ15 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (X + C (b alpha 0)) * C1 r0 r1 s0 s1 s2 s3 alpha +
    C2 r0 r1 s0 s1 s2 s3 alpha

/-! Syntactic degree bounds used solely to transport the circuit through `reflect`. -/

private theorem degree_C_le (z : A) (d : ℕ) : (C z).natDegree ≤ d := by
  rw [natDegree_C]
  omega

private theorem degree_add_le {p q : A[X]} {d : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) : (p + q).natDegree ≤ d :=
  le_trans (natDegree_add_le _ _) (max_le hp hq)

private theorem degree_mul_le {p q : A[X]} {d e : ℕ}
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ e) : (p * q).natDegree ≤ d + e :=
  le_trans natDegree_mul_le (Nat.add_le_add hp hq)

private theorem H2_degree_le (r0 r1 : A) : (H2 r0 r1).natDegree ≤ 2 := by
  rw [H2]
  apply degree_add_le
  · apply degree_add_le (natDegree_X_pow_le 2)
    exact le_trans (degree_mul_le (degree_C_le _ 0) (natDegree_X_pow_le 1)) (by omega)
  · exact degree_C_le _ 2

private theorem H4_degree_le (s0 s1 s2 s3 : A) : (H4 s0 s1 s2 s3).natDegree ≤ 4 := by
  rw [H4]
  apply degree_add_le
  · apply degree_add_le
    · apply degree_add_le
      · apply degree_add_le (natDegree_X_pow_le 4)
        exact le_trans (degree_mul_le (degree_C_le _ 0) (natDegree_X_pow_le 3)) (by omega)
      · exact le_trans (degree_mul_le (degree_C_le _ 0) (natDegree_X_pow_le 2)) (by omega)
    · exact le_trans (degree_mul_le (degree_C_le _ 0) (natDegree_X_pow_le 1)) (by omega)
  · exact degree_C_le _ 4

private theorem H8_degree_le (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (H8 r0 r1 s0 s1 s2 s3 alpha).natDegree ≤ 8 := by
  rw [H8]
  apply degree_add_le
  · exact le_trans (degree_mul_le
      (degree_add_le (H4_degree_le s0 s1 s2 s3)
        (le_trans (degree_add_le natDegree_X_le (degree_C_le _ 1)) (by omega)))
      (degree_add_le (H4_degree_le s0 s1 s2 s3)
        (le_trans (degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2)) (by omega))))
      (by omega)
  · exact degree_C_le _ 8

private theorem Q3_degree_le (r0 r1 : A) (alpha : ℕ → A) :
    (Q3 r0 r1 alpha).natDegree ≤ 3 := by
  rw [Q3]
  apply degree_add_le
  · exact le_trans (degree_mul_le
      (degree_add_le natDegree_X_le (degree_C_le _ 1))
      (degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2))) (by omega)
  · exact degree_C_le _ 3

private theorem U0_degree_le (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (U0 r0 r1 s0 s1 s2 s3 alpha).natDegree ≤ 12 := by
  rw [U0]
  apply degree_add_le
  · exact le_trans (degree_mul_le
      (degree_add_le (H4_degree_le s0 s1 s2 s3) (degree_C_le _ 4))
      (H8_degree_le r0 r1 s0 s1 s2 s3 alpha)) (by omega)
  · exact le_trans (Q3_degree_le r0 r1 alpha) (by omega)

private theorem V0_degree_le (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (V0 r0 r1 s0 s1 s2 s3 alpha).natDegree ≤ 12 := by
  rw [V0]
  apply degree_add_le
  · exact le_trans (degree_mul_le
      (degree_add_le (H4_degree_le s0 s1 s2 s3) (degree_C_le _ 4))
      (degree_add_le (H8_degree_le r0 r1 s0 s1 s2 s3 alpha) (degree_C_le _ 8)))
      (by omega)
  · exact degree_C_le _ 12

private theorem C1_degree_le (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (C1 r0 r1 s0 s1 s2 s3 alpha).natDegree ≤ 14 := by
  rw [C1]
  apply degree_add_le
  · exact le_trans (degree_mul_le
      (degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2))
      (U0_degree_le r0 r1 s0 s1 s2 s3 alpha)) (by omega)
  · exact degree_C_le _ 14

private theorem C2_degree_le (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (C2 r0 r1 s0 s1 s2 s3 alpha).natDegree ≤ 14 := by
  rw [C2]
  apply degree_add_le
  · exact le_trans (degree_mul_le
      (degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2))
      (V0_degree_le r0 r1 s0 s1 s2 s3 alpha)) (by omega)
  · exact degree_C_le _ 14

/-- Padding a reflection by extra zero rows multiplies its jet by a power of `X`. -/
private theorem reflect_pad (p : A[X]) {d N : ℕ} (hp : p.natDegree ≤ d) (hdN : d ≤ N) :
    p.reflect N = p.reflect d * X ^ (N - d) := by
  calc
    p.reflect N = (p * 1).reflect (d + (N - d)) := by
      rw [mul_one, Nat.add_sub_of_le hdN]
    _ = p.reflect d * (1 : A[X]).reflect (N - d) :=
      reflect_mul p 1 hp (by rw [natDegree_one]; omega)
    _ = p.reflect d * X ^ (N - d) := by rw [reflect_one]

private theorem reflect_X_one : (X : A[X]).reflect 1 = 1 := by
  exact reflect_one_X

private theorem reflect_X_four : (X : A[X]).reflect 4 = X ^ 3 := by
  calc
    (X : A[X]).reflect 4 = (X ^ 1 : A[X]).reflect 4 := by rw [pow_one]
    _ = X ^ revAt 4 1 := reflect_monomial 4 1
    _ = X ^ 3 := by norm_num [revAt]

/-! The same circuit at infinity.  Coefficient `i` is the original row `15-i`. -/

noncomputable def jH2 (r0 r1 : A) : A[X] := 1 + C r1 * X + C r0 * X ^ 2

noncomputable def jH4 (s0 s1 s2 s3 : A) : A[X] :=
  1 + C s3 * X + C s2 * X ^ 2 + C s1 * X ^ 3 + C s0 * X ^ 4

noncomputable def jF1 (s0 s1 s2 s3 : A) : A[X] := jH4 s0 s1 s2 s3 + X ^ 3

noncomputable def jF2 (r0 r1 s0 s1 s2 s3 : A) : A[X] :=
  jH4 s0 s1 s2 s3 + X ^ 2 * jH2 r0 r1

noncomputable def jH8Base (r0 r1 s0 s1 s2 s3 : A) : A[X] :=
  jF1 s0 s1 s2 s3 * jF2 r0 r1 s0 s1 s2 s3

noncomputable def jH8 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (jF1 s0 s1 s2 s3 + C (u alpha) * X ^ 4) *
    (jF2 r0 r1 s0 s1 s2 s3 + C (v alpha) * X ^ 4) +
      C (w alpha) * X ^ 8

noncomputable def jQ3 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  (1 + C (a alpha 5) * X) * (jH2 r0 r1 + C (a alpha 4) * X ^ 2) +
    C (a alpha 3) * X ^ 3

noncomputable def jU0 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (jH4 s0 s1 s2 s3 + C (b alpha 3) * X ^ 4) *
      jH8 r0 r1 s0 s1 s2 s3 alpha + X ^ 9 * jQ3 r0 r1 alpha

noncomputable def jV0 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (jH4 s0 s1 s2 s3 + C (b alpha 4) * X ^ 4) *
      (jH8 r0 r1 s0 s1 s2 s3 alpha + C (rho alpha) * X ^ 8) +
    C (a alpha 2) * X ^ 12

noncomputable def jC1 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (jH2 r0 r1 + C (b alpha 1) * X ^ 2) *
      jU0 r0 r1 s0 s1 s2 s3 alpha + C (a alpha 1) * X ^ 14

noncomputable def jC2 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (jH2 r0 r1 + C (b alpha 2) * X ^ 2) *
      jV0 r0 r1 s0 s1 s2 s3 alpha + C (a alpha 0) * X ^ 14

noncomputable def jQ (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (1 + C (b alpha 0) * X) * jC1 r0 r1 s0 s1 s2 s3 alpha +
    X * jC2 r0 r1 s0 s1 s2 s3 alpha

private theorem H2_reflect (r0 r1 : A) : (H2 r0 r1).reflect 2 = jH2 r0 r1 := by
  simp only [H2, jH2, reflect_add, reflect_C_mul_X_pow, reflect_C, reflect_monomial]
  norm_num [revAt]

private theorem H4_reflect (s0 s1 s2 s3 : A) :
    (H4 s0 s1 s2 s3).reflect 4 = jH4 s0 s1 s2 s3 := by
  simp only [H4, jH4, reflect_add, reflect_C_mul_X_pow, reflect_C, reflect_monomial]
  norm_num [revAt]

private theorem H2_reflect_four (r0 r1 : A) :
    (H2 r0 r1).reflect 4 = X ^ 2 * jH2 r0 r1 := by
  rw [reflect_pad (H2 r0 r1) (H2_degree_le r0 r1) (by omega), H2_reflect]
  ring

private theorem H8_reflect (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (H8 r0 r1 s0 s1 s2 s3 alpha).reflect 8 = jH8 r0 r1 s0 s1 s2 s3 alpha := by
  have hF1 : (H4 s0 s1 s2 s3 + (X + C (u alpha))).natDegree ≤ 4 := by
    apply degree_add_le (H4_degree_le s0 s1 s2 s3)
    exact le_trans (degree_add_le natDegree_X_le (degree_C_le _ 1)) (by omega)
  have hF2 : (H4 s0 s1 s2 s3 + (H2 r0 r1 + C (v alpha))).natDegree ≤ 4 := by
    apply degree_add_le (H4_degree_le s0 s1 s2 s3)
    exact le_trans (degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2)) (by omega)
  rw [H8, reflect_add, reflect_mul _ _ hF1 hF2]
  simp only [reflect_add, H4_reflect, H2_reflect_four, reflect_C, reflect_X_four,
    jH8, jF1, jF2]
  ring

private theorem Q3_reflect (r0 r1 : A) (alpha : ℕ → A) :
    (Q3 r0 r1 alpha).reflect 3 = jQ3 r0 r1 alpha := by
  have h1 : (X + C (a alpha 5) : A[X]).natDegree ≤ 1 :=
    degree_add_le natDegree_X_le (degree_C_le _ 1)
  have h2 : (H2 r0 r1 + C (a alpha 4)).natDegree ≤ 2 :=
    degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2)
  rw [Q3, reflect_add, reflect_mul _ _ h1 h2]
  simp only [reflect_add, H2_reflect, reflect_C, reflect_X_one, jQ3]
  ring

private theorem U0_reflect (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (U0 r0 r1 s0 s1 s2 s3 alpha).reflect 12 = jU0 r0 r1 s0 s1 s2 s3 alpha := by
  have h4b : (H4 s0 s1 s2 s3 + C (b alpha 3)).natDegree ≤ 4 :=
    degree_add_le (H4_degree_le s0 s1 s2 s3) (degree_C_le _ 4)
  rw [U0, reflect_add, reflect_mul _ _ h4b (H8_degree_le r0 r1 s0 s1 s2 s3 alpha),
    reflect_pad (Q3 r0 r1 alpha) (Q3_degree_le r0 r1 alpha) (by omega)]
  simp only [reflect_add, H4_reflect, H8_reflect, Q3_reflect, reflect_C, jU0]
  all_goals ring

private theorem V0_reflect (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (V0 r0 r1 s0 s1 s2 s3 alpha).reflect 12 = jV0 r0 r1 s0 s1 s2 s3 alpha := by
  have h4b : (H4 s0 s1 s2 s3 + C (b alpha 4)).natDegree ≤ 4 :=
    degree_add_le (H4_degree_le s0 s1 s2 s3) (degree_C_le _ 4)
  have h8r : (H8 r0 r1 s0 s1 s2 s3 alpha + C (rho alpha)).natDegree ≤ 8 :=
    degree_add_le (H8_degree_le r0 r1 s0 s1 s2 s3 alpha) (degree_C_le _ 8)
  rw [V0, reflect_add, reflect_mul _ _ h4b h8r]
  simp only [reflect_add, H4_reflect, H8_reflect, reflect_C, jV0]

private theorem C1_reflect (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (C1 r0 r1 s0 s1 s2 s3 alpha).reflect 14 = jC1 r0 r1 s0 s1 s2 s3 alpha := by
  have h2b : (H2 r0 r1 + C (b alpha 1)).natDegree ≤ 2 :=
    degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2)
  rw [C1, reflect_add, reflect_mul _ _ h2b (U0_degree_le r0 r1 s0 s1 s2 s3 alpha)]
  simp only [reflect_add, H2_reflect, U0_reflect, reflect_C, jC1]

private theorem C2_reflect (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (C2 r0 r1 s0 s1 s2 s3 alpha).reflect 14 = jC2 r0 r1 s0 s1 s2 s3 alpha := by
  have h2b : (H2 r0 r1 + C (b alpha 2)).natDegree ≤ 2 :=
    degree_add_le (H2_degree_le r0 r1) (degree_C_le _ 2)
  rw [C2, reflect_add, reflect_mul _ _ h2b (V0_degree_le r0 r1 s0 s1 s2 s3 alpha)]
  simp only [reflect_add, H2_reflect, V0_reflect, reflect_C, jC2]

/-- Reversal at infinity is exact for the whole degree-15 circuit. -/
theorem barQ15_reflect (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (barQ15 r0 r1 s0 s1 s2 s3 alpha).reflect 15 =
      jQ r0 r1 s0 s1 s2 s3 alpha := by
  have h1 : (X + C (b alpha 0) : A[X]).natDegree ≤ 1 :=
    degree_add_le natDegree_X_le (degree_C_le _ 1)
  rw [barQ15, reflect_add, reflect_mul _ _ h1 (C1_degree_le r0 r1 s0 s1 s2 s3 alpha),
    reflect_pad (C2 r0 r1 s0 s1 s2 s3 alpha)
      (C2_degree_le r0 r1 s0 s1 s2 s3 alpha) (by omega)]
  simp only [reflect_add, C1_reflect, C2_reflect, reflect_C, reflect_X_one, jQ]
  ring

/-! Named structural factors for the scalar and four-by-four pivot stages. -/

noncomputable def jP1 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  (1 + C (b alpha 0) * X) * (jH2 r0 r1 + C (b alpha 1) * X ^ 2)

noncomputable def jP2 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  X * (jH2 r0 r1 + C (b alpha 2) * X ^ 2)

noncomputable def jOuter (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jP1 r0 r1 alpha + jP2 r0 r1 alpha

noncomputable def jTopBase (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jOuter r0 r1 alpha * jH4 s0 s1 s2 s3 * jH8Base r0 r1 s0 s1 s2 s3

noncomputable def jScalarBase (r0 r1 s0 s1 s2 s3 : A) : A[X] :=
  (jH2 r0 r1 + X * jH2 r0 r1) * jH4 s0 s1 s2 s3 *
    jH8Base r0 r1 s0 s1 s2 s3

noncomputable def jB0Col (r0 r1 s0 s1 s2 s3 : A) : A[X] :=
  X ^ 1 * (jH2 r0 r1 * jH4 s0 s1 s2 s3 * jH8Base r0 r1 s0 s1 s2 s3)

noncomputable def jB1Col (r0 r1 s0 s1 s2 s3 b0 : A) : A[X] :=
  X ^ 2 * ((1 + C b0 * X) * jH4 s0 s1 s2 s3 *
    jH8Base r0 r1 s0 s1 s2 s3)

noncomputable def jB2Col (r0 r1 s0 s1 s2 s3 : A) : A[X] :=
  X ^ 3 * (jH4 s0 s1 s2 s3 * jH8Base r0 r1 s0 s1 s2 s3)

noncomputable def jScalarStage1 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jScalarBase r0 r1 s0 s1 s2 s3 +
    C (b alpha 0) * jB0Col r0 r1 s0 s1 s2 s3

noncomputable def jScalarStage2 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jScalarStage1 r0 r1 s0 s1 s2 s3 alpha +
    C (b alpha 1) * jB1Col r0 r1 s0 s1 s2 s3 (b alpha 0)

noncomputable def jScalarLinear (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jScalarStage2 r0 r1 s0 s1 s2 s3 alpha +
    C (b alpha 2) * jB2Col r0 r1 s0 s1 s2 s3

noncomputable def jB3Col (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  X ^ 4 * (jP1 r0 r1 alpha * jH8Base r0 r1 s0 s1 s2 s3)

noncomputable def jB4Col (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  X ^ 4 * (jP2 r0 r1 alpha * jH8Base r0 r1 s0 s1 s2 s3)

noncomputable def jUCol (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  X ^ 4 * (jOuter r0 r1 alpha * jH4 s0 s1 s2 s3 *
    jF2 r0 r1 s0 s1 s2 s3)

noncomputable def jVCol (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  X ^ 4 * (jOuter r0 r1 alpha * jH4 s0 s1 s2 s3 *
    jF1 s0 s1 s2 s3)

noncomputable def jBlockLinear (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jTopBase r0 r1 s0 s1 s2 s3 alpha +
    C (b alpha 3) * jB3Col r0 r1 s0 s1 s2 s3 alpha +
    C (b alpha 4) * jB4Col r0 r1 s0 s1 s2 s3 alpha +
    C (u alpha) * jUCol r0 r1 s0 s1 s2 s3 alpha +
    C (v alpha) * jVCol r0 r1 s0 s1 s2 s3 alpha

noncomputable def blockA1 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A :=
  (jB3Col r0 r1 s0 s1 s2 s3 alpha).coeff 5

noncomputable def blockC (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A :=
  (jB3Col r0 r1 s0 s1 s2 s3 alpha).coeff 6

noncomputable def blockD (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A :=
  (jB4Col r0 r1 s0 s1 s2 s3 alpha).coeff 6

noncomputable def blockE (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A :=
  (jB3Col r0 r1 s0 s1 s2 s3 alpha).coeff 7

noncomputable def blockF (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A :=
  (jB4Col r0 r1 s0 s1 s2 s3 alpha).coeff 7

noncomputable def blockL (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A :=
  blockE r0 r1 s0 s1 s2 s3 alpha + blockF r0 r1 s0 s1 s2 s3 alpha -
    (jVCol r0 r1 s0 s1 s2 s3 alpha).coeff 7

noncomputable def jBlockColumns (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    Fin 4 → A[X] :=
  ![jB3Col r0 r1 s0 s1 s2 s3 alpha,
    jB4Col r0 r1 s0 s1 s2 s3 alpha,
    jUCol r0 r1 s0 s1 s2 s3 alpha,
    jVCol r0 r1 s0 s1 s2 s3 alpha]

noncomputable def jBlockMatrix (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    Matrix (Fin 4) (Fin 4) A :=
  fun i j => (jBlockColumns r0 r1 s0 s1 s2 s3 alpha j).coeff (4 + i)

/-! The last two high pivots and the exact six-row low residual. -/

noncomputable def jG (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jP1 r0 r1 alpha * (jH4 s0 s1 s2 s3 + C (b alpha 3) * X ^ 4) +
    jP2 r0 r1 alpha * (jH4 s0 s1 s2 s3 + C (b alpha 4) * X ^ 4)

noncomputable def jH8NoWR (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  (jF1 s0 s1 s2 s3 + C (u alpha) * X ^ 4) *
    (jF2 r0 r1 s0 s1 s2 s3 + C (v alpha) * X ^ 4)

noncomputable def jWCol (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  X ^ 8 * jG r0 r1 s0 s1 s2 s3 alpha

noncomputable def jRhoCol (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  X ^ 8 *
    (jP2 r0 r1 alpha * (jH4 s0 s1 s2 s3 + C (b alpha 4) * X ^ 4))

noncomputable def jMidBase (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jG r0 r1 s0 s1 s2 s3 alpha * jH8NoWR r0 r1 s0 s1 s2 s3 alpha +
    X ^ 9 * (jP1 r0 r1 alpha * jH2 r0 r1)

noncomputable def jLowCore (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jP1 r0 r1 alpha * jQ3 r0 r1 alpha +
    C (a alpha 2) * (X ^ 4 * (jH2 r0 r1 + C (b alpha 2) * X ^ 2)) +
    C (a alpha 1) * (X ^ 5 * (1 + C (b alpha 0) * X)) +
    C (a alpha 0) * X ^ 6

noncomputable def jLowStage5 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jP1 r0 r1 alpha * jH2 r0 r1

noncomputable def jLowStage4 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jP1 r0 r1 alpha * ((1 + C (a alpha 5) * X) * jH2 r0 r1)

noncomputable def jLowStage3 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jP1 r0 r1 alpha *
    ((1 + C (a alpha 5) * X) * (jH2 r0 r1 + C (a alpha 4) * X ^ 2))

noncomputable def jLowStage2 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jP1 r0 r1 alpha * jQ3 r0 r1 alpha

noncomputable def jLowStage1 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jLowStage2 r0 r1 alpha +
    C (a alpha 2) * (X ^ 4 * (jH2 r0 r1 + C (b alpha 2) * X ^ 2))

noncomputable def jLowStage0 (r0 r1 : A) (alpha : ℕ → A) : A[X] :=
  jLowStage1 r0 r1 alpha +
    C (a alpha 1) * (X ^ 5 * (1 + C (b alpha 0) * X))

noncomputable def jHigh (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) : A[X] :=
  jG r0 r1 s0 s1 s2 s3 alpha * jH8 r0 r1 s0 s1 s2 s3 alpha +
    C (rho alpha) * jRhoCol r0 r1 s0 s1 s2 s3 alpha

/-! Staged congruences.  Their proofs expand only one circuit layer at a time. -/

theorem jH8_linear_mod_eight (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    JetEq 8 (jH8 r0 r1 s0 s1 s2 s3 alpha)
      (jH8Base r0 r1 s0 s1 s2 s3 +
        C (u alpha) * X ^ 4 * jF2 r0 r1 s0 s1 s2 s3 +
        C (v alpha) * X ^ 4 * jF1 s0 s1 s2 s3) := by
  rw [JetEq]
  refine ⟨C (u alpha * v alpha + w alpha), ?_⟩
  simp only [jH8, jH8Base, map_add, map_mul]
  ring

theorem jTopBase_scalar_decomposition (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    jTopBase r0 r1 s0 s1 s2 s3 alpha =
      jScalarBase r0 r1 s0 s1 s2 s3 +
        C (b alpha 0) * jB0Col r0 r1 s0 s1 s2 s3 +
        C (b alpha 1) * jB1Col r0 r1 s0 s1 s2 s3 (b alpha 0) +
        C (b alpha 2) * jB2Col r0 r1 s0 s1 s2 s3 := by
  simp only [jTopBase, jOuter, jP1, jP2, jScalarBase, jB0Col, jB1Col, jB2Col]
  ring

set_option maxRecDepth 4000 in
/-- The four structural columns have exactly the barred matrix from the paper. -/
theorem jBlockMatrix_eq_barred (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    jBlockMatrix r0 r1 s0 s1 s2 s3 alpha =
      barredPivotMatrix (1 : R)
        (blockA1 r0 r1 s0 s1 s2 s3 alpha)
        (blockC r0 r1 s0 s1 s2 s3 alpha)
        (blockD r0 r1 s0 s1 s2 s3 alpha)
        (blockE r0 r1 s0 s1 s2 s3 alpha)
        (blockF r0 r1 s0 s1 s2 s3 alpha)
        (blockL r0 r1 s0 s1 s2 s3 alpha) := by
  rw [barredPivotMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jBlockMatrix, jBlockColumns, blockA1, blockC, blockD, blockE, blockF,
      blockL, jB3Col, jB4Col, jUCol, jVCol, jOuter, jP1, jP2, jH8Base, jF1,
      jF2, jH4, jH2, coeff_X_pow_mul', Polynomial.mul_coeff_zero,
      Polynomial.mul_coeff_one, mul_coeff_two, mul_coeff_three]
  all_goals ring

/- The full jet and its structural four-column linearization agree through row seven. -/
theorem jQ_block_mod_eight (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    JetEq 8 (jQ r0 r1 s0 s1 s2 s3 alpha)
      (jBlockLinear r0 r1 s0 s1 s2 s3 alpha) := by
  -- First discard the low `Q₃/a₂/a₁/a₀/rho` terms.
  let P1 := jP1 r0 r1 alpha
  let P2 := jP2 r0 r1 alpha
  let H := jH8 r0 r1 s0 s1 s2 s3 alpha
  let H4j := jH4 s0 s1 s2 s3
  let top := P1 * (H4j + C (b alpha 3) * X ^ 4) * H +
    P2 * (H4j + C (b alpha 4) * X ^ 4) * H
  have htop : JetEq 8 (jQ r0 r1 s0 s1 s2 s3 alpha) top := by
    rw [JetEq]
    refine ⟨
      X * P1 * jQ3 r0 r1 alpha +
        C (a alpha 1) * X ^ 6 * (1 + C (b alpha 0) * X) +
        C (rho alpha) * P2 * (H4j + C (b alpha 4) * X ^ 4) +
        C (a alpha 2) * X ^ 4 * P2 +
        C (a alpha 0) * X ^ 7,
      ?_⟩
    simp only [jQ, jC1, jC2, jU0, jV0, P1, P2, H, H4j, top, jP1, jP2]
    ring
  -- Substitute the linearized `H₈` and discard products whose first possible row is 8.
  let Hlin := jH8Base r0 r1 s0 s1 s2 s3 +
    C (u alpha) * X ^ 4 * jF2 r0 r1 s0 s1 s2 s3 +
    C (v alpha) * X ^ 4 * jF1 s0 s1 s2 s3
  have hsub : JetEq 8 top
      (P1 * (H4j + C (b alpha 3) * X ^ 4) * Hlin +
        P2 * (H4j + C (b alpha 4) * X ^ 4) * Hlin) := by
    exact (JetEq.add
      ((JetEq.refl 8 (P1 * (H4j + C (b alpha 3) * X ^ 4))).mul
        (jH8_linear_mod_eight r0 r1 s0 s1 s2 s3 alpha))
      ((JetEq.refl 8 (P2 * (H4j + C (b alpha 4) * X ^ 4))).mul
        (jH8_linear_mod_eight r0 r1 s0 s1 s2 s3 alpha)))
  have hlin : JetEq 8
      (P1 * (H4j + C (b alpha 3) * X ^ 4) * Hlin +
        P2 * (H4j + C (b alpha 4) * X ^ 4) * Hlin)
      (jBlockLinear r0 r1 s0 s1 s2 s3 alpha) := by
    rw [JetEq]
    refine ⟨?_, ?_⟩
    · exact
        C (b alpha 3 * u alpha) * P1 * jF2 r0 r1 s0 s1 s2 s3 +
        C (b alpha 3 * v alpha) * P1 * jF1 s0 s1 s2 s3 +
        C (b alpha 4 * u alpha) * P2 * jF2 r0 r1 s0 s1 s2 s3 +
        C (b alpha 4 * v alpha) * P2 * jF1 s0 s1 s2 s3
    · simp only [jBlockLinear, jTopBase, jB3Col, jB4Col, jUCol, jVCol,
        jOuter, P1, P2, H4j, Hlin, map_mul]
      ring
  exact htop.trans (hsub.trans hlin)

theorem jQ_scalar_mod_four (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    JetEq 4 (jQ r0 r1 s0 s1 s2 s3 alpha)
      (jScalarLinear r0 r1 s0 s1 s2 s3 alpha) := by
  have hqt : JetEq 4 (jQ r0 r1 s0 s1 s2 s3 alpha)
      (jTopBase r0 r1 s0 s1 s2 s3 alpha) := by
    have hqb := JetEq.mono (n := 4) (m := 8) (by omega)
      (jQ_block_mod_eight r0 r1 s0 s1 s2 s3 alpha)
    apply hqb.trans
    rw [JetEq]
    refine ⟨
      C (b alpha 3) * (jP1 r0 r1 alpha * jH8Base r0 r1 s0 s1 s2 s3) +
        C (b alpha 4) * (jP2 r0 r1 alpha * jH8Base r0 r1 s0 s1 s2 s3) +
        C (u alpha) * (jOuter r0 r1 alpha * jH4 s0 s1 s2 s3 *
          jF2 r0 r1 s0 s1 s2 s3) +
        C (v alpha) * (jOuter r0 r1 alpha * jH4 s0 s1 s2 s3 *
          jF1 s0 s1 s2 s3),
      ?_⟩
    simp only [jBlockLinear, jB3Col, jB4Col, jUCol, jVCol]
    ring
  apply hqt.trans
  apply JetEq.of_eq
  simpa only [jScalarLinear, jScalarStage2, jScalarStage1] using
    jTopBase_scalar_decomposition r0 r1 s0 s1 s2 s3 alpha

theorem scalar_pivot_b0 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 1 =
      b alpha 0 + (jScalarBase r0 r1 s0 s1 s2 s3).coeff 1 := by
  rw [(jQ_scalar_mod_four r0 r1 s0 s1 s2 s3 alpha).coeff_eq (by omega)]
  simp only [jScalarLinear, jScalarStage2, jScalarStage1, coeff_add, coeff_C_mul,
    jB0Col, jB1Col, jB2Col, coeff_X_pow_mul']
  simp [jH2, jH4, jH8Base, jF1, jF2, Polynomial.mul_coeff_zero]
  ring

theorem scalar_pivot_b1 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 2 =
      b alpha 1 + (jScalarStage1 r0 r1 s0 s1 s2 s3 alpha).coeff 2 := by
  rw [(jQ_scalar_mod_four r0 r1 s0 s1 s2 s3 alpha).coeff_eq (by omega)]
  simp only [jScalarLinear, jScalarStage2, coeff_add, coeff_C_mul, jB1Col, jB2Col,
    coeff_X_pow_mul']
  simp [Polynomial.mul_coeff_zero, jH4, jH8Base, jF1, jF2, jH2]
  ring

theorem scalar_pivot_b2 (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 3 =
      b alpha 2 + (jScalarStage2 r0 r1 s0 s1 s2 s3 alpha).coeff 3 := by
  rw [(jQ_scalar_mod_four r0 r1 s0 s1 s2 s3 alpha).coeff_eq (by omega)]
  simp only [jScalarLinear, coeff_add, coeff_C_mul, jB2Col, coeff_X_pow_mul']
  simp [Polynomial.mul_coeff_zero, jH4, jH8Base, jF1, jF2, jH2]
  ring

/-- Through row nine only `w` and then `rho` remain after the four-variable block. -/
theorem jQ_mid_mod_ten (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    JetEq 10 (jQ r0 r1 s0 s1 s2 s3 alpha)
      (jMidBase r0 r1 s0 s1 s2 s3 alpha +
        C (w alpha) * jWCol r0 r1 s0 s1 s2 s3 alpha +
        C (rho alpha) * jRhoCol r0 r1 s0 s1 s2 s3 alpha) := by
  rw [JetEq]
  let deltaQ :=
    C (a alpha 5) * jH2 r0 r1 +
      C (a alpha 4) * X * (1 + C (a alpha 5) * X) +
      C (a alpha 3) * X ^ 2
  refine ⟨
    jP1 r0 r1 alpha * deltaQ +
      C (a alpha 2) * X ^ 2 * jP2 r0 r1 alpha +
      C (a alpha 1) * X ^ 4 * (1 + C (b alpha 0) * X) +
      C (a alpha 0) * X ^ 5,
    ?_⟩
  simp only [jQ, jC1, jC2, jU0, jV0, jMidBase, jWCol, jRhoCol, jG,
    jH8NoWR, jH8, jP1, jP2, jQ3, deltaQ]
  ring

theorem mid_pivot_w (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 8 =
      w alpha + (jMidBase r0 r1 s0 s1 s2 s3 alpha).coeff 8 := by
  rw [(jQ_mid_mod_ten r0 r1 s0 s1 s2 s3 alpha).coeff_eq (by omega)]
  simp only [coeff_add, coeff_C_mul, jWCol, jRhoCol, coeff_X_pow_mul']
  simp [jG, jP1, jP2, jH4, jH2, Polynomial.mul_coeff_zero]
  ring

theorem mid_pivot_rho (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 9 =
      rho alpha + w alpha * (jWCol r0 r1 s0 s1 s2 s3 alpha).coeff 9 +
        (jMidBase r0 r1 s0 s1 s2 s3 alpha).coeff 9 := by
  rw [(jQ_mid_mod_ten r0 r1 s0 s1 s2 s3 alpha).coeff_eq (by omega)]
  simp only [coeff_add, coeff_C_mul, jRhoCol, coeff_X_pow_mul']
  simp [jP2, jH4, jH2, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one]
  ring

/-- After the high eleven parameters are known, the remaining expression is exactly a
shifted six-row residual. -/
theorem jQ_eq_high_add_low (r0 r1 s0 s1 s2 s3 : A) (alpha : ℕ → A) :
    jQ r0 r1 s0 s1 s2 s3 alpha =
      jHigh r0 r1 s0 s1 s2 s3 alpha + X ^ 9 * jLowCore r0 r1 alpha := by
  simp only [jQ, jC1, jC2, jU0, jV0, jHigh, jG, jRhoCol, jLowCore, jP1,
    jP2]
  ring

theorem low_pivot_a5 (r0 r1 : A) (alpha : ℕ → A) :
    (jLowCore r0 r1 alpha).coeff 1 =
      a alpha 5 + (jLowStage5 r0 r1 alpha).coeff 1 := by
  simp only [jLowCore, jLowStage5, jQ3, coeff_add,
    Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero,
    Polynomial.coeff_one]
  simp [jP1, jH2]
  ring

theorem low_pivot_a4 (r0 r1 : A) (alpha : ℕ → A) :
    (jLowCore r0 r1 alpha).coeff 2 =
      a alpha 4 + (jLowStage4 r0 r1 alpha).coeff 2 := by
  simp only [jLowCore, jLowStage4, jQ3, coeff_add,
    mul_coeff_two, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, Polynomial.coeff_one]
  simp [jP1, jH2]
  ring

theorem low_pivot_a3 (r0 r1 : A) (alpha : ℕ → A) :
    (jLowCore r0 r1 alpha).coeff 3 =
      a alpha 3 + (jLowStage3 r0 r1 alpha).coeff 3 := by
  simp only [jLowCore, jLowStage3, jQ3, coeff_add,
    mul_coeff_two, mul_coeff_three, Polynomial.mul_coeff_one,
    Polynomial.mul_coeff_zero, Polynomial.coeff_one]
  simp [jP1, jH2]
  ring

theorem low_pivot_a2 (r0 r1 : A) (alpha : ℕ → A) :
    (jLowCore r0 r1 alpha).coeff 4 =
      a alpha 2 + (jLowStage2 r0 r1 alpha).coeff 4 := by
  simp only [jLowCore, jLowStage2, coeff_add, coeff_C_mul, coeff_X_pow_mul']
  simp [jH2]
  ring

theorem low_pivot_a1 (r0 r1 : A) (alpha : ℕ → A) :
    (jLowCore r0 r1 alpha).coeff 5 =
      a alpha 1 + (jLowStage1 r0 r1 alpha).coeff 5 := by
  simp only [jLowCore, jLowStage1, jLowStage2, coeff_add, coeff_C_mul,
    coeff_X_pow_mul']
  simp
  ring

theorem low_pivot_a0 (r0 r1 : A) (alpha : ℕ → A) :
    (jLowCore r0 r1 alpha).coeff 6 =
      a alpha 0 + (jLowStage0 r0 r1 alpha).coeff 6 := by
  simp only [jLowCore, jLowStage0, jLowStage1, jLowStage2, coeff_add, coeff_C_mul,
    coeff_X_pow_mul']
  simp
  ring

/-! ## Explicit decoder -/

noncomputable def barQ15Alg (K : Subalgebra R A) (r0 r1 s0 s1 s2 s3 : A)
    (alpha : ℕ → A) : Subalgebra R A :=
  K ⊔ adjoin R (Set.range fun i => (barQ15 r0 r1 s0 s1 s2 s3 alpha).coeff i)

/-- The finite barred gadget is decodable relative to the coefficients of the given
quadratic and quartic.  The proof follows the rows in order
`b₀,b₁,b₂ | (b₃,b₄,u,v) | w,rho | a₅,…,a₀`; the middle bar is the
explicit determinant-`-1` block solve. -/
theorem barQ15_recover (K : Subalgebra R A) (r0 r1 s0 s1 s2 s3 : A)
    (alpha : ℕ → A)
    (hr0 : r0 ∈ K) (hr1 : r1 ∈ K) (hs0 : s0 ∈ K) (hs1 : s1 ∈ K)
    (hs2 : s2 ∈ K) (hs3 : s3 ∈ K) :
    ∀ i, i < 15 → alpha i ∈ barQ15Alg K r0 r1 s0 s1 s2 s3 alpha := by
  let S := barQ15Alg K r0 r1 s0 s1 s2 s3 alpha
  have hKS : K ≤ S := le_sup_left
  have hobs : ∀ i, (jQ r0 r1 s0 s1 s2 s3 alpha).coeff i ∈ S := by
    intro i
    have href := congrArg (fun p : A[X] => p.coeff i)
      (barQ15_reflect r0 r1 s0 s1 s2 s3 alpha)
    change ((barQ15 r0 r1 s0 s1 s2 s3 alpha).reflect 15).coeff i =
      (jQ r0 r1 s0 s1 s2 s3 alpha).coeff i at href
    rw [coeff_reflect] at href
    rw [← href]
    exact (le_sup_right : adjoin R _ ≤ S)
      (subset_adjoin ⟨revAt 15 i, rfl⟩)
  have hX : CoeffsIn S (X : A[X]) := CoeffsIn.X S
  have hOne : CoeffsIn S (1 : A[X]) := CoeffsIn.one S
  have hH2 : CoeffsIn S (jH2 r0 r1) := by
    rw [jH2]
    exact (hOne.add ((CoeffsIn.C (hKS hr1)).mul hX)).add
      ((CoeffsIn.C (hKS hr0)).mul (hX.pow 2))
  have hH4 : CoeffsIn S (jH4 s0 s1 s2 s3) := by
    rw [jH4]
    exact (((hOne.add ((CoeffsIn.C (hKS hs3)).mul hX)).add
      ((CoeffsIn.C (hKS hs2)).mul (hX.pow 2))).add
      ((CoeffsIn.C (hKS hs1)).mul (hX.pow 3))).add
      ((CoeffsIn.C (hKS hs0)).mul (hX.pow 4))
  have hF1 : CoeffsIn S (jF1 s0 s1 s2 s3) := by
    rw [jF1]
    exact hH4.add (hX.pow 3)
  have hF2 : CoeffsIn S (jF2 r0 r1 s0 s1 s2 s3) := by
    rw [jF2]
    exact hH4.add ((hX.pow 2).mul hH2)
  have hH8base : CoeffsIn S (jH8Base r0 r1 s0 s1 s2 s3) := by
    rw [jH8Base]
    exact hF1.mul hF2
  have hScalarBase : CoeffsIn S (jScalarBase r0 r1 s0 s1 s2 s3) := by
    rw [jScalarBase]
    exact (hH2.add (hX.mul hH2)).mul hH4 |>.mul hH8base

  -- Three scalar top pivots.
  have hb0 : b alpha 0 ∈ S := by
    have hkey : b alpha 0 = (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 1 -
        (jScalarBase r0 r1 s0 s1 s2 s3).coeff 1 := by
      rw [scalar_pivot_b0]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs 1) (hScalarBase 1)
  have hB0Col : CoeffsIn S (jB0Col r0 r1 s0 s1 s2 s3) := by
    rw [jB0Col]
    exact (hX.pow 1).mul ((hH2.mul hH4).mul hH8base)
  have hStage1 : CoeffsIn S (jScalarStage1 r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jScalarStage1]
    exact hScalarBase.add ((CoeffsIn.C hb0).mul hB0Col)
  have hb1 : b alpha 1 ∈ S := by
    have hkey : b alpha 1 = (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 2 -
        (jScalarStage1 r0 r1 s0 s1 s2 s3 alpha).coeff 2 := by
      rw [scalar_pivot_b1]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs 2) (hStage1 2)
  have hB1Col : CoeffsIn S (jB1Col r0 r1 s0 s1 s2 s3 (b alpha 0)) := by
    rw [jB1Col]
    exact (hX.pow 2).mul
      (((hOne.add ((CoeffsIn.C hb0).mul hX)).mul hH4).mul hH8base)
  have hStage2 : CoeffsIn S (jScalarStage2 r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jScalarStage2]
    exact hStage1.add ((CoeffsIn.C hb1).mul hB1Col)
  have hb2 : b alpha 2 ∈ S := by
    have hkey : b alpha 2 = (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 3 -
        (jScalarStage2 r0 r1 s0 s1 s2 s3 alpha).coeff 3 := by
      rw [scalar_pivot_b2]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs 3) (hStage2 3)

  -- The determinant-`-1` four-variable block.
  have hP1 : CoeffsIn S (jP1 r0 r1 alpha) := by
    rw [jP1]
    exact (hOne.add ((CoeffsIn.C hb0).mul hX)).mul
      (hH2.add ((CoeffsIn.C hb1).mul (hX.pow 2)))
  have hP2 : CoeffsIn S (jP2 r0 r1 alpha) := by
    rw [jP2]
    exact hX.mul (hH2.add ((CoeffsIn.C hb2).mul (hX.pow 2)))
  have hOuter : CoeffsIn S (jOuter r0 r1 alpha) := by
    rw [jOuter]
    exact hP1.add hP2
  have hTopBase : CoeffsIn S (jTopBase r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jTopBase]
    exact (hOuter.mul hH4).mul hH8base
  have hB3Col : CoeffsIn S (jB3Col r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jB3Col]
    exact (hX.pow 4).mul (hP1.mul hH8base)
  have hB4Col : CoeffsIn S (jB4Col r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jB4Col]
    exact (hX.pow 4).mul (hP2.mul hH8base)
  have hUCol : CoeffsIn S (jUCol r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jUCol]
    exact (hX.pow 4).mul ((hOuter.mul hH4).mul hF2)
  have hVCol : CoeffsIn S (jVCol r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jVCol]
    exact (hX.pow 4).mul ((hOuter.mul hH4).mul hF1)
  let unknown : Fin 4 → A := ![b alpha 3, b alpha 4, u alpha, v alpha]
  let y : Fin 4 → A := fun i => (jQ r0 r1 s0 s1 s2 s3 alpha).coeff (4 + i)
  let e : Fin 4 → A := fun i => (jTopBase r0 r1 s0 s1 s2 s3 alpha).coeff (4 + i)
  let M := barredPivotMatrix (1 : R)
    (blockA1 r0 r1 s0 s1 s2 s3 alpha)
    (blockC r0 r1 s0 s1 s2 s3 alpha)
    (blockD r0 r1 s0 s1 s2 s3 alpha)
    (blockE r0 r1 s0 s1 s2 s3 alpha)
    (blockF r0 r1 s0 s1 s2 s3 alpha)
    (blockL r0 r1 s0 s1 s2 s3 alpha)
  have hM : ∀ i j, M i j ∈ S := by
    intro i j
    rw [show M = jBlockMatrix r0 r1 s0 s1 s2 s3 alpha from
      (jBlockMatrix_eq_barred r0 r1 s0 s1 s2 s3 alpha).symm]
    fin_cases j
    · exact hB3Col (4 + i)
    · exact hB4Col (4 + i)
    · exact hUCol (4 + i)
    · exact hVCol (4 + i)
  have he : ∀ i, e i ∈ S := fun i => hTopBase (4 + i)
  have hy : ∀ i, y i = ∑ j, M i j * unknown j + e i := by
    intro i
    have hrow := (jQ_block_mod_eight r0 r1 s0 s1 s2 s3 alpha).coeff_eq
      (show 4 + (i : ℕ) < 8 by omega)
    rw [show M = jBlockMatrix r0 r1 s0 s1 s2 s3 alpha from
      (jBlockMatrix_eq_barred r0 r1 s0 s1 s2 s3 alpha).symm]
    fin_cases i <;>
      simp [y, e, unknown, jBlockMatrix, jBlockColumns, jBlockLinear,
        coeff_add, coeff_C_mul, Fin.sum_univ_four] at hrow ⊢ <;>
      (rw [hrow]; ring)
  have hblock := mem_of_barredPivotCert S unknown y e (1 : R)
    (blockA1 r0 r1 s0 s1 s2 s3 alpha)
    (blockC r0 r1 s0 s1 s2 s3 alpha)
    (blockD r0 r1 s0 s1 s2 s3 alpha)
    (blockE r0 r1 s0 s1 s2 s3 alpha)
    (blockF r0 r1 s0 s1 s2 s3 alpha)
    (blockL r0 r1 s0 s1 s2 s3 alpha) isUnit_one hM he hy
  have hyS : ∀ i, y i ∈ S := fun i => hobs (4 + i)
  have hcollapse : S ⊔ adjoin R (Set.range y) ≤ S :=
    sup_le le_rfl (adjoin_le fun z hz => by obtain ⟨i, rfl⟩ := hz; exact hyS i)
  have hb3 : b alpha 3 ∈ S := by simpa [unknown] using hcollapse (hblock 0)
  have hb4 : b alpha 4 ∈ S := by simpa [unknown] using hcollapse (hblock 1)
  have hu : u alpha ∈ S := by simpa [unknown] using hcollapse (hblock 2)
  have hv : v alpha ∈ S := by simpa [unknown] using hcollapse (hblock 3)

  -- Two scalar seam pivots.
  have hG : CoeffsIn S (jG r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jG]
    exact (hP1.mul (hH4.add ((CoeffsIn.C hb3).mul (hX.pow 4)))).add
      (hP2.mul (hH4.add ((CoeffsIn.C hb4).mul (hX.pow 4))))
  have hH8No : CoeffsIn S (jH8NoWR r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jH8NoWR]
    exact (hF1.add ((CoeffsIn.C hu).mul (hX.pow 4))).mul
      (hF2.add ((CoeffsIn.C hv).mul (hX.pow 4)))
  have hWCol : CoeffsIn S (jWCol r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jWCol]
    exact (hX.pow 8).mul hG
  have hRhoCol : CoeffsIn S (jRhoCol r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jRhoCol]
    exact (hX.pow 8).mul
      (hP2.mul (hH4.add ((CoeffsIn.C hb4).mul (hX.pow 4))))
  have hMid : CoeffsIn S (jMidBase r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jMidBase]
    exact (hG.mul hH8No).add ((hX.pow 9).mul (hP1.mul hH2))
  have hw : w alpha ∈ S := by
    have hkey : w alpha = (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 8 -
        (jMidBase r0 r1 s0 s1 s2 s3 alpha).coeff 8 := by
      rw [mid_pivot_w]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs 8) (hMid 8)
  have hrho : rho alpha ∈ S := by
    have hkey : rho alpha = (jQ r0 r1 s0 s1 s2 s3 alpha).coeff 9 -
        w alpha * (jWCol r0 r1 s0 s1 s2 s3 alpha).coeff 9 -
        (jMidBase r0 r1 s0 s1 s2 s3 alpha).coeff 9 := by
      rw [mid_pivot_rho]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ (hobs 9) (Subalgebra.mul_mem _ hw (hWCol 9))) (hMid 9)

  -- Isolate the exact low residual and descend through its six unit pivots.
  have hH8 : CoeffsIn S (jH8 r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jH8]
    exact ((hF1.add ((CoeffsIn.C hu).mul (hX.pow 4))).mul
      (hF2.add ((CoeffsIn.C hv).mul (hX.pow 4)))).add
      ((CoeffsIn.C hw).mul (hX.pow 8))
  have hHigh : CoeffsIn S (jHigh r0 r1 s0 s1 s2 s3 alpha) := by
    rw [jHigh]
    exact (hG.mul hH8).add ((CoeffsIn.C hrho).mul hRhoCol)
  have hLow : ∀ i, (jLowCore r0 r1 alpha).coeff i ∈ S := by
    intro i
    have hrow := congrArg (fun p : A[X] => p.coeff (9 + i))
      (jQ_eq_high_add_low r0 r1 s0 s1 s2 s3 alpha)
    change (jQ r0 r1 s0 s1 s2 s3 alpha).coeff (9 + i) =
      (jHigh r0 r1 s0 s1 s2 s3 alpha + X ^ 9 * jLowCore r0 r1 alpha).coeff
        (9 + i) at hrow
    have hshift : (X ^ 9 * jLowCore r0 r1 alpha).coeff (9 + i) =
        (jLowCore r0 r1 alpha).coeff i := by
      simpa only [Nat.add_comm] using coeff_X_pow_mul (jLowCore r0 r1 alpha) 9 i
    rw [coeff_add, hshift] at hrow
    have hkey : (jLowCore r0 r1 alpha).coeff i =
        (jQ r0 r1 s0 s1 s2 s3 alpha).coeff (9 + i) -
          (jHigh r0 r1 s0 s1 s2 s3 alpha).coeff (9 + i) := by
      rw [hrow]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs (9 + i)) (hHigh (9 + i))
  have hLow5 : CoeffsIn S (jLowStage5 r0 r1 alpha) := by
    rw [jLowStage5]
    exact hP1.mul hH2
  have ha5 : a alpha 5 ∈ S := by
    have hkey : a alpha 5 = (jLowCore r0 r1 alpha).coeff 1 -
        (jLowStage5 r0 r1 alpha).coeff 1 := by rw [low_pivot_a5]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hLow 1) (hLow5 1)
  have hLow4 : CoeffsIn S (jLowStage4 r0 r1 alpha) := by
    rw [jLowStage4]
    exact hP1.mul ((hOne.add ((CoeffsIn.C ha5).mul hX)).mul hH2)
  have ha4 : a alpha 4 ∈ S := by
    have hkey : a alpha 4 = (jLowCore r0 r1 alpha).coeff 2 -
        (jLowStage4 r0 r1 alpha).coeff 2 := by rw [low_pivot_a4]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hLow 2) (hLow4 2)
  have hLow3 : CoeffsIn S (jLowStage3 r0 r1 alpha) := by
    rw [jLowStage3]
    exact hP1.mul ((hOne.add ((CoeffsIn.C ha5).mul hX)).mul
      (hH2.add ((CoeffsIn.C ha4).mul (hX.pow 2))))
  have ha3 : a alpha 3 ∈ S := by
    have hkey : a alpha 3 = (jLowCore r0 r1 alpha).coeff 3 -
        (jLowStage3 r0 r1 alpha).coeff 3 := by rw [low_pivot_a3]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hLow 3) (hLow3 3)
  have hQ3 : CoeffsIn S (jQ3 r0 r1 alpha) := by
    rw [jQ3]
    exact ((hOne.add ((CoeffsIn.C ha5).mul hX)).mul
      (hH2.add ((CoeffsIn.C ha4).mul (hX.pow 2)))).add
      ((CoeffsIn.C ha3).mul (hX.pow 3))
  have hLow2 : CoeffsIn S (jLowStage2 r0 r1 alpha) := by
    rw [jLowStage2]
    exact hP1.mul hQ3
  have ha2 : a alpha 2 ∈ S := by
    have hkey : a alpha 2 = (jLowCore r0 r1 alpha).coeff 4 -
        (jLowStage2 r0 r1 alpha).coeff 4 := by rw [low_pivot_a2]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hLow 4) (hLow2 4)
  have hLow1 : CoeffsIn S (jLowStage1 r0 r1 alpha) := by
    rw [jLowStage1]
    exact hLow2.add ((CoeffsIn.C ha2).mul
      ((hX.pow 4).mul (hH2.add ((CoeffsIn.C hb2).mul (hX.pow 2)))))
  have ha1 : a alpha 1 ∈ S := by
    have hkey : a alpha 1 = (jLowCore r0 r1 alpha).coeff 5 -
        (jLowStage1 r0 r1 alpha).coeff 5 := by rw [low_pivot_a1]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hLow 5) (hLow1 5)
  have hLow0 : CoeffsIn S (jLowStage0 r0 r1 alpha) := by
    rw [jLowStage0]
    exact hLow1.add ((CoeffsIn.C ha1).mul
      ((hX.pow 5).mul (hOne.add ((CoeffsIn.C hb0).mul hX))))
  have ha0 : a alpha 0 ∈ S := by
    have hkey : a alpha 0 = (jLowCore r0 r1 alpha).coeff 6 -
        (jLowStage0 r0 r1 alpha).coeff 6 := by rw [low_pivot_a0]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hLow 6) (hLow0 6)

  intro i hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
      i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
  · simpa [S, barQ15Alg, w] using hw
  · simpa [S, barQ15Alg, u] using hu
  · simpa [S, barQ15Alg, v] using hv
  · simpa [S, barQ15Alg, rho] using hrho
  · simpa [S, barQ15Alg, a] using ha0
  · simpa [S, barQ15Alg, a] using ha1
  · simpa [S, barQ15Alg, a] using ha2
  · simpa [S, barQ15Alg, a] using ha3
  · simpa [S, barQ15Alg, a] using ha4
  · simpa [S, barQ15Alg, a] using ha5
  · simpa [S, barQ15Alg, b] using hb0
  · simpa [S, barQ15Alg, b] using hb1
  · simpa [S, barQ15Alg, b] using hb2
  · simpa [S, barQ15Alg, b] using hb3
  · simpa [S, barQ15Alg, b] using hb4

end FastPoly.BarQ15
