/-
The degree-six lower bound (`sections/lower.tex`): the case `D = 0`.
-/
import FastPoly.LowerBound.Defs
import FastPoly.LowerBound.Jacobian
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

/-!
# Case `D = 0`: three Jacobian rows can be made linearly dependent

Here `D = L₃₂ R₃₁ - R₃₂ L₃₁ = 0`.  Following `sections/lower.tex`, we pick three of the six
evaluation points `x₀, x₁, x₂` and use the functional

`⟨f⟩ = (x₁ - x₂) f(x₀) + (x₂ - x₀) f(x₁) + (x₀ - x₁) f(x₂)`,

which kills `1` and `x` and satisfies `⟨x²⟩ = (x₀-x₁)(x₀-x₂)(x₁-x₂) ≠ 0`.  The weight
vector `w` of `det_eq_zero_of_rows_dep` is this triple of coefficients, extended by zero.

## The case tree of `exists_singular_jacobian_of_D_eq_zero`

1. `s₃ = 0`: the `a₃` column of the Jacobian vanishes
   (`jacobian_det_eq_zero_of_s3_eq_zero`).
2. `E = L₂₀R₂₁ - L₂₁R₂₀ = 0`: the `a₂` and `b₂` columns become dependent
   (`exists_singular_jacobian_of_E_eq_zero`, in `Defs.lean`, shared with Case `D ≠ 0`).
3. `R₁₀ = 0`: `u₁` is affine in `x`, so all six sensitivities have degree `≤ 4`
   (`sensPoly_natDegree_le_four_of_R10`).
4. `L₃₂ = R₃₂ = 0`: the third multiplication does not use `u₂`; again degree `≤ 4`
   (`sensPoly_natDegree_le_four_of_L32_R32`).
5. `L₃₂ = 0 ≠ R₃₂`: then `D = 0` forces `L₃₁ = 0`, so `ℓ₃` is affine and, again, all six
   sensitivities have degree `≤ 4` (`sensPoly_natDegree_le_four_of_L32_L31`); the mirror
   branch `R₃₂ = 0 ≠ L₃₂` is `sensPoly_natDegree_le_four_of_R32_R31`.
6. otherwise (`s₃ ≠ 0`, `E ≠ 0`, `L₃₂R₃₂ ≠ 0`, `R₁₀ ≠ 0`) the construction of the paper
   applies: `exists_dependent_rows`.

Branches 3–5 all go through `det_eq_zero_of_sens_natDegree_le`: six polynomials of degree
`≤ 4` evaluated at six points give six Jacobian columns inside a space of dimension `≤ 5`.
The annihilating weight vector is obtained from a `6 × 6` matrix of powers `x_k^j`
(`j ≤ 4`) whose last column is zero, so no explicit divided-difference formula is needed.

In branch 6 the parameters are `(a₁, a₂, b₂, a₃, b₃, b₁) = (0, a₂, b₂, 0, b₃, 0)`, with
`(a₂, b₂)` solving the `2 × 2` system of `Step 1` and `b₃` solving the single equation of
`Step 2`; `char F ≠ 2` enters exactly once, in `hE3` (the step
`0 = ⟨ū₂⟩ = 2s₃R₃₂⟨ℓ₃⟩`).
-/

namespace FastPoly.LowerBound

open Polynomial

variable {F : Type*} [Field F]

/-! ## The program as a polynomial in the input `x`

The degenerate branches of the case analysis are all of the form "all six sensitivities
have degree `≤ 4` in `x`", so that the six columns of the Jacobian are evaluation vectors
of polynomials from a space of dimension `≤ 5`. -/

/-- The circuit constants, pushed into `Polynomial F`. -/
noncomputable def circP (c : Circuit F) : Circuit (Polynomial F) := c.map Polynomial.C

/-- The parameter slots, pushed into `Polynomial F` (they are constants in `x`). -/
noncomputable def parP (p : Fin 6 → F) : Fin 6 → Polynomial F := fun j => Polynomial.C (p j)

/-- The `i`-th sensitivity as a polynomial in the input `x` (the parameters `p` being
fixed): the semantics of `Defs.lean` instantiated at `A = Polynomial F`. -/
noncomputable def sensPoly (c : Circuit F) (p : Fin 6 → F) (i : Fin 6) : Polynomial F :=
  sens (circP c) Polynomial.X (parP p) i

@[simp] theorem eval_sensPoly (c : Circuit F) (p : Fin 6 → F) (x : F) (i : Fin 6) :
    (sensPoly c p i).eval x = sens c x p i := by
  have h1 : (c.map (Polynomial.C : F → Polynomial F)).map (Polynomial.evalRingHom x) = c := by
    rw [Circuit.map_map, Circuit.map_congr c (g := id) (fun y => by simp), Circuit.map_id]
  have h2 : (fun j => (Polynomial.evalRingHom x) (Polynomial.C (p j))) = p := by
    funext j; simp
  have h := map_sens (Polynomial.evalRingHom x) (c.map Polynomial.C) Polynomial.X
    (fun j => Polynomial.C (p j)) i
  rw [h1, h2] at h
  simpa [sensPoly, circP, parP] using h

/-- **The degree criterion.**  If all six sensitivity polynomials have degree `≤ 4` in the
input, then the six columns of the Jacobian are evaluation vectors at six points of
polynomials lying in the `5`-dimensional space `span {1, x, x², x³, x⁴}`, so the Jacobian
is singular. -/
theorem det_eq_zero_of_sens_natDegree_le (c : Circuit F) (xs : Fin 6 → F) (p : Fin 6 → F)
    (h : ∀ i, (sensPoly c p i).natDegree ≤ 4) : (jacobian c xs p).det = 0 := by
  classical
  set W : Matrix (Fin 6) (Fin 6) F :=
    Matrix.of (fun k j => if (j : ℕ) < 5 then xs k ^ (j : ℕ) else 0) with hW
  have hWdet : W.det = 0 := by
    refine Matrix.det_eq_zero_of_column_eq_zero 5 fun k => ?_
    simp [hW]
  obtain ⟨w, hw, hmul⟩ :=
    (Matrix.exists_mulVec_eq_zero_iff (M := W.transpose)).mpr (by rwa [Matrix.det_transpose])
  have hpow : ∀ m : ℕ, m < 5 → ∑ k : Fin 6, w k * xs k ^ m = 0 := by
    intro m hm
    have hj := congrFun hmul (⟨m, by omega⟩ : Fin 6)
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hW, Matrix.of_apply,
      Pi.zero_apply] at hj
    rw [← hj]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [if_pos hm, mul_comm]
  refine det_eq_zero_of_rows_dep w hw fun i => ?_
  have hexp : ∀ k : Fin 6, jacobian c xs p k i
      = ∑ m ∈ Finset.range 5, (sensPoly c p i).coeff m * xs k ^ m := by
    intro k
    rw [jacobian_apply, ← eval_sensPoly c p (xs k) i,
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (h i))]
  calc ∑ k : Fin 6, w k * jacobian c xs p k i
      = ∑ k : Fin 6, ∑ m ∈ Finset.range 5,
          (sensPoly c p i).coeff m * (w k * xs k ^ m) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hexp k, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = ∑ m ∈ Finset.range 5, (sensPoly c p i).coeff m * ∑ k : Fin 6, w k * xs k ^ m := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun m _ => (Finset.mul_sum _ _ _).symm
    _ = 0 := by
        refine Finset.sum_eq_zero fun m hm => ?_
        rw [hpow m (Finset.mem_range.mp hm), mul_zero]

/-! ### Degree bookkeeping

Small composition lemmas for `natDegree`, then the four degenerate branches in which all
six sensitivities have degree `≤ 4`. -/

section Degrees

variable (c : Circuit F) (p : Fin 6 → F)

private theorem nd2 {P Q : Polynomial F} {k : ℕ} (a b : F) (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ k) : (C a * P + C b * Q).natDegree ≤ k :=
  (natDegree_add_le_of_le ((natDegree_C_mul_le _ _).trans hP)
    ((natDegree_C_mul_le _ _).trans hQ)).trans (by omega)

private theorem nd3 {P Q : Polynomial F} {k : ℕ} (a b u : F) (hP : P.natDegree ≤ k)
    (hQ : Q.natDegree ≤ k) : (C a * P + C b * Q + C u).natDegree ≤ k :=
  (natDegree_add_le_of_le (nd2 a b hP hQ) (natDegree_C u).le).trans (by omega)

private theorem nd4 {P Q : Polynomial F} {k : ℕ} (a b s u : F) (hk : 1 ≤ k)
    (hP : P.natDegree ≤ k) (hQ : Q.natDegree ≤ k) :
    (C a * P + C b * Q + C s * X + C u).natDegree ≤ k :=
  (natDegree_add_le_of_le
    (natDegree_add_le_of_le (nd2 a b hP hQ)
      ((natDegree_C_mul_le _ _).trans (natDegree_X_le.trans hk)))
    (natDegree_C u).le).trans (by omega)

/-- `u₁ = x(R₁₀x + a₁)` has degree `≤ 2`. -/
private theorem nd_u1_two : (u1 (circP c) X (parP p)).natDegree ≤ 2 := by
  show (X * (C c.R10 * X + C (p 0))).natDegree ≤ 2
  compute_degree

/-- If `R₁₀ = 0` then `u₁ = a₁x` has degree `≤ 1`. -/
private theorem nd_u1_one (hR10 : c.R10 = 0) : (u1 (circP c) X (parP p)).natDegree ≤ 1 := by
  show (X * (C c.R10 * X + C (p 0))).natDegree ≤ 1
  rw [hR10]
  simp only [map_zero, zero_mul, zero_add]
  compute_degree

private theorem nd_ell2 {d : ℕ} (hd : 1 ≤ d)
    (hu1 : (u1 (circP c) X (parP p)).natDegree ≤ d) :
    (ell2 (circP c) X (parP p)).natDegree ≤ d :=
  nd3 c.L21 c.L20 (p 1) hu1 (natDegree_X_le.trans hd)

private theorem nd_r2 {d : ℕ} (hd : 1 ≤ d)
    (hu1 : (u1 (circP c) X (parP p)).natDegree ≤ d) :
    (r2 (circP c) X (parP p)).natDegree ≤ d :=
  nd3 c.R21 c.R20 (p 2) hu1 (natDegree_X_le.trans hd)

private theorem nd_u2 {d : ℕ} (hd : 1 ≤ d)
    (hu1 : (u1 (circP c) X (parP p)).natDegree ≤ d) :
    (u2 (circP c) X (parP p)).natDegree ≤ d + d :=
  natDegree_mul_le_of_le (nd_ell2 c p hd hu1) (nd_r2 c p hd hu1)

/-- **The degree bookkeeping of the degenerate branches.**  `d` bounds `u₁`, `e` and `f`
bound `ℓ₃` and `r₃`, `g` bounds `L₃₂r₃ + R₃₂ℓ₃` (hence `ū₂`) and `h` bounds
`L₃₁r₃ + R₃₁ℓ₃`; the arithmetic side conditions are exactly what makes all six
sensitivities have degree `≤ 4`. -/
private theorem sensPoly_natDegree_le_four {d e f g h : ℕ} (hd : 1 ≤ d)
    (hu1 : (u1 (circP c) X (parP p)).natDegree ≤ d)
    (hell3 : (ell3 (circP c) X (parP p)).natDegree ≤ e)
    (hr3 : (r3 (circP c) X (parP p)).natDegree ≤ f)
    (hg : (C c.L32 * r3 (circP c) X (parP p)
            + C c.R32 * ell3 (circP c) X (parP p)).natDegree ≤ g)
    (hh : (C c.L31 * r3 (circP c) X (parP p)
            + C c.R31 * ell3 (circP c) X (parP p)).natDegree ≤ h)
    (hgd : g + d ≤ 3) (hh3 : h ≤ 3) (he : e ≤ 4) (hf : f ≤ 4) :
    ∀ i, (sensPoly c p i).natDegree ≤ 4 := by
  have hell2 := nd_ell2 c p hd hu1
  have hr2 := nd_r2 c p hd hu1
  have hubar2 : (ubar2 (circP c) X (parP p)).natDegree ≤ g := by
    show (C c.s2 + C c.s3 * (C c.L32 * r3 (circP c) X (parP p)
      + C c.R32 * ell3 (circP c) X (parP p))).natDegree ≤ g
    exact (natDegree_add_le_of_le (natDegree_C _).le
      ((natDegree_C_mul_le _ _).trans hg)).trans (by omega)
  have hubar1 : (ubar1 (circP c) X (parP p)).natDegree ≤ 3 := by
    show (C c.s1 + ubar2 (circP c) X (parP p)
        * (C c.L21 * r2 (circP c) X (parP p) + C c.R21 * ell2 (circP c) X (parP p))
      + C c.s3 * (C c.L31 * r3 (circP c) X (parP p)
        + C c.R31 * ell3 (circP c) X (parP p))).natDegree ≤ 3
    have hmid : (ubar2 (circP c) X (parP p)
        * (C c.L21 * r2 (circP c) X (parP p)
          + C c.R21 * ell2 (circP c) X (parP p))).natDegree ≤ 3 :=
      (natDegree_mul_le_of_le hubar2 (nd2 c.L21 c.R21 hr2 hell2)).trans (by omega)
    have hlast : (C c.s3 * (C c.L31 * r3 (circP c) X (parP p)
        + C c.R31 * ell3 (circP c) X (parP p))).natDegree ≤ 3 :=
      ((natDegree_C_mul_le _ _).trans hh).trans hh3
    exact (natDegree_add_le_of_le
      (natDegree_add_le_of_le (natDegree_C _).le hmid) hlast).trans (by omega)
  intro i
  fin_cases i
  · show (ubar1 (circP c) X (parP p) * X).natDegree ≤ 4
    exact (natDegree_mul_le_of_le hubar1 natDegree_X_le).trans (by omega)
  · show (ubar2 (circP c) X (parP p) * r2 (circP c) X (parP p)).natDegree ≤ 4
    exact (natDegree_mul_le_of_le hubar2 hr2).trans (by omega)
  · show (ubar2 (circP c) X (parP p) * ell2 (circP c) X (parP p)).natDegree ≤ 4
    exact (natDegree_mul_le_of_le hubar2 hell2).trans (by omega)
  · show (C c.s3 * r3 (circP c) X (parP p)).natDegree ≤ 4
    exact ((natDegree_C_mul_le _ _).trans hr3).trans hf
  · show (C c.s3 * ell3 (circP c) X (parP p)).natDegree ≤ 4
    exact ((natDegree_C_mul_le _ _).trans hell3).trans he
  · show ((1 : Polynomial F)).natDegree ≤ 4
    simp

/-- Branch `L₃₂ = R₃₂ = 0`: the third multiplication does not use `u₂`. -/
private theorem sensPoly_natDegree_le_four_of_L32_R32 (hL32 : c.L32 = 0) (hR32 : c.R32 = 0) :
    ∀ i, (sensPoly c p i).natDegree ≤ 4 := by
  have hu1 := nd_u1_two c p
  have hell3 : (ell3 (circP c) X (parP p)).natDegree ≤ 2 := by
    show (C c.L32 * u2 (circP c) X (parP p) + C c.L31 * u1 (circP c) X (parP p)
      + C c.L30 * X + C (p 3)).natDegree ≤ 2
    rw [hL32]
    simp only [map_zero, zero_mul, zero_add]
    exact nd3 c.L31 c.L30 (p 3) hu1 (natDegree_X_le.trans (by omega))
  have hr3 : (r3 (circP c) X (parP p)).natDegree ≤ 2 := by
    show (C c.R32 * u2 (circP c) X (parP p) + C c.R31 * u1 (circP c) X (parP p)
      + C c.R30 * X + C (p 4)).natDegree ≤ 2
    rw [hR32]
    simp only [map_zero, zero_mul, zero_add]
    exact nd3 c.R31 c.R30 (p 4) hu1 (natDegree_X_le.trans (by omega))
  refine sensPoly_natDegree_le_four c p (d := 2) (e := 2) (f := 2) (g := 0) (h := 2)
    (by omega) hu1 hell3 hr3 ?_ (nd2 c.L31 c.R31 hr3 hell3) (by omega) (by omega) (by omega)
    (by omega)
  rw [hL32, hR32]
  simp

/-- Branch `L₃₂ = L₃₁ = 0`: `ℓ₃` is affine in `x`.  (With `D = 0`, this is what
`L₃₂ = 0 ≠ R₃₂` forces.) -/
private theorem sensPoly_natDegree_le_four_of_L32_L31 (hL32 : c.L32 = 0) (hL31 : c.L31 = 0) :
    ∀ i, (sensPoly c p i).natDegree ≤ 4 := by
  have hu1 := nd_u1_two c p
  have hu2 := nd_u2 c p (by omega) hu1
  have hell3 : (ell3 (circP c) X (parP p)).natDegree ≤ 1 := by
    show (C c.L32 * u2 (circP c) X (parP p) + C c.L31 * u1 (circP c) X (parP p)
      + C c.L30 * X + C (p 3)).natDegree ≤ 1
    rw [hL32, hL31]
    simp only [map_zero, zero_mul, zero_add]
    exact (natDegree_add_le_of_le ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      (natDegree_C _).le).trans (by omega)
  have hr3 : (r3 (circP c) X (parP p)).natDegree ≤ 4 :=
    nd4 c.R32 c.R31 c.R30 (p 4) (by omega) hu2 (hu1.trans (by omega))
  refine sensPoly_natDegree_le_four c p (d := 2) (e := 1) (f := 4) (g := 1) (h := 1)
    (by omega) hu1 hell3 hr3 ?_ ?_ (by omega) (by omega) (by omega) (by omega)
  · rw [hL32]
    simp only [map_zero, zero_mul, zero_add]
    exact (natDegree_C_mul_le _ _).trans hell3
  · rw [hL31]
    simp only [map_zero, zero_mul, zero_add]
    exact (natDegree_C_mul_le _ _).trans hell3

/-- Branch `R₃₂ = R₃₁ = 0`: `r₃` is affine in `x` (the mirror image of the previous
branch). -/
private theorem sensPoly_natDegree_le_four_of_R32_R31 (hR32 : c.R32 = 0) (hR31 : c.R31 = 0) :
    ∀ i, (sensPoly c p i).natDegree ≤ 4 := by
  have hu1 := nd_u1_two c p
  have hu2 := nd_u2 c p (by omega) hu1
  have hr3 : (r3 (circP c) X (parP p)).natDegree ≤ 1 := by
    show (C c.R32 * u2 (circP c) X (parP p) + C c.R31 * u1 (circP c) X (parP p)
      + C c.R30 * X + C (p 4)).natDegree ≤ 1
    rw [hR32, hR31]
    simp only [map_zero, zero_mul, zero_add]
    exact (natDegree_add_le_of_le ((natDegree_C_mul_le _ _).trans natDegree_X_le)
      (natDegree_C _).le).trans (by omega)
  have hell3 : (ell3 (circP c) X (parP p)).natDegree ≤ 4 :=
    nd4 c.L32 c.L31 c.L30 (p 3) (by omega) hu2 (hu1.trans (by omega))
  refine sensPoly_natDegree_le_four c p (d := 2) (e := 4) (f := 1) (g := 1) (h := 1)
    (by omega) hu1 hell3 hr3 ?_ ?_ (by omega) (by omega) (by omega) (by omega)
  · rw [hR32]
    simp only [map_zero, zero_mul, add_zero]
    exact (natDegree_C_mul_le _ _).trans hr3
  · rw [hR31]
    simp only [map_zero, zero_mul, add_zero]
    exact (natDegree_C_mul_le _ _).trans hr3

/-- Branch `R₁₀ = 0`: `u₁` is affine in `x`. -/
private theorem sensPoly_natDegree_le_four_of_R10 (hR10 : c.R10 = 0) :
    ∀ i, (sensPoly c p i).natDegree ≤ 4 := by
  have hu1 := nd_u1_one c p hR10
  have hu2 := nd_u2 c p (by omega) hu1
  have hell3 : (ell3 (circP c) X (parP p)).natDegree ≤ 2 :=
    nd4 c.L32 c.L31 c.L30 (p 3) (by omega) hu2 (hu1.trans (by omega))
  have hr3 : (r3 (circP c) X (parP p)).natDegree ≤ 2 :=
    nd4 c.R32 c.R31 c.R30 (p 4) (by omega) hu2 (hu1.trans (by omega))
  exact sensPoly_natDegree_le_four c p (d := 1) (e := 2) (f := 2) (g := 2) (h := 2)
    (by omega) hu1 hell3 hr3 (nd2 c.L32 c.R32 hr3 hell3) (nd2 c.L31 c.R31 hr3 hell3)
    (by omega) (by omega) (by omega) (by omega)

end Degrees

/-! ## The main branch

`s₃ ≠ 0`, `E ≠ 0`, `L₃₂R₃₂ ≠ 0` and `R₁₀ ≠ 0`.  We take `a₁ = a₃ = b₁ = 0` and choose
`(a₂, b₂)` and then `b₃` so that `ū₂` vanishes at the three chosen points. -/

/-- **The main branch of Case `D = 0`.**  Three parameters are chosen: `(a₂, b₂)` making
`f = L₃₂r₃ + R₃₂ℓ₃` take the same value at the three points (a `2 × 2` linear system with
determinant `(2L₃₂R₃₂)²·E·R₁₀·(y₀-y₁)(y₀-y₂)(y₁-y₂) ≠ 0`), then `b₃` making `ū₂` vanish at
`y₀` — hence, `f` being constant, at all three points.  Then `⟨ℓ₃⟩ = ⟨r₃⟩ = 0` (this is the
step using `char F ≠ 2`) and `ū₁` is constant, so the functional `⟨·⟩` annihilates all six
sensitivities. -/
private theorem exists_dependent_rows (h2 : (2 : F) ≠ 0) (c : Circuit F) (hD : c.D = 0)
    (hs3 : c.s3 ≠ 0) (hE : c.E ≠ 0) (hL32 : c.L32 ≠ 0) (hR32 : c.R32 ≠ 0) (hR10 : c.R10 ≠ 0)
    (y0 y1 y2 : F) (h01 : y0 - y1 ≠ 0) (h02 : y0 - y2 ≠ 0) (h12 : y1 - y2 ≠ 0) :
    ∃ p : Fin 6 → F, ∀ i : Fin 6,
      (y1 - y2) * sens c y0 p i + (y2 - y0) * sens c y1 p i + (y0 - y1) * sens c y2 p i = 0 := by
  have hD' : c.L32 * c.R31 - c.R32 * c.L31 = 0 := hD
  have hE' : c.L20 * c.R21 - c.L21 * c.R20 ≠ 0 := hE
  have hk : (2 : F) * c.L32 * c.R32 ≠ 0 := mul_ne_zero (mul_ne_zero h2 hL32) hR32
  -- `A`, `B` and the `(a₂,b₂)`-free part `G` of `L₃₂r₃ + R₃₂ℓ₃`.
  obtain ⟨Av, hAv⟩ : ∃ f : F → F, ∀ t, f t = c.R21 * (c.R10 * t ^ 2) + c.R20 * t :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Bv, hBv⟩ : ∃ f : F → F, ∀ t, f t = c.L21 * (c.R10 * t ^ 2) + c.L20 * t :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨Gv, hGv⟩ : ∃ f : F → F, ∀ t, f t = (c.L32 * c.R31 + c.R32 * c.L31) * (c.R10 * t ^ 2)
      + (c.L32 * c.R30 + c.R32 * c.L30) * t := ⟨_, fun _ => rfl⟩
  -- **Step 1**: choose `(a₂, b₂)` making `f` constant on the three points.
  have hdet : (2 * c.L32 * c.R32 * (Av y0 - Av y1)) * (2 * c.L32 * c.R32 * (Bv y0 - Bv y2))
      - (2 * c.L32 * c.R32 * (Bv y0 - Bv y1)) * (2 * c.L32 * c.R32 * (Av y0 - Av y2)) ≠ 0 := by
    have hid : (2 * c.L32 * c.R32 * (Av y0 - Av y1)) * (2 * c.L32 * c.R32 * (Bv y0 - Bv y2))
        - (2 * c.L32 * c.R32 * (Bv y0 - Bv y1)) * (2 * c.L32 * c.R32 * (Av y0 - Av y2))
        = (2 * c.L32 * c.R32) * (2 * c.L32 * c.R32) *
          ((c.L20 * c.R21 - c.L21 * c.R20) * c.R10 * ((y0 - y1) * (y0 - y2) * (y1 - y2))) := by
      simp only [hAv, hBv]
      ring
    rw [hid]
    exact mul_ne_zero (mul_ne_zero hk hk)
      (mul_ne_zero (mul_ne_zero hE' hR10) (mul_ne_zero (mul_ne_zero h01 h02) h12))
  obtain ⟨a2, b2, heq1, heq2⟩ := exists_solve_two
    (2 * c.L32 * c.R32 * (Av y0 - Av y1)) (2 * c.L32 * c.R32 * (Bv y0 - Bv y1))
    (2 * c.L32 * c.R32 * (Av y0 - Av y2)) (2 * c.L32 * c.R32 * (Bv y0 - Bv y2)) hdet
    (-(2 * c.L32 * c.R32 * (Bv y0 * Av y0 - Bv y1 * Av y1) + (Gv y0 - Gv y1)))
    (-(2 * c.L32 * c.R32 * (Bv y0 * Av y0 - Bv y2 * Av y2) + (Gv y0 - Gv y2)))
  -- **Step 2**: choose `b₃` making `ū₂(y₀) = 0`.
  obtain ⟨b3, hb3⟩ : ∃ b3 : F, c.L32 * b3 = -(c.s2 / c.s3)
      - (2 * c.L32 * c.R32 * ((Bv y0 + a2) * (Av y0 + b2)) + Gv y0) :=
    ⟨(-(c.s2 / c.s3) - (2 * c.L32 * c.R32 * ((Bv y0 + a2) * (Av y0 + b2)) + Gv y0)) / c.L32,
      by field_simp⟩
  obtain ⟨p, hp0, hp1, hp2, hp3, hp4⟩ : ∃ p : Fin 6 → F,
      p 0 = 0 ∧ p 1 = a2 ∧ p 2 = b2 ∧ p 3 = 0 ∧ p 4 = b3 :=
    ⟨![0, a2, b2, 0, b3, 0], by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨p, ?_⟩
  -- The program values at this parameter point.
  have hu1v : ∀ t : F, u1 c t p = c.R10 * t ^ 2 := by
    intro t
    show t * (c.R10 * t + p 0) = _
    rw [hp0]; ring
  have hell2v : ∀ t : F, ell2 c t p = Bv t + a2 := by
    intro t
    show c.L21 * u1 c t p + c.L20 * t + p 1 = _
    rw [hp1, hu1v, hBv]
  have hr2v : ∀ t : F, r2 c t p = Av t + b2 := by
    intro t
    show c.R21 * u1 c t p + c.R20 * t + p 2 = _
    rw [hp2, hu1v, hAv]
  have hu2v : ∀ t : F, u2 c t p = (Bv t + a2) * (Av t + b2) := by
    intro t
    show ell2 c t p * r2 c t p = _
    rw [hell2v, hr2v]
  have hell3v : ∀ t : F,
      ell3 c t p = c.L32 * u2 c t p + c.L31 * (c.R10 * t ^ 2) + c.L30 * t := by
    intro t
    show c.L32 * u2 c t p + c.L31 * u1 c t p + c.L30 * t + p 3 = _
    rw [hp3, hu1v]; ring
  have hr3v : ∀ t : F,
      r3 c t p = c.R32 * u2 c t p + c.R31 * (c.R10 * t ^ 2) + c.R30 * t + b3 := by
    intro t
    show c.R32 * u2 c t p + c.R31 * u1 c t p + c.R30 * t + p 4 = _
    rw [hp4, hu1v]
  have hubar2v : ∀ t : F, ubar2 c t p
      = c.s2 + c.s3 * (2 * c.L32 * c.R32 * ((Bv t + a2) * (Av t + b2)) + Gv t + c.L32 * b3) := by
    intro t
    show c.s2 + c.s3 * (c.L32 * r3 c t p + c.R32 * ell3 c t p) = _
    rw [hell3v t, hr3v t, hu2v t, hGv]
    ring
  -- Step 1 makes `f` constant on the three points ...
  have hH1 : 2 * c.L32 * c.R32 * ((Bv y0 + a2) * (Av y0 + b2)) + Gv y0
      = 2 * c.L32 * c.R32 * ((Bv y1 + a2) * (Av y1 + b2)) + Gv y1 := by
    linear_combination heq1
  have hH2 : 2 * c.L32 * c.R32 * ((Bv y0 + a2) * (Av y0 + b2)) + Gv y0
      = 2 * c.L32 * c.R32 * ((Bv y2 + a2) * (Av y2 + b2)) + Gv y2 := by
    linear_combination heq2
  -- ... and step 2 then makes `ū₂` vanish at all three.
  have hb2_0 : ubar2 c y0 p = 0 := by
    rw [hubar2v, hb3]
    field_simp
    ring
  have hb2_1 : ubar2 c y1 p = 0 := by
    rw [hubar2v, ← hH1, hb3]
    field_simp
    ring
  have hb2_2 : ubar2 c y2 p = 0 := by
    rw [hubar2v, ← hH2, hb3]
    field_simp
    ring
  -- **Step 3**: `⟨ℓ₃⟩ = ⟨r₃⟩ = 0`.  `D = 0` gives `L₃₂⟨r₃⟩ = R₃₂⟨ℓ₃⟩` ...
  have hEll : c.L32 * ((y1 - y2) * r3 c y0 p + (y2 - y0) * r3 c y1 p + (y0 - y1) * r3 c y2 p)
      - c.R32 * ((y1 - y2) * ell3 c y0 p + (y2 - y0) * ell3 c y1 p
        + (y0 - y1) * ell3 c y2 p) = 0 := by
    rw [hell3v y0, hell3v y1, hell3v y2, hr3v y0, hr3v y1, hr3v y2]
    linear_combination (c.R10 * ((y1 - y2) * y0 ^ 2 + (y2 - y0) * y1 ^ 2
      + (y0 - y1) * y2 ^ 2)) * hD'
  -- ... while `ū₂ = 0` pointwise gives `s₃(L₃₂⟨r₃⟩ + R₃₂⟨ℓ₃⟩) = 0`.
  have hsum2 : c.s3 * (c.L32 * ((y1 - y2) * r3 c y0 p + (y2 - y0) * r3 c y1 p
        + (y0 - y1) * r3 c y2 p)
      + c.R32 * ((y1 - y2) * ell3 c y0 p + (y2 - y0) * ell3 c y1 p
        + (y0 - y1) * ell3 c y2 p)) = 0 := by
    have e0 : c.s2 + c.s3 * (c.L32 * r3 c y0 p + c.R32 * ell3 c y0 p) = 0 := hb2_0
    have e1 : c.s2 + c.s3 * (c.L32 * r3 c y1 p + c.R32 * ell3 c y1 p) = 0 := hb2_1
    have e2 : c.s2 + c.s3 * (c.L32 * r3 c y2 p + c.R32 * ell3 c y2 p) = 0 := hb2_2
    linear_combination (y1 - y2) * e0 + (y2 - y0) * e1 + (y0 - y1) * e2
  -- Adding the two: `2s₃R₃₂⟨ℓ₃⟩ = 0`.  **This is the only use of `char F ≠ 2`.**
  have hE3 : (y1 - y2) * ell3 c y0 p + (y2 - y0) * ell3 c y1 p + (y0 - y1) * ell3 c y2 p = 0 := by
    have hkey : 2 * c.s3 * c.R32 * ((y1 - y2) * ell3 c y0 p + (y2 - y0) * ell3 c y1 p
        + (y0 - y1) * ell3 c y2 p) = 0 := by
      linear_combination hsum2 - c.s3 * hEll
    exact (mul_eq_zero.mp hkey).resolve_left (mul_ne_zero (mul_ne_zero h2 hs3) hR32)
  have hR3 : (y1 - y2) * r3 c y0 p + (y2 - y0) * r3 c y1 p + (y0 - y1) * r3 c y2 p = 0 := by
    have hmul : c.L32 * ((y1 - y2) * r3 c y0 p + (y2 - y0) * r3 c y1 p
        + (y0 - y1) * r3 c y2 p) = 0 := by
      linear_combination hEll + c.R32 * hE3
    exact (mul_eq_zero.mp hmul).resolve_left hL32
  -- **Step 4**: `ū₁` is constant on the three points.
  have hbL : c.L31 = c.L31 / c.L32 * c.L32 := by field_simp
  have hbR : c.R31 = c.L31 / c.L32 * c.R32 := by
    rw [div_mul_eq_mul_div, eq_div_iff hL32]
    linear_combination hD'
  have hubar1v : ∀ t : F, ubar2 c t p = 0 → ubar1 c t p = c.s1 - c.L31 / c.L32 * c.s2 := by
    intro t ht
    have hw : c.s2 + c.s3 * (c.L32 * r3 c t p + c.R32 * ell3 c t p) = 0 := ht
    show c.s1 + ubar2 c t p * (c.L21 * r2 c t p + c.R21 * ell2 c t p)
      + c.s3 * (c.L31 * r3 c t p + c.R31 * ell3 c t p) = _
    rw [ht]
    linear_combination (c.s3 * r3 c t p) * hbL + (c.s3 * ell3 c t p) * hbR
      + c.L31 / c.L32 * hw
  have hc0 := hubar1v y0 hb2_0
  have hc1 := hubar1v y1 hb2_1
  have hc2 := hubar1v y2 hb2_2
  -- **Conclusion**: the functional annihilates all six sensitivities.
  intro i
  fin_cases i
  · show (y1 - y2) * (ubar1 c y0 p * y0) + (y2 - y0) * (ubar1 c y1 p * y1)
      + (y0 - y1) * (ubar1 c y2 p * y2) = 0
    rw [hc0, hc1, hc2]; ring
  · show (y1 - y2) * (ubar2 c y0 p * r2 c y0 p) + (y2 - y0) * (ubar2 c y1 p * r2 c y1 p)
      + (y0 - y1) * (ubar2 c y2 p * r2 c y2 p) = 0
    rw [hb2_0, hb2_1, hb2_2]; ring
  · show (y1 - y2) * (ubar2 c y0 p * ell2 c y0 p) + (y2 - y0) * (ubar2 c y1 p * ell2 c y1 p)
      + (y0 - y1) * (ubar2 c y2 p * ell2 c y2 p) = 0
    rw [hb2_0, hb2_1, hb2_2]; ring
  · show (y1 - y2) * (c.s3 * r3 c y0 p) + (y2 - y0) * (c.s3 * r3 c y1 p)
      + (y0 - y1) * (c.s3 * r3 c y2 p) = 0
    linear_combination c.s3 * hR3
  · show (y1 - y2) * (c.s3 * ell3 c y0 p) + (y2 - y0) * (c.s3 * ell3 c y1 p)
      + (y0 - y1) * (c.s3 * ell3 c y2 p) = 0
    linear_combination c.s3 * hE3
  · show (y1 - y2) * (1 : F) + (y2 - y0) * 1 + (y0 - y1) * 1 = 0
    ring

/-- **Case `D = 0`.**  If `L₃₂R₃₁ - R₃₂L₃₁ = 0` and `char F ≠ 2` then some parameter point
makes the Jacobian singular, by making the rows at three distinct evaluation points
linearly dependent. -/
theorem exists_singular_jacobian_of_D_eq_zero (h2 : (2 : F) ≠ 0) (c : Circuit F)
    (hD : c.D = 0) (xs : Fin 6 → F) (hxs : Function.Injective xs) :
    ∃ p : Fin 6 → F, (jacobian c xs p).det = 0 := by
  have hD' : c.L32 * c.R31 - c.R32 * c.L31 = 0 := hD
  by_cases hs3 : c.s3 = 0
  · exact ⟨0, jacobian_det_eq_zero_of_s3_eq_zero c hs3 xs 0⟩
  by_cases hE : c.E = 0
  · exact exists_singular_jacobian_of_E_eq_zero c hE xs
  by_cases hR10 : c.R10 = 0
  · exact ⟨0, det_eq_zero_of_sens_natDegree_le c xs 0
      (sensPoly_natDegree_le_four_of_R10 c 0 hR10)⟩
  by_cases hL32 : c.L32 = 0
  · by_cases hR32 : c.R32 = 0
    · exact ⟨0, det_eq_zero_of_sens_natDegree_le c xs 0
        (sensPoly_natDegree_le_four_of_L32_R32 c 0 hL32 hR32)⟩
    · have hL31 : c.L31 = 0 := by
        have hmul : c.R32 * c.L31 = 0 := by rw [hL32] at hD'; linear_combination -hD'
        exact (mul_eq_zero.mp hmul).resolve_left hR32
      exact ⟨0, det_eq_zero_of_sens_natDegree_le c xs 0
        (sensPoly_natDegree_le_four_of_L32_L31 c 0 hL32 hL31)⟩
  · by_cases hR32 : c.R32 = 0
    · have hR31 : c.R31 = 0 := by
        have hmul : c.L32 * c.R31 = 0 := by rw [hR32] at hD'; linear_combination hD'
        exact (mul_eq_zero.mp hmul).resolve_left hL32
      exact ⟨0, det_eq_zero_of_sens_natDegree_le c xs 0
        (sensPoly_natDegree_le_four_of_R32_R31 c 0 hR32 hR31)⟩
    · obtain ⟨p, hp⟩ := exists_dependent_rows h2 c hD hs3 hE hL32 hR32 hR10 (xs 0) (xs 1) (xs 2)
        (sub_ne_zero.mpr fun h => (by decide : (0 : Fin 6) ≠ 1) (hxs h))
        (sub_ne_zero.mpr fun h => (by decide : (0 : Fin 6) ≠ 2) (hxs h))
        (sub_ne_zero.mpr fun h => (by decide : (1 : Fin 6) ≠ 2) (hxs h))
      obtain ⟨w, hw0, hw1, hw2, hw3, hw4, hw5⟩ : ∃ w : Fin 6 → F,
          w 0 = xs 1 - xs 2 ∧ w 1 = xs 2 - xs 0 ∧ w 2 = xs 0 - xs 1
            ∧ w 3 = 0 ∧ w 4 = 0 ∧ w 5 = 0 :=
        ⟨![xs 1 - xs 2, xs 2 - xs 0, xs 0 - xs 1, 0, 0, 0],
          by simp, by simp, by simp, by simp, by simp, by simp⟩
      refine ⟨p, det_eq_zero_of_rows_dep w ?_ ?_⟩
      · intro hcon
        exact (sub_ne_zero.mpr fun h => (by decide : (1 : Fin 6) ≠ 2) (hxs h) :
          xs 1 - xs 2 ≠ 0) (by rw [← hw0, hcon]; rfl)
      · intro i
        rw [Fin.sum_univ_six, hw0, hw1, hw2, hw3, hw4, hw5]
        simp only [jacobian_apply]
        linear_combination hp i

end FastPoly.LowerBound
