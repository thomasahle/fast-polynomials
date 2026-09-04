/-
The degree-six lower bound (`sections/lower.tex`): the case `D ≠ 0`.
-/
import FastPoly.LowerBound.Defs
import FastPoly.LowerBound.Jacobian

/-!
# Case `D ≠ 0`: two Jacobian rows can be made equal

Here `D = L₃₂ R₃₁ - R₃₂ L₃₁ ≠ 0`.  Following `sections/lower.tex`, we pick two of the six
evaluation points, `x₀ = xs 0 ≠ xs 1 = x₁`, and choose parameters making the Jacobian rows
at `x₀` and `x₁` identical; `det_eq_zero_of_rows_eq` then finishes.

## Structure of the proof

Two degenerate branches, each of which already makes the Jacobian singular:

* `s₃ = 0`: the `a₃` and `b₃` columns vanish — `jacobian_det_eq_zero_of_s3_eq_zero`
  (`Defs.lean`).
* `E = L₂₀R₂₁ - L₂₁R₂₀ = 0`: two dependent `u₂`-slot columns at `p = 0` —
  `exists_singular_jacobian_of_E_eq_zero` (`Defs.lean`; Case `D = 0` uses the same lemma).

Main branch (`s₃ ≠ 0`, `E ≠ 0`).  All choices are made by *explicitly solving* small linear
systems (`exists_solve_one`, `exists_solve_two` of `Jacobian.lean`), never by an existence
black box.

* **Step 0.**  Since `D ≠ 0` the `2 × 2` system
  `L₃₁K₁ + L₃₂K₂ = -L₃₀`, `R₃₁K₁ + R₃₂K₂ = -R₃₀`
  has a (unique) solution `(K₁, K₂)`.  These are the required *slopes*: we will force
  `u₁(x₀) - u₁(x₁) = (x₀-x₁)K₁` and `u₂(x₀) - u₂(x₁) = (x₀-x₁)K₂`, which is exactly
  `ℓ₃(x₀) = ℓ₃(x₁)` and `r₃(x₀) = r₃(x₁)`.
* **Step 1a.**  `u₁(x₀) - u₁(x₁) = (x₀-x₁)(R₁₀(x₀+x₁) + a₁)`, so `a₁ := K₁ - R₁₀(x₀+x₁)`
  is the pivot.
* **Step 1b.**  With `A_k = R₂₁u₁(x_k) + R₂₀x_k` and `B_k = L₂₁u₁(x_k) + L₂₀x_k`,
  `u₂(x₀) - u₂(x₁) = (B₀A₀ - B₁A₁) + a₂(A₀-A₁) + b₂(B₀-B₁)` is affine in `(a₂, b₂)` with
  coefficient vector `(A₀-A₁, B₀-B₁) ≠ (0,0)`, because
  `R₂₁(B₀-B₁) - L₂₁(A₀-A₁) = E·(x₀-x₁) ≠ 0`.  Solve for `(a₂, b₂)`.
* **Step 2.**  At `x₀` (writing `W₁ = u₁(x₀)`, `W₂ = u₂(x₀)`, which no longer depend on
  `(a₃,b₃)`),
  `ū₂(x₀) = C₂ + s₃(R₃₂a₃ + L₃₂b₃)` and — *once `ū₂(x₀) = 0`* —
  `ū₁(x₀) = C₁ + s₃(R₃₁a₃ + L₃₁b₃)`.  The determinant of this `2 × 2` system is
  `s₃²(R₃₂L₃₁ - L₃₂R₃₁) = -s₃²D ≠ 0`, so `(a₃, b₃)` can be solved for.
  (Imposing `ū₂(x₀) = 0` first is what removes the paper's `T = (L₂₁r₂ + R₂₁ℓ₂)(x₀)` from
  the system; the determinant is the same.)
* **Conclusion.**  Step 1 gives `ℓ₃(x₀) = ℓ₃(x₁)` and `r₃(x₀) = r₃(x₁)`, hence
  `ū₂(x₀) = ū₂(x₁)` and then `ū₁(x₀) = ū₁(x₁)`; Step 2 makes both vanish.  So all six
  sensitivities agree at `x₀` and `x₁`: `1 = 1`, `ū₁x = 0`, `ū₂r₂ = 0`, `ū₂ℓ₂ = 0`,
  `s₃r₃(x₀) = s₃r₃(x₁)`, `s₃ℓ₃(x₀) = s₃ℓ₃(x₁)`.
-/

namespace FastPoly.LowerBound

variable {F : Type*} [Field F]

/-! ## Two rows of the Jacobian are equal -/

/-- The six sensitivities agree at `x` and `y` as soon as `ū₁` and `ū₂` vanish at both and
`ℓ₃`, `r₃` agree.  This is the "Conclusion" display of `sections/lower.tex`, Case
`D ≠ 0`. -/
private theorem sens_eq_of_ubar_vanish (c : Circuit F) (x y : F) (p : Fin 6 → F)
    (h1x : ubar1 c x p = 0) (h1y : ubar1 c y p = 0)
    (h2x : ubar2 c x p = 0) (h2y : ubar2 c y p = 0)
    (h3 : ell3 c x p = ell3 c y p) (h4 : r3 c x p = r3 c y p) :
    ∀ i, sens c x p i = sens c y p i := by
  intro i
  fin_cases i
  · show ubar1 c x p * x = ubar1 c y p * y
    rw [h1x, h1y, zero_mul, zero_mul]
  · show ubar2 c x p * r2 c x p = ubar2 c y p * r2 c y p
    rw [h2x, h2y, zero_mul, zero_mul]
  · show ubar2 c x p * ell2 c x p = ubar2 c y p * ell2 c y p
    rw [h2x, h2y, zero_mul, zero_mul]
  · show ubar3 c * r3 c x p = ubar3 c * r3 c y p
    rw [h4]
  · show ubar3 c * ell3 c x p = ubar3 c * ell3 c y p
    rw [h3]
  · rfl

/-! ## The main case -/

/-- **Case `D ≠ 0`.**  If `L₃₂R₃₁ - R₃₂L₃₁ ≠ 0` then some parameter point makes the
Jacobian singular, by making the rows at two distinct evaluation points equal. -/
theorem exists_singular_jacobian_of_D_ne_zero (c : Circuit F) (hD : c.D ≠ 0)
    (xs : Fin 6 → F) (hxs : Function.Injective xs) :
    ∃ p : Fin 6 → F, (jacobian c xs p).det = 0 := by
  -- Degenerate branch: `s₃ = 0` kills the `a₃` and `b₃` columns.
  by_cases hs3 : c.s3 = 0
  · exact ⟨0, jacobian_det_eq_zero_of_s3_eq_zero c hs3 xs 0⟩
  -- Degenerate branch: `E = 0` makes the two `u₂` columns dependent.
  by_cases hE : c.E = 0
  · exact exists_singular_jacobian_of_E_eq_zero c hE xs
  have hD' : c.L32 * c.R31 - c.R32 * c.L31 ≠ 0 := hD
  have hE' : c.L20 * c.R21 - c.L21 * c.R20 ≠ 0 := hE
  -- The two evaluation points.
  obtain ⟨x0, x1, hx0, hx1, hne⟩ : ∃ y z : F, xs 0 = y ∧ xs 1 = z ∧ y - z ≠ 0 := by
    refine ⟨xs 0, xs 1, rfl, rfl, sub_ne_zero.mpr fun h => ?_⟩
    exact absurd (hxs h) (by simp)
  -- Step 0: the two slopes forced by `ℓ₃(x₀) = ℓ₃(x₁)` and `r₃(x₀) = r₃(x₁)`.
  obtain ⟨K1, K2, hAeq, hBeq⟩ : ∃ K1 K2 : F,
      c.L31 * K1 + c.L32 * K2 = -c.L30 ∧ c.R31 * K1 + c.R32 * K2 = -c.R30 := by
    refine exists_solve_two c.L31 c.L32 c.R31 c.R32 ?_ _ _
    intro hcon
    exact hD' (by linear_combination -hcon)
  -- Step 1a: the pivot for `a₁`.
  obtain ⟨a1, ha1⟩ : ∃ a1 : F,
      x0 * (c.R10 * x0 + a1) - x1 * (c.R10 * x1 + a1) = (x0 - x1) * K1 :=
    ⟨K1 - c.R10 * (x0 + x1), by ring⟩
  -- Step 1b: solve the (single) linear equation for `(a₂, b₂)`.
  obtain ⟨a2, b2, hab2⟩ : ∃ a2 b2 : F,
      (c.L21 * (x0 * (c.R10 * x0 + a1)) + c.L20 * x0 + a2) *
          (c.R21 * (x0 * (c.R10 * x0 + a1)) + c.R20 * x0 + b2) -
        (c.L21 * (x1 * (c.R10 * x1 + a1)) + c.L20 * x1 + a2) *
          (c.R21 * (x1 * (c.R10 * x1 + a1)) + c.R20 * x1 + b2)
        = (x0 - x1) * K2 := by
    have hST : ¬ (c.R21 * (x0 * (c.R10 * x0 + a1)) + c.R20 * x0
                    - (c.R21 * (x1 * (c.R10 * x1 + a1)) + c.R20 * x1) = 0
                ∧ c.L21 * (x0 * (c.R10 * x0 + a1)) + c.L20 * x0
                    - (c.L21 * (x1 * (c.R10 * x1 + a1)) + c.L20 * x1) = 0) := by
      rintro ⟨hs, ht⟩
      refine mul_ne_zero hE' hne ?_
      linear_combination c.R21 * ht - c.L21 * hs
    obtain ⟨a2, b2, hab⟩ := exists_solve_one hST
      ((x0 - x1) * K2
        - ((c.L21 * (x0 * (c.R10 * x0 + a1)) + c.L20 * x0) *
              (c.R21 * (x0 * (c.R10 * x0 + a1)) + c.R20 * x0)
          - (c.L21 * (x1 * (c.R10 * x1 + a1)) + c.L20 * x1) *
              (c.R21 * (x1 * (c.R10 * x1 + a1)) + c.R20 * x1)))
    exact ⟨a2, b2, by linear_combination hab⟩
  -- The values of `u₁` and `u₂` at `x₀`; they no longer depend on `(a₃, b₃)`.
  obtain ⟨W1, hW1⟩ : ∃ W : F, x0 * (c.R10 * x0 + a1) = W := ⟨_, rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W : F,
      (c.L21 * W1 + c.L20 * x0 + a2) * (c.R21 * W1 + c.R20 * x0 + b2) = W := ⟨_, rfl⟩
  -- Step 2: solve the `2 × 2` system of determinant `-s₃²D` for `(a₃, b₃)`.
  obtain ⟨a3, b3, h3a, h3b⟩ : ∃ a3 b3 : F,
      c.s2 + c.s3 * (c.L32 * (c.R32 * W2 + c.R31 * W1 + c.R30 * x0 + b3)
          + c.R32 * (c.L32 * W2 + c.L31 * W1 + c.L30 * x0 + a3)) = 0
      ∧ c.s1 + c.s3 * (c.L31 * (c.R32 * W2 + c.R31 * W1 + c.R30 * x0 + b3)
          + c.R31 * (c.L32 * W2 + c.L31 * W1 + c.L30 * x0 + a3)) = 0 := by
    obtain ⟨a3, b3, hh1, hh2⟩ := exists_solve_two
      (c.s3 * c.R32) (c.s3 * c.L32) (c.s3 * c.R31) (c.s3 * c.L31)
      (by
        intro hcon
        refine mul_ne_zero (mul_ne_zero hs3 hs3) hD' ?_
        linear_combination -hcon)
      (-(c.s2 + c.s3 * (c.L32 * (c.R32 * W2 + c.R31 * W1 + c.R30 * x0)
          + c.R32 * (c.L32 * W2 + c.L31 * W1 + c.L30 * x0))))
      (-(c.s1 + c.s3 * (c.L31 * (c.R32 * W2 + c.R31 * W1 + c.R30 * x0)
          + c.R31 * (c.L32 * W2 + c.L31 * W1 + c.L30 * x0))))
    exact ⟨a3, b3, by linear_combination hh1, by linear_combination hh2⟩
  -- The parameter point.
  obtain ⟨p, hp0, hp1, hp2, hp3, hp4⟩ : ∃ p : Fin 6 → F,
      p 0 = a1 ∧ p 1 = a2 ∧ p 2 = b2 ∧ p 3 = a3 ∧ p 4 = b3 :=
    ⟨![a1, a2, b2, a3, b3, 0], by simp, by simp, by simp, by simp, by simp⟩
  refine ⟨p, ?_⟩
  -- The program values at `p`, in closed form.
  have e1 : ∀ x : F, u1 c x p = x * (c.R10 * x + a1) := by
    intro x
    show x * (c.R10 * x + p 0) = _
    rw [hp0]
  have e2 : ∀ x : F, ell2 c x p = c.L21 * (x * (c.R10 * x + a1)) + c.L20 * x + a2 := by
    intro x
    show c.L21 * u1 c x p + c.L20 * x + p 1 = _
    rw [hp1, e1]
  have e3 : ∀ x : F, r2 c x p = c.R21 * (x * (c.R10 * x + a1)) + c.R20 * x + b2 := by
    intro x
    show c.R21 * u1 c x p + c.R20 * x + p 2 = _
    rw [hp2, e1]
  have e4 : ∀ x : F, u2 c x p
      = (c.L21 * (x * (c.R10 * x + a1)) + c.L20 * x + a2)
        * (c.R21 * (x * (c.R10 * x + a1)) + c.R20 * x + b2) := by
    intro x
    show ell2 c x p * r2 c x p = _
    rw [e2, e3]
  -- Step 1 achieved: the two required differences.
  have hd1 : u1 c x0 p - u1 c x1 p = (x0 - x1) * K1 := by rw [e1, e1]; exact ha1
  have hd2 : u2 c x0 p - u2 c x1 p = (x0 - x1) * K2 := by rw [e4, e4]; exact hab2
  -- hence `ℓ₃` and `r₃` agree at `x₀` and `x₁`.
  have hell3eq : ell3 c x0 p = ell3 c x1 p := by
    show c.L32 * u2 c x0 p + c.L31 * u1 c x0 p + c.L30 * x0 + p 3
        = c.L32 * u2 c x1 p + c.L31 * u1 c x1 p + c.L30 * x1 + p 3
    linear_combination c.L32 * hd2 + c.L31 * hd1 + (x0 - x1) * hAeq
  have hr3eq : r3 c x0 p = r3 c x1 p := by
    show c.R32 * u2 c x0 p + c.R31 * u1 c x0 p + c.R30 * x0 + p 4
        = c.R32 * u2 c x1 p + c.R31 * u1 c x1 p + c.R30 * x1 + p 4
    linear_combination c.R32 * hd2 + c.R31 * hd1 + (x0 - x1) * hBeq
  -- Step 2 achieved: `ū₂` and `ū₁` vanish at `x₀`.
  have hu1x0 : u1 c x0 p = W1 := by rw [e1]; exact hW1
  have hu2x0 : u2 c x0 p = W2 := by rw [e4, hW1]; exact hW2
  have hell3x0 : ell3 c x0 p = c.L32 * W2 + c.L31 * W1 + c.L30 * x0 + a3 := by
    show c.L32 * u2 c x0 p + c.L31 * u1 c x0 p + c.L30 * x0 + p 3 = _
    rw [hu1x0, hu2x0, hp3]
  have hr3x0 : r3 c x0 p = c.R32 * W2 + c.R31 * W1 + c.R30 * x0 + b3 := by
    show c.R32 * u2 c x0 p + c.R31 * u1 c x0 p + c.R30 * x0 + p 4 = _
    rw [hu1x0, hu2x0, hp4]
  have hub2x0 : ubar2 c x0 p = 0 := by
    show c.s2 + c.s3 * (c.L32 * r3 c x0 p + c.R32 * ell3 c x0 p) = 0
    rw [hr3x0, hell3x0]
    exact h3a
  have hub1x0 : ubar1 c x0 p = 0 := by
    show c.s1 + ubar2 c x0 p * (c.L21 * r2 c x0 p + c.R21 * ell2 c x0 p)
        + c.s3 * (c.L31 * r3 c x0 p + c.R31 * ell3 c x0 p) = 0
    rw [hub2x0, zero_mul, add_zero, hr3x0, hell3x0]
    exact h3b
  -- and therefore also at `x₁`.
  have hub2eq : ubar2 c x0 p = ubar2 c x1 p := by
    show c.s2 + ubar3 c * (c.L32 * r3 c x0 p + c.R32 * ell3 c x0 p)
        = c.s2 + ubar3 c * (c.L32 * r3 c x1 p + c.R32 * ell3 c x1 p)
    rw [hr3eq, hell3eq]
  have hub2x1 : ubar2 c x1 p = 0 := by rw [← hub2eq]; exact hub2x0
  have hub1eq : ubar1 c x0 p = ubar1 c x1 p := by
    show c.s1 + ubar2 c x0 p * (c.L21 * r2 c x0 p + c.R21 * ell2 c x0 p)
        + ubar3 c * (c.L31 * r3 c x0 p + c.R31 * ell3 c x0 p)
        = c.s1 + ubar2 c x1 p * (c.L21 * r2 c x1 p + c.R21 * ell2 c x1 p)
        + ubar3 c * (c.L31 * r3 c x1 p + c.R31 * ell3 c x1 p)
    rw [hub2x0, hub2x1, zero_mul, zero_mul, hr3eq, hell3eq]
  have hub1x1 : ubar1 c x1 p = 0 := by rw [← hub1eq]; exact hub1x0
  -- Conclusion: the rows at `x₀` and `x₁` coincide.
  refine det_eq_zero_of_rows_eq (k := 0) (l := 1) (by simp) fun i => ?_
  rw [jacobian_apply, jacobian_apply, hx0, hx1]
  exact sens_eq_of_ubar_vanish c x0 x1 p hub1x0 hub1x1 hub2x0 hub2x1 hell3eq hr3eq i

end FastPoly.LowerBound
