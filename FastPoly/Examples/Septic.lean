import FastPoly.Section4.KnownPowers
import FastPoly.Recover.Context
import FastPoly.Polynomial.CausalShell

/-!
# Checkpoint example: the septic base construction

The four-multiplication circuit of `lem:septic-base` in `sections/constructions.tex`:

  y = x(x + α₆),  z = (α₅ + x + y)(α₄ + x),  w = (α₃ + z)x,
  v = (α₂ + x + z)(α₁ + w),  P₇ = α₀ + y + w + v.

We prove that all seven parameters are recoverable from the seven low coefficients of `P₇`
whenever `2` is a unit in the scalar ring, following the paper's triangular decoder verbatim:
first the internal quantities `z₂, z₁` of the cubic `z`, then `α₁, α₆, α₄, α₅, α₃, α₂, α₀`.

Unlike `Q₃` (an instance of the scalar engine), this decoder interleaves nonlinear steps, so
we work directly in the observation algebra `W = K ⊔ adjoin R {[x^i]P₇ : i < 7}` and
accumulate memberships — the "dynamic known context" style.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section Septic

variable (a₀ a₁ a₂ a₃ a₄ a₅ a₆ : A)

/-- The septic circuit of `lem:septic-base`. -/
noncomputable def septic : A[X] :=
  C a₀ + X * (X + C a₆)
    + (C a₃ + (C a₅ + X + X * (X + C a₆)) * (C a₄ + X)) * X
    + (C a₂ + X + (C a₅ + X + X * (X + C a₆)) * (C a₄ + X))
      * (C a₁ + (C a₃ + (C a₅ + X + X * (X + C a₆)) * (C a₄ + X)) * X)

/-- Fully expanded form of the septic (coefficients verified symbolically). -/
theorem septic_eq :
    septic a₀ a₁ a₂ a₃ a₄ a₅ a₆ =
      X ^ 7
        + C (2*a₄ + 2*a₆ + 2) * X ^ 6
        + C (a₄^2 + 4*a₄*a₆ + 4*a₄ + 2*a₅ + a₆^2 + 2*a₆ + 2) * X ^ 5
        + C (a₂ + a₃ + 2*a₄^2*a₆ + 2*a₄^2 + 4*a₄*a₅ + 2*a₄*a₆^2 + 4*a₄*a₆ + 3*a₄
              + 2*a₅*a₆ + 2*a₅ + a₆ + 2) * X ^ 4
        + C (a₁ + a₂*a₄ + a₂*a₆ + a₂ + a₃*a₄ + a₃*a₆ + a₃ + 2*a₄^2*a₅ + a₄^2*a₆^2
              + 2*a₄^2*a₆ + a₄^2 + 4*a₄*a₅*a₆ + 4*a₄*a₅ + a₄*a₆ + 2*a₄ + a₅^2 + a₅
              + a₆ + 1) * X ^ 3
        + C (a₁*a₄ + a₁*a₆ + a₁ + a₂*a₄*a₆ + a₂*a₄ + a₂*a₅ + a₃*a₄*a₆ + a₃*a₄ + a₃*a₅
              + a₃ + 2*a₄^2*a₅*a₆ + 2*a₄^2*a₅ + 2*a₄*a₅^2 + a₄*a₅ + a₄*a₆ + a₄ + a₅
              + 1) * X ^ 2
        + C (a₁*a₄*a₆ + a₁*a₄ + a₁*a₅ + a₁ + a₂*a₃ + a₂*a₄*a₅ + a₃*a₄*a₅ + a₃
              + a₄^2*a₅^2 + a₄*a₅ + a₆) * X
        + C (a₀ + a₁*a₂ + a₁*a₄*a₅) := by
  simp only [septic, map_add, map_mul, map_pow, map_one, map_ofNat]
  ring

theorem septic_coeff_6 : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff 6 = 2*a₄ + 2*a₆ + 2 := by
  rw [septic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem septic_coeff_5 : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff 5 =
    a₄^2 + 4*a₄*a₆ + 4*a₄ + 2*a₅ + a₆^2 + 2*a₆ + 2 := by
  rw [septic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem septic_coeff_4 : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff 4 =
    a₂ + a₃ + 2*a₄^2*a₆ + 2*a₄^2 + 4*a₄*a₅ + 2*a₄*a₆^2 + 4*a₄*a₆ + 3*a₄
      + 2*a₅*a₆ + 2*a₅ + a₆ + 2 := by
  rw [septic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem septic_coeff_3 : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff 3 =
    a₁ + a₂*a₄ + a₂*a₆ + a₂ + a₃*a₄ + a₃*a₆ + a₃ + 2*a₄^2*a₅ + a₄^2*a₆^2
      + 2*a₄^2*a₆ + a₄^2 + 4*a₄*a₅*a₆ + 4*a₄*a₅ + a₄*a₆ + 2*a₄ + a₅^2 + a₅ + a₆ + 1 := by
  rw [septic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem septic_coeff_2 : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff 2 =
    a₁*a₄ + a₁*a₆ + a₁ + a₂*a₄*a₆ + a₂*a₄ + a₂*a₅ + a₃*a₄*a₆ + a₃*a₄ + a₃*a₅
      + a₃ + 2*a₄^2*a₅*a₆ + 2*a₄^2*a₅ + 2*a₄*a₅^2 + a₄*a₅ + a₄*a₆ + a₄ + a₅ + 1 := by
  rw [septic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem septic_coeff_1 : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff 1 =
    a₁*a₄*a₆ + a₁*a₄ + a₁*a₅ + a₁ + a₂*a₃ + a₂*a₄*a₅ + a₃*a₄*a₅ + a₃
      + a₄^2*a₅^2 + a₄*a₅ + a₆ := by
  rw [septic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem septic_coeff_0 : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff 0 =
    a₀ + a₁*a₂ + a₁*a₄*a₅ := by
  rw [septic_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

section decoder

variable (K : Subalgebra R A)

/-- The observation algebra of the septic: known context plus the seven low coefficients. -/
noncomputable def septicObs : Subalgebra R A :=
  K ⊔ adjoin R ((fun i => (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff i) '' Set.Iio 7)

theorem coeff_mem_septicObs {i : ℕ} (hi : i < 7) :
    (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff i ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K :=
  (le_sup_right :
      adjoin R ((fun i => (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff i) '' Set.Iio 7)
        ≤ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K)
    (subset_adjoin ⟨i, hi, rfl⟩)

/-- **The septic is decodable** (`lem:septic-base`): if `2` is a unit in `R`, every parameter
lies in the observation algebra `K ⊔ adjoin R {[x^i]P₇ : i < 7}`. -/
theorem septic_decodable (h2 : IsUnit (2 : R)) :
    a₀ ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K ∧ a₁ ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K ∧
    a₂ ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K ∧ a₃ ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K ∧
    a₄ ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K ∧ a₅ ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K ∧
    a₆ ∈ septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K := by
  set W := septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K with hW
  -- the seven visible coefficients, in explicit form
  have hc6 : (2*a₄ + 2*a₆ + 2 : A) ∈ W := by
    have h := coeff_mem_septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K (by norm_num : (6:ℕ) < 7)
    rwa [septic_coeff_6] at h
  have hc5 : (a₄^2 + 4*a₄*a₆ + 4*a₄ + 2*a₅ + a₆^2 + 2*a₆ + 2 : A) ∈ W := by
    have h := coeff_mem_septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K (by norm_num : (5:ℕ) < 7)
    rwa [septic_coeff_5] at h
  have hc4 : (a₂ + a₃ + 2*a₄^2*a₆ + 2*a₄^2 + 4*a₄*a₅ + 2*a₄*a₆^2 + 4*a₄*a₆ + 3*a₄
      + 2*a₅*a₆ + 2*a₅ + a₆ + 2 : A) ∈ W := by
    have h := coeff_mem_septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K (by norm_num : (4:ℕ) < 7)
    rwa [septic_coeff_4] at h
  have hc3 : (a₁ + a₂*a₄ + a₂*a₆ + a₂ + a₃*a₄ + a₃*a₆ + a₃ + 2*a₄^2*a₅ + a₄^2*a₆^2
      + 2*a₄^2*a₆ + a₄^2 + 4*a₄*a₅*a₆ + 4*a₄*a₅ + a₄*a₆ + 2*a₄ + a₅^2 + a₅ + a₆ + 1 : A)
      ∈ W := by
    have h := coeff_mem_septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K (by norm_num : (3:ℕ) < 7)
    rwa [septic_coeff_3] at h
  have hc2 : (a₁*a₄ + a₁*a₆ + a₁ + a₂*a₄*a₆ + a₂*a₄ + a₂*a₅ + a₃*a₄*a₆ + a₃*a₄ + a₃*a₅
      + a₃ + 2*a₄^2*a₅*a₆ + 2*a₄^2*a₅ + 2*a₄*a₅^2 + a₄*a₅ + a₄*a₆ + a₄ + a₅ + 1 : A)
      ∈ W := by
    have h := coeff_mem_septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K (by norm_num : (2:ℕ) < 7)
    rwa [septic_coeff_2] at h
  have hc1 : (a₁*a₄*a₆ + a₁*a₄ + a₁*a₅ + a₁ + a₂*a₃ + a₂*a₄*a₅ + a₃*a₄*a₅ + a₃
      + a₄^2*a₅^2 + a₄*a₅ + a₆ : A) ∈ W := by
    have h := coeff_mem_septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K (by norm_num : (1:ℕ) < 7)
    rwa [septic_coeff_1] at h
  have hc0 : (a₀ + a₁*a₂ + a₁*a₄*a₅ : A) ∈ W := by
    have h := coeff_mem_septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ K (by norm_num : (0:ℕ) < 7)
    rwa [septic_coeff_0] at h
  -- Step 1: z₂ = α₄ + 1 + α₆  (from c₆ = 2z₂)
  have hz2 : (a₄ + 1 + a₆ : A) ∈ W := mem_of_two_mul_eq h2 hc6 (by ring)
  -- Step 2: z₁ = α₄(1 + α₆) + α₅  (from c₅ = z₂² + 2z₁ + 1)
  have hz1 : (a₄ * (1 + a₆) + a₅ : A) ∈ W :=
    mem_of_two_mul_eq h2 (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hc5
      (Subalgebra.mul_mem _ hz2 hz2)) (Subalgebra.one_mem _)) (by ring)
  -- Step 3: R' = 2z₀ + α₂ + α₃  (from c₄, no division needed)
  have hR : (2 * (a₄ * a₅) + a₂ + a₃ : A) ∈ W := by
    have key : (2 * (a₄ * a₅) + a₂ + a₃ : A) =
        (a₂ + a₃ + 2*a₄^2*a₆ + 2*a₄^2 + 4*a₄*a₅ + 2*a₄*a₆^2 + 4*a₄*a₆ + 3*a₄
          + 2*a₅*a₆ + 2*a₅ + a₆ + 2)
        - 1 - ((a₄ + 1 + a₆) * (a₄ * (1 + a₆) + a₅) + (a₄ + 1 + a₆) * (a₄ * (1 + a₆) + a₅))
        - (a₄ + 1 + a₆) := by ring
    rw [key]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hc4
      (Subalgebra.one_mem _))
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ hz2 hz1) (Subalgebra.mul_mem _ hz2 hz1)))
      hz2
  -- Step 4: α₁  (from c₃)
  have ha1 : a₁ ∈ W := by
    have key : a₁ =
        (a₁ + a₂*a₄ + a₂*a₆ + a₂ + a₃*a₄ + a₃*a₆ + a₃ + 2*a₄^2*a₅ + a₄^2*a₆^2
          + 2*a₄^2*a₆ + a₄^2 + 4*a₄*a₅*a₆ + 4*a₄*a₅ + a₄*a₆ + 2*a₄ + a₅^2 + a₅ + a₆ + 1)
        - (a₄ + 1 + a₆) - (a₄ + 1 + a₆) * (2 * (a₄ * a₅) + a₂ + a₃)
        - (a₄ * (1 + a₆) + a₅) * (a₄ * (1 + a₆) + a₅) - (a₄ * (1 + a₆) + a₅) := by ring
    rw [key]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ hc3 hz2) (Subalgebra.mul_mem _ hz2 hR))
      (Subalgebra.mul_mem _ hz1 hz1)) hz1
  -- Step 5: W' = z₀ + α₃  (from c₂)
  have hWq : (a₄ * a₅ + a₃ : A) ∈ W := by
    have key : (a₄ * a₅ + a₃ : A) =
        (a₁*a₄ + a₁*a₆ + a₁ + a₂*a₄*a₆ + a₂*a₄ + a₂*a₅ + a₃*a₄*a₆ + a₃*a₄ + a₃*a₅
          + a₃ + 2*a₄^2*a₅*a₆ + 2*a₄^2*a₅ + 2*a₄*a₅^2 + a₄*a₅ + a₄*a₆ + a₄ + a₅ + 1)
        - (a₄ * (1 + a₆) + a₅) - 1 - (a₄ + 1 + a₆) * a₁
        - (a₄ * (1 + a₆) + a₅) * (2 * (a₄ * a₅) + a₂ + a₃) := by ring
    rw [key]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _
      (Subalgebra.sub_mem _ hc2 hz1) (Subalgebra.one_mem _))
      (Subalgebra.mul_mem _ hz2 ha1)) (Subalgebra.mul_mem _ hz1 hR)
  -- Step 6: α₆  (from c₁)
  have ha6 : a₆ ∈ W := by
    have key : a₆ =
        (a₁*a₄*a₆ + a₁*a₄ + a₁*a₅ + a₁ + a₂*a₃ + a₂*a₄*a₅ + a₃*a₄*a₅ + a₃
          + a₄^2*a₅^2 + a₄*a₅ + a₆)
        - ((a₄ * (1 + a₆) + a₅) + 1) * a₁
        - (a₄ * a₅ + a₃) * ((2 * (a₄ * a₅) + a₂ + a₃) + 1 - (a₄ * a₅ + a₃)) := by ring
    rw [key]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hc1
      (Subalgebra.mul_mem _ (Subalgebra.add_mem _ hz1 (Subalgebra.one_mem _)) ha1))
      (Subalgebra.mul_mem _ hWq (Subalgebra.sub_mem _
        (Subalgebra.add_mem _ hR (Subalgebra.one_mem _)) hWq))
  -- Step 7: α₄ = z₂ - 1 - α₆
  have ha4 : a₄ ∈ W := by
    have key : a₄ = (a₄ + 1 + a₆) - 1 - a₆ := by ring
    rw [key]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hz2 (Subalgebra.one_mem _)) ha6
  -- Step 8: α₅ = z₁ - α₄(1 + α₆)
  have ha5 : a₅ ∈ W := by
    have key : a₅ = (a₄ * (1 + a₆) + a₅) - a₄ * (1 + a₆) := by ring
    rw [key]
    exact Subalgebra.sub_mem _ hz1 (Subalgebra.mul_mem _ ha4
      (Subalgebra.add_mem _ (Subalgebra.one_mem _) ha6))
  -- Step 9: α₃ = W' - α₄α₅
  have ha3 : a₃ ∈ W := by
    have key : a₃ = (a₄ * a₅ + a₃) - a₄ * a₅ := by ring
    rw [key]
    exact Subalgebra.sub_mem _ hWq (Subalgebra.mul_mem _ ha4 ha5)
  -- Step 10: α₂ = R' - 2α₄α₅ - α₃
  have ha2 : a₂ ∈ W := by
    have key : a₂ = (2 * (a₄ * a₅) + a₂ + a₃) - (a₄ * a₅ + a₄ * a₅) - a₃ := by ring
    rw [key]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ hR
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha4 ha5) (Subalgebra.mul_mem _ ha4 ha5)))
      ha3
  -- Step 11: α₀ = c₀ - (α₄α₅ + α₂)α₁
  have ha0 : a₀ ∈ W := by
    have key : a₀ = (a₀ + a₁*a₂ + a₁*a₄*a₅) - (a₄ * a₅ + a₂) * a₁ := by ring
    rw [key]
    exact Subalgebra.sub_mem _ hc0 (Subalgebra.mul_mem _
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha4 ha5) ha2) ha1)
  exact ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6⟩

/-- Decode the septic against any subalgebra containing its seven low coefficients:
the `K = ⊥` observation algebra pushes forward along `septicObs ⊥ ≤ V`. -/
theorem septic_decodable_of_coeff_mem (h2 : IsUnit (2 : R)) {V : Subalgebra R A}
    (hV : ∀ i, i < 7 → (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).coeff i ∈ V) :
    a₀ ∈ V ∧ a₁ ∈ V ∧ a₂ ∈ V ∧ a₃ ∈ V ∧ a₄ ∈ V ∧ a₅ ∈ V ∧ a₆ ∈ V := by
  have hle : septicObs a₀ a₁ a₂ a₃ a₄ a₅ a₆ ⊥ ≤ V := by
    refine sup_le bot_le (Algebra.adjoin_le ?_)
    rintro x ⟨j, hj, rfl⟩
    exact hV j (Set.mem_Iio.mp hj)
  obtain ⟨p0, p1, p2, p3, p4, p5, p6⟩ :=
    septic_decodable a₀ a₁ a₂ a₃ a₄ a₅ a₆ ⊥ h2
  exact ⟨hle p0, hle p1, hle p2, hle p3, hle p4, hle p5, hle p6⟩

end decoder

/-- The septic is monic of degree `7`. -/
theorem septic_good [Nontrivial A] : (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).Monic ∧
    (septic a₀ a₁ a₂ a₃ a₄ a₅ a₆).natDegree = 7 := by
  rw [septic_eq]
  have step : ∀ (P : A[X]) (b : A) (i : ℕ), P.Monic → P.natDegree = 7 → i ≤ 6 →
      (P + C b * X ^ i).Monic ∧ (P + C b * X ^ i).natDegree = 7 := by
    intro P b i hm hd hi
    have hle : (C b * X ^ i).natDegree ≤ i :=
      le_trans natDegree_mul_le (by rw [natDegree_C, natDegree_X_pow]; omega)
    obtain ⟨hm', hd'⟩ := monic_add_low (e := C b * X ^ i) hm
      (Or.inr (by omega))
    exact ⟨hm', hd'.trans hd⟩
  obtain ⟨h1m, h1d⟩ := step (X ^ 7) _ 6 (monic_X_pow 7) (natDegree_X_pow 7)
    (by omega)
  obtain ⟨h2m, h2d⟩ := step _ _ 5 h1m h1d (by omega)
  obtain ⟨h3m, h3d⟩ := step _ _ 4 h2m h2d (by omega)
  obtain ⟨h4m, h4d⟩ := step _ _ 3 h3m h3d (by omega)
  obtain ⟨h5m, h5d⟩ := step _ _ 2 h4m h4d (by omega)
  have hX1 : ∀ (P : A[X]) (b : A), P.Monic → P.natDegree = 7 →
      (P + C b * X).Monic ∧ (P + C b * X).natDegree = 7 := by
    intro P b hm hd
    have hle : (C b * X : A[X]).natDegree ≤ 1 :=
      le_trans natDegree_mul_le (by rw [natDegree_C, natDegree_X])
    obtain ⟨hm', hd'⟩ := monic_add_low (e := C b * X) hm (Or.inr (by omega))
    exact ⟨hm', hd'.trans hd⟩
  obtain ⟨h6m, h6d⟩ := hX1 _ _ h5m h5d
  obtain ⟨h7m, h7d⟩ := monic_add_low (e := C (a₀ + a₁*a₂ + a₁*a₄*a₅)) h6m
    (Or.inr (by rw [natDegree_C, h6d]; omega))
  exact ⟨h7m, h7d.trans h6d⟩

end Septic

end FastPoly
