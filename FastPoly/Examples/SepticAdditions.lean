import FastPoly.Examples.Septic

/-!
# The ten-addition septic schedule

The manuscript saves one addition in the direct degree-seven circuit by absorbing the
summand `β₁ + w` into the last product.  This file verifies that optimization algebraically
and transports the original explicit decoder across the affine coordinate change

`α₀ = β₀ + β₁`, `α₁ = β₁`, `α₂ = β₂ - 1`.

The proof is an identity followed by substitution; it does not infer invertibility from a
Jacobian calculation.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section OptimizedSeptic

variable (b₀ b₁ b₂ b₃ b₄ b₅ b₆ : A)

private noncomputable def addSepticY : A[X] :=
  X * (X + C b₆)

private noncomputable def addSepticZ : A[X] :=
  (C b₅ + X + addSepticY b₆) * (C b₄ + X)

private noncomputable def addSepticW : A[X] :=
  (C b₃ + addSepticZ b₄ b₅ b₆) * X

/-- The four-product septic after the addition-saving affine reparameterization.  Its ten
additions are the ten affine/output gates displayed in `sec:addition-count`. -/
noncomputable def optimizedSeptic : A[X] :=
  C b₀ + addSepticY b₆ +
    (C b₂ + X + addSepticZ b₄ b₅ b₆) *
      (C b₁ + addSepticW b₃ b₄ b₅ b₆)

/-- The optimized circuit is the original septic after the manuscript's invertible affine
change of coordinates. -/
theorem optimizedSeptic_eq_septic :
    optimizedSeptic b₀ b₁ b₂ b₃ b₄ b₅ b₆ =
      septic (b₀ + b₁) b₁ (b₂ - 1) b₃ b₄ b₅ b₆ := by
  simp only [optimizedSeptic, addSepticY, addSepticZ, addSepticW, septic,
    map_add, map_sub, map_one]
  ring

variable (K : Subalgebra R A)

noncomputable def optimizedSepticObs : Subalgebra R A :=
  K ⊔ adjoin R
    ((fun i => (optimizedSeptic b₀ b₁ b₂ b₃ b₄ b₅ b₆).coeff i) '' Set.Iio 7)

theorem optimizedSepticObs_eq :
    optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K =
      septicObs (b₀ + b₁) b₁ (b₂ - 1) b₃ b₄ b₅ b₆ K := by
  rw [optimizedSepticObs, septicObs, optimizedSeptic_eq_septic]

/-- The ten-addition septic retains the original explicit decoder. -/
theorem optimizedSeptic_decodable (h2 : IsUnit (2 : R)) :
    b₀ ∈ optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K ∧
    b₁ ∈ optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K ∧
    b₂ ∈ optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K ∧
    b₃ ∈ optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K ∧
    b₄ ∈ optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K ∧
    b₅ ∈ optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K ∧
    b₆ ∈ optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K := by
  have h := septic_decodable (b₀ + b₁) b₁ (b₂ - 1) b₃ b₄ b₅ b₆ K h2
  rw [← optimizedSepticObs_eq b₀ b₁ b₂ b₃ b₄ b₅ b₆ K] at h
  rcases h with ⟨ha₀, hb₁, ha₂, hb₃, hb₄, hb₅, hb₆⟩
  let W := optimizedSepticObs b₀ b₁ b₂ b₃ b₄ b₅ b₆ K
  have hb₀ : b₀ ∈ W := by
    have hsub := Subalgebra.sub_mem W ha₀ hb₁
    simpa only [add_sub_cancel_right] using hsub
  have hb₂ : b₂ ∈ W := by
    have hadd := Subalgebra.add_mem W ha₂ (Subalgebra.one_mem W)
    simpa only [sub_add_cancel] using hadd
  exact ⟨hb₀, hb₁, hb₂, hb₃, hb₄, hb₅, hb₆⟩

end OptimizedSeptic

end FastPoly
