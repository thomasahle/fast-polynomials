import FastPoly.Recover.Context
import FastPoly.Recover.Filtered
import Mathlib.Data.Fin.VecNotation

/-!
# Checkpoint example: the `Q₃` gadget

`Q₃[α₀,α₁,α₂](x, H) = (x + α₂)(H + α₁) + α₀` for a known monic quadratic `H`
(paper: the `Q₃` lemma in `sections/constructions.tex`).

We prove that the three parameters are recoverable from the three low coefficients of `Q₃`
given the coefficients of `H`, as an instance of the scalar triangular engine
`mem_obsAlg_of_scalarCert`: the pivot table is

  degree | parameter | slope
  -------|-----------|------
    2    |    α₂     |  1
    1    |    α₁     |  1
    0    |    α₀     |  1
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section Q3

variable (H : A[X]) (a₀ a₁ a₂ : A)

/-- The `Q₃` gadget `(X + α₂)(H + α₁) + α₀`. -/
noncomputable def Q₃ : A[X] := (X + C a₂) * (H + C a₁) + C a₀

variable {H} (hH : H.Monic) (hd : H.natDegree = 2)

include hH hd

theorem Q₃_coeff_two : (Q₃ H a₀ a₁ a₂).coeff 2 = a₂ + H.coeff 1 := by
  have h2 : H.coeff 2 = 1 := by rw [← hd]; exact hH.coeff_natDegree
  simp [Q₃, mul_add, add_mul, coeff_X_mul, coeff_C_mul, h2]
  ring

omit hH hd in
theorem Q₃_coeff_one : (Q₃ H a₀ a₁ a₂).coeff 1 = a₁ + (H.coeff 0 + a₂ * H.coeff 1) := by
  simp [Q₃, mul_add, add_mul, coeff_X_mul, coeff_C_mul, coeff_C]
  ring

omit hH hd in
theorem Q₃_coeff_zero : (Q₃ H a₀ a₁ a₂).coeff 0 = a₀ + a₂ * (H.coeff 0 + a₁) := by
  simp [Q₃, mul_add, add_mul, coeff_C]
  ring

/-- **`Q₃` is decodable given `H`** (an instance of the scalar triangular engine):
each parameter `αᵢ` is a polynomial over `R` in the coefficients of `H` and the
coefficients of `Q₃` of degree `≥ i`. -/
theorem Q₃_decodable (K : Subalgebra R A) (hK : ∀ j, H.coeff j ∈ K) :
    ∀ i : Fin 3, ![a₀, a₁, a₂] i ∈
      obsAlg K (fun j : Fin 3 => (Q₃ H a₀ a₁ a₂).coeff (j : ℕ)) i := by
  apply mem_obsAlg_of_scalarCert K _ _ (fun _ => (1 : R)) (fun _ => isUnit_one)
  intro j
  have hmem : ∀ (i : Fin 3), i ∈ Set.Ioi j →
      ![a₀, a₁, a₂] i ∈ laterAlg K ![a₀, a₁, a₂] j := fun i hi =>
    (le_sup_right : adjoin R _ ≤ laterAlg K ![a₀, a₁, a₂] j)
      (subset_adjoin ⟨i, hi, rfl⟩)
  have hKmem : ∀ b ∈ K, b ∈ laterAlg K ![a₀, a₁, a₂] j :=
    fun b hb => (le_sup_left : K ≤ laterAlg K ![a₀, a₁, a₂] j) hb
  fin_cases j
  · -- degree 0 pivot: α₀
    refine ⟨a₂ * (H.coeff 0 + a₁), ?_, ?_⟩
    · exact Subalgebra.mul_mem _ (hmem 2 (by decide))
        (Subalgebra.add_mem _ (hKmem _ (hK 0)) (hmem 1 (by decide)))
    · rw [Q₃_coeff_zero a₀ a₁ a₂, map_one, one_mul]
      norm_num
  · -- degree 1 pivot: α₁
    refine ⟨H.coeff 0 + a₂ * H.coeff 1, ?_, ?_⟩
    · exact Subalgebra.add_mem _ (hKmem _ (hK 0))
        (Subalgebra.mul_mem _ (hmem 2 (by decide)) (hKmem _ (hK 1)))
    · rw [Q₃_coeff_one a₀ a₁ a₂, map_one, one_mul]
      norm_num
  · -- degree 2 pivot: α₂
    refine ⟨H.coeff 1, hKmem _ (hK 1), ?_⟩
    rw [Q₃_coeff_two a₀ a₁ a₂ hH hd, map_one, one_mul]
    norm_num

end Q3

end FastPoly
