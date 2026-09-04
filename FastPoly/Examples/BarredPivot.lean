import FastPoly.Recover.KnownBlock
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

namespace FastPoly

open Algebra Matrix

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

private def barredUL (A₁ : A) : Matrix (Fin 2) (Fin 2) A :=
  !![1, 0; A₁, 1]

private def barredUR (κ A₁ : A) : Matrix (Fin 2) (Fin 2) A :=
  !![κ, κ; κ * (A₁ + 1), κ * (A₁ + 1)]

private def barredLL (C D E F : A) : Matrix (Fin 2) (Fin 2) A :=
  !![C, D; E, F]

private def barredLR (κ C D E F L : A) : Matrix (Fin 2) (Fin 2) A :=
  !![κ * (C + D), κ * (C + D - 1);
     κ * (E + F - 1), κ * (E + F - L)]

/-- The two simultaneous column operations `C₃,C₄ ← C₃,C₄ - κ(C₁+C₂)`. -/
private def barredShear (κ : A) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) A :=
  Matrix.fromBlocks 1 !![-κ, -κ; -κ, -κ] 0 1

private def barredPivotBlock (κ A₁ C D E F L : A) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) A :=
  Matrix.fromBlocks (barredUL A₁) (barredUR κ A₁) (barredLL C D E F)
    (barredLR κ C D E F L)

private def barredReducedBlock (κ A₁ C D E F L : A) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) A :=
  Matrix.fromBlocks (barredUL A₁) 0 (barredLL C D E F)
    !![0, -κ; -κ, -κ * L]

/-- Multiplication by the unit block shear performs exactly the two displayed column
operations from the paper. -/
private theorem barredPivotBlock_mul_shear (κ A₁ C D E F L : A) :
    barredPivotBlock κ A₁ C D E F L * barredShear κ =
      barredReducedBlock κ A₁ C D E F L := by
  rw [barredPivotBlock, barredShear, barredReducedBlock, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_inj]
  refine ⟨by simp, ?_, by simp, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [barredUL, barredUR]
    all_goals ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [barredLL, barredLR]
    all_goals ring

private theorem barredShear_det (κ : A) : (barredShear κ).det = 1 := by
  rw [barredShear, Matrix.det_fromBlocks_zero₂₁]
  simp

private theorem barredReducedBlock_det (κ A₁ C D E F L : A) :
    (barredReducedBlock κ A₁ C D E F L).det = -(κ ^ 2) := by
  rw [barredReducedBlock, Matrix.det_fromBlocks_zero₁₂]
  simp [barredUL, Matrix.det_fin_two]
  ring

private theorem barredPivotBlock_det (κ A₁ C D E F L : A) :
    (barredPivotBlock κ A₁ C D E F L).det = -(κ ^ 2) := by
  have h := congrArg Matrix.det (barredPivotBlock_mul_shear κ A₁ C D E F L)
  rw [Matrix.det_mul, barredShear_det, mul_one, barredReducedBlock_det] at h
  exact h

/-- The four simultaneous pivots in the barred `8k+7` gadget. -/
def barredPivotMatrix (k : R) (A₁ C D E F L : A) : Matrix (Fin 4) (Fin 4) A :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv
    (barredPivotBlock (algebraMap R A k) A₁ C D E F L)

/-- Entrywise form of `barredPivotMatrix`, matching the displayed matrix in the paper. -/
theorem barredPivotMatrix_eq (k : R) (A₁ C D E F L : A) :
    barredPivotMatrix k A₁ C D E F L =
      let κ := algebraMap R A k
      !![1, 0, κ, κ;
         A₁, 1, κ * (A₁ + 1), κ * (A₁ + 1);
         C, D, κ * (C + D), κ * (C + D - 1);
         E, F, κ * (E + F - 1), κ * (E + F - L)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [barredPivotMatrix, barredPivotBlock, barredUL, barredUR, barredLL, barredLR,
      Matrix.reindex_apply, finSumFinEquiv, Fin.addCases]

/-- The barred pivot has the fixed determinant `-k²`, independently of all quantities
decoded in earlier rows.  The proof is the paper's pair of column operations, expressed as
multiplication by a unit block shear. -/
theorem barredPivotMatrix_det (k : R) (A₁ C D E F L : A) :
    (barredPivotMatrix k A₁ C D E F L).det = algebraMap R A (-(k ^ 2)) := by
  rw [barredPivotMatrix, Matrix.det_reindex_self, barredPivotBlock_det, map_neg, map_pow]

/-- Explicit recovery for the barred four-pivot block.  The six nonconstant matrix
quantities must have been decoded in earlier rows; the only inverse required is the fixed
unit `-k²`. -/
theorem mem_of_barredPivotCert (S : Subalgebra R A) (α y e : Fin 4 → A)
    (k : R) (A₁ C D E F L : A) (hk : IsUnit k)
    (hM : ∀ i j, barredPivotMatrix k A₁ C D E F L i j ∈ S)
    (he : ∀ i, e i ∈ S)
    (hy : ∀ i, y i = ∑ j, barredPivotMatrix k A₁ C D E F L i j * α j + e i) :
    ∀ i, α i ∈ S ⊔ adjoin R (Set.range y) := by
  exact mem_of_known_blockCert_of_det S α y e (barredPivotMatrix k A₁ C D E F L)
    (-(k ^ 2)) (hk.pow 2).neg (barredPivotMatrix_det k A₁ C D E F L) hM he hy

end FastPoly
