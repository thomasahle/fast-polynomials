import FastPoly.Recover.Filtered
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Block recovery with known, nonconstant matrix entries

The barred-gadget pivot matrix is not constant: its entries are polynomials in quantities
decoded in earlier rows.  What is constant is its determinant.  The existing
`mem_of_blockCert` covers a matrix over the scalar ring; the lemmas below are the natural
relative version.  They allow the matrix to live in the ambient algebra and require its
inverse entries to belong to the current known subalgebra.
-/

namespace FastPoly

open Algebra Matrix

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Relative block recovery.**  Suppose `D = M α + e`, where `e` is known and the
entries of a supplied left inverse `N` are known.  Then every unknown in the block is
polynomially recoverable from the observations `D` and the current known context.

The entries of `M` need not lie in the scalar ring, and no data-dependent division is
hidden here: an application must exhibit `N`, prove `N * M = 1`, and prove every entry of
`N` belongs to `S`. -/
theorem mem_of_known_blockCert (S : Subalgebra R A) (α D e : m → A)
    (M N : Matrix m m A) (hNM : N * M = 1) (hN : ∀ i j, N i j ∈ S)
    (he : ∀ i, e i ∈ S)
    (hD : ∀ i, D i = ∑ j, M i j * α j + e i) :
    ∀ i, α i ∈ S ⊔ adjoin R (Set.range D) := by
  intro i
  have key : ∑ j, N i j * (D j - e j) = α i := by
    calc
      ∑ j, N i j * (D j - e j)
          = ∑ j, ∑ k, (N i j * M j k) * α k := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [hD j, add_sub_cancel_right, Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [mul_assoc]
      _ = ∑ k, (∑ j, N i j * M j k) * α k := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.sum_mul]
      _ = ∑ k, (N * M) i k * α k := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Matrix.mul_apply]
      _ = α i := by
              rw [hNM]
              simp [Matrix.one_apply, ite_mul]
  rw [← key]
  refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _
    ((le_sup_left : S ≤ S ⊔ adjoin R (Set.range D)) (hN i j))
    (Subalgebra.sub_mem _ ?_
      ((le_sup_left : S ≤ S ⊔ adjoin R (Set.range D)) (he j)))
  exact (le_sup_right : adjoin R (Set.range D) ≤ S ⊔ adjoin R (Set.range D))
    (subset_adjoin ⟨j, rfl⟩)

/-- A determinant belongs to a subalgebra whenever all matrix entries do. -/
theorem matrix_det_mem (S : Subalgebra R A) (M : Matrix m m A)
    (hM : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine Subalgebra.sum_mem _ fun σ _ => Subalgebra.mul_mem _
    (Subalgebra.intCast_mem _ _) ?_
  exact Subalgebra.prod_mem _ fun i _ => hM (σ i) i

/-- Every adjugate entry is polynomial in the matrix entries, hence remains known. -/
theorem matrix_adjugate_mem (S : Subalgebra R A) (M : Matrix m m A)
    (hM : ∀ i j, M i j ∈ S) : ∀ i j, M.adjugate i j ∈ S := by
  intro i j
  rw [Matrix.adjugate_apply]
  apply matrix_det_mem S
  intro a b
  rw [Matrix.updateRow_apply]
  split
  · rw [Pi.single_apply]
    split
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  · exact hM a b

/-- **Constant-determinant block recovery.**  The pivot matrix may depend polynomially on
previously decoded quantities, but its determinant is the image of a fixed unit `r : R`.
The proof constructs the inverse `r⁻¹ adj(M)` explicitly and then applies
`mem_of_known_blockCert`. -/
theorem mem_of_known_blockCert_of_det (S : Subalgebra R A) (α D e : m → A)
    (M : Matrix m m A) (r : R) (hr : IsUnit r)
    (hdet : M.det = algebraMap R A r) (hM : ∀ i j, M i j ∈ S)
    (he : ∀ i, e i ∈ S)
    (hD : ∀ i, D i = ∑ j, M i j * α j + e i) :
    ∀ i, α i ∈ S ⊔ adjoin R (Set.range D) := by
  obtain ⟨u, hu⟩ := hr
  let N : Matrix m m A := algebraMap R A (↑u⁻¹) • M.adjugate
  have hscalar : algebraMap R A (↑u⁻¹) * M.det = 1 := by
    calc
      algebraMap R A (↑u⁻¹) * M.det
          = algebraMap R A (↑u⁻¹) * algebraMap R A r := by rw [hdet]
      _ = algebraMap R A (↑u⁻¹ * r) := by rw [map_mul]
      _ = 1 := by rw [← hu, Units.inv_mul, map_one]
  have hNM : N * M = 1 := by
    calc
      N * M = algebraMap R A (↑u⁻¹) • (M.adjugate * M) := by
        change (algebraMap R A (↑u⁻¹) • M.adjugate) * M = _
        rw [Matrix.smul_mul]
      _ = algebraMap R A (↑u⁻¹) • (M.det • (1 : Matrix m m A)) := by
        rw [Matrix.adjugate_mul]
      _ = (algebraMap R A (↑u⁻¹) * M.det) • (1 : Matrix m m A) := by
        rw [smul_smul]
      _ = 1 := by rw [hscalar, one_smul]
  have hN : ∀ i j, N i j ∈ S := by
    intro i j
    change algebraMap R A (↑u⁻¹) * M.adjugate i j ∈ S
    exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (matrix_adjugate_mem S M hM i j)
  exact mem_of_known_blockCert S α D e M N hNM hN he hD

end FastPoly
