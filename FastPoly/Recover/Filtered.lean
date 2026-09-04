import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.Fintype.Order
import FastPoly.Recover.Context

/-!
# Triangular (de Jonquières) recovery in a filtered subalgebra

The one generic theorem behind every "pivot table" of `sections/constructions.tex`.

Let `K` be a known context and `α : ι → A` a family of unknowns indexed by a well-founded
order (`ι = Fin n`, say).  Define the filtration

  `F j = K ⊔ adjoin R {α i | i > j}`      ("everything decoded strictly later than `j`").

A **scalar certificate** is a family of observations `D j = λ j • α j + e j` with `λ j` a unit
of `R` and `e j ∈ F j`.  Descending induction shows that every `α j` lies in
`K ⊔ adjoin R {D i | i ≥ j}` — i.e. the unknowns are polynomial in the observations, with the
correct causal cutoff.

A **block certificate** recovers several unknowns at once from as many observations, via a
matrix with an explicitly supplied inverse.  This is what the exceptional decoders (septic,
`Q̄₁₅`, `15`, `27`, `31`) need.
-/

namespace FastPoly

open Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section scalar

variable {ι : Type*} [Preorder ι]

/-- The filtration of the unknowns: `K` together with all `α i` for `i > j`. -/
def laterAlg (K : Subalgebra R A) (α : ι → A) (j : ι) : Subalgebra R A :=
  K ⊔ adjoin R (α '' Set.Ioi j)

/-- The observation algebra at cutoff `j`: `K` together with all `D i` for `i ≥ j`. -/
def obsAlg (K : Subalgebra R A) (D : ι → A) (j : ι) : Subalgebra R A :=
  K ⊔ adjoin R (D '' Set.Ici j)

theorem obsAlg_antitone (K : Subalgebra R A) (D : ι → A) {i j : ι} (h : j ≤ i) :
    obsAlg K D i ≤ obsAlg K D j :=
  sup_le_sup_left (adjoin_mono (Set.image_mono fun _ hx => le_trans h hx)) _

theorem obs_mem_obsAlg (K : Subalgebra R A) (D : ι → A) (j : ι) : D j ∈ obsAlg K D j :=
  (le_sup_right : adjoin R (D '' Set.Ici j) ≤ obsAlg K D j) (subset_adjoin ⟨j, Set.self_mem_Ici, rfl⟩)

theorem known_le_obsAlg (K : Subalgebra R A) (D : ι → A) (j : ι) : K ≤ obsAlg K D j :=
  le_sup_left

/-- **Scalar triangular recovery.**  If each observation `D j` is `λ j • α j` plus something
decoded strictly later, with `λ j` a unit, then every unknown `α j` is polynomial (over `R`,
given `K`) in the observations `D i`, `i ≥ j`. -/
theorem mem_obsAlg_of_scalarCert [WellFoundedGT ι] (K : Subalgebra R A) (α D : ι → A)
    (lam : ι → R)
    (hunit : ∀ j, IsUnit (lam j))
    (hD : ∀ j, ∃ e ∈ laterAlg K α j, D j = algebraMap R A (lam j) * α j + e) :
    ∀ j, α j ∈ obsAlg K D j := by
  intro j
  induction j using WellFoundedGT.induction with
  | _ j ih =>
    obtain ⟨e, he, hDj⟩ := hD j
    -- everything decoded later is already in the observation algebra at cutoff `j`
    have hlater : laterAlg K α j ≤ obsAlg K D j := by
      refine sup_le (known_le_obsAlg K D j) (adjoin_le ?_)
      rintro _ ⟨i, hi, rfl⟩
      exact obsAlg_antitone K D (le_of_lt hi) (ih i hi)
    exact mem_of_unit_slope (hunit j)
      (Subalgebra.sub_mem _ (obs_mem_obsAlg K D j) (hlater he))
      (by rw [hDj]; ring)

end scalar

section block

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Block recovery.**  If the observations `D` are an affine image `D = M α + e` of the
unknowns with `M` invertible over `R` (inverse `N` supplied explicitly) and `e` known, then the
unknowns are polynomial in the observations given the known context. -/
theorem mem_of_blockCert (S : Subalgebra R A) (α D e : m → A) (M N : Matrix m m R)
    (hNM : N * M = 1) (he : ∀ i, e i ∈ S)
    (hD : ∀ i, D i = ∑ j, algebraMap R A (M i j) * α j + e i) :
    ∀ i, α i ∈ S ⊔ adjoin R (Set.range D) := by
  intro i
  have key : ∑ j, algebraMap R A (N i j) * (D j - e j) = α i := by
    calc ∑ j, algebraMap R A (N i j) * (D j - e j)
        = ∑ j, ∑ k, algebraMap R A (N i j * M j k) * α k := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hD j, add_sub_cancel_right, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul, mul_assoc]
      _ = ∑ k, algebraMap R A (∑ j, N i j * M j k) * α k := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_sum, Finset.sum_mul]
      _ = ∑ k, algebraMap R A ((N * M) i k) * α k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.mul_apply]
      _ = α i := by
          rw [hNM]
          simp [Matrix.one_apply, apply_ite (algebraMap R A), ite_mul]
  rw [← key]
  refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.sub_mem _ ?_ ((le_sup_left : S ≤ S ⊔ adjoin R (Set.range D)) (he j)))
  exact (le_sup_right : adjoin R (Set.range D) ≤ S ⊔ adjoin R (Set.range D))
    (subset_adjoin ⟨j, rfl⟩)

end block

end FastPoly
