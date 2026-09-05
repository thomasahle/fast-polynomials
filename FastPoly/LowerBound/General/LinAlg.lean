/-
The degree-six lower bound: explicit linear algebra for a `7 × 6` matrix — the left-kernel
vector from a nonzero minor, the left inverse, and the two kernels.
-/
import FastPoly.LowerBound.Jacobian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Linear algebra of the slot matrix `M : Matrix (Fin 7) (Fin 6) F`

Everything here is explicit (rule 1 of `AGENTS.md`): when the `6 × 6` minor `minor M i₀`
(row `i₀` deleted) is invertible, the left-kernel vector `ℓ = lker M i₀` is written down
from the inverse minor (`ℓ_{i₀} = 1`, `ℓ_S = −M_{i₀} (M_S)⁻¹`), the left inverse
`MplusVec M i₀` is the inverse minor applied to the corresponding six coordinates, and the
kernel vectors are built by pivots.

* `lker_vecMul`: `ℓᵀ M = 0`.
* `mulVec_MplusVec_of_dot_eq_zero`: `im M = ker ℓᵀ`, with the explicit preimage `M⁺ z`.
* `eq_smul_lker_of_vecMul_eq_zero`: the left kernel of `M` is spanned by `ℓ`.
* `exists_mulVec_eq_zero_of_forall_minor`: if every maximal minor vanishes, `M` has a
  nonzero kernel vector (seven vectors in `F⁶` are dependent: a `7 × 7` matrix with a zero
  row).
* `exists_solve_affine`: one affine equation in six unknowns is solved by a pivot.

(The appendix's `ℓ` is the cofactor vector `((−1)ⁱ det (minor M i))ᵢ`; when
`det (minor M i₀) ≠ 0` it is a nonzero multiple of `lker M i₀`, by
`eq_smul_lker_of_vecMul_eq_zero`, and nothing downstream depends on the normalization.)
-/

namespace FastPoly.LowerBound.General

open Matrix

/-! ## Index bookkeeping around `Fin.succAbove` -/

theorem funext_succAbove {α : Type*} {i₀ : Fin 7} {f g : Fin 7 → α} (h0 : f i₀ = g i₀)
    (h : ∀ k, f (i₀.succAbove k) = g (i₀.succAbove k)) : f = g := by
  funext i
  by_cases hi : i = i₀
  · rw [hi]
    exact h0
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hi
    exact h k

variable {F : Type*} [Field F]

theorem dotProduct_succAbove (i₀ : Fin 7) (v w : Fin 7 → F) :
    v ⬝ᵥ w = v i₀ * w i₀ + ∑ k, v (i₀.succAbove k) * w (i₀.succAbove k) :=
  Fin.sum_univ_succAbove (fun i => v i * w i) i₀

theorem vecMul_succAbove (i₀ : Fin 7) (w : Fin 7 → F) (M : Matrix (Fin 7) (Fin 6) F)
    (j : Fin 6) :
    (w ᵥ* M) j = w i₀ * M i₀ j + ∑ k, w (i₀.succAbove k) * M (i₀.succAbove k) j :=
  Fin.sum_univ_succAbove (fun i => w i * M i j) i₀

/-! ## Minors and the left-kernel vector -/

/-- The `6 × 6` minor of `M` with row `i` deleted. -/
def minor (M : Matrix (Fin 7) (Fin 6) F) (i : Fin 7) : Matrix (Fin 6) (Fin 6) F :=
  M.submatrix i.succAbove id

theorem minor_mulVec (M : Matrix (Fin 7) (Fin 6) F) (i₀ : Fin 7) (v : Fin 6 → F) :
    minor M i₀ *ᵥ v = (M *ᵥ v) ∘ i₀.succAbove := rfl

/-- The left-kernel vector normalized at `i₀`: `ℓ_{i₀} = 1`, `ℓ_S = −M_{i₀} (M_S)⁻¹` where
`S` = all rows but `i₀`. -/
noncomputable def lker (M : Matrix (Fin 7) (Fin 6) F) (i₀ : Fin 7) : Fin 7 → F :=
  Fin.insertNth i₀ 1 (-(M i₀ ᵥ* (minor M i₀)⁻¹))

theorem lker_same (M : Matrix (Fin 7) (Fin 6) F) (i₀ : Fin 7) : lker M i₀ i₀ = 1 :=
  Fin.insertNth_apply_same i₀ _ _

theorem lker_succAbove (M : Matrix (Fin 7) (Fin 6) F) (i₀ : Fin 7) (k : Fin 6) :
    lker M i₀ (i₀.succAbove k) = -(M i₀ ᵥ* (minor M i₀)⁻¹) k :=
  Fin.insertNth_apply_succAbove i₀ _ _ k

theorem lker_ne_zero (M : Matrix (Fin 7) (Fin 6) F) (i₀ : Fin 7) : lker M i₀ i₀ ≠ 0 := by
  rw [lker_same]
  exact one_ne_zero

/-- **`ℓᵀ M = 0`.** -/
theorem lker_vecMul (M : Matrix (Fin 7) (Fin 6) F) {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) :
    lker M i₀ ᵥ* M = 0 := by
  funext j
  rw [vecMul_succAbove i₀, lker_same, one_mul]
  have hS : ∑ k, lker M i₀ (i₀.succAbove k) * M (i₀.succAbove k) j
      = ((-(M i₀ ᵥ* (minor M i₀)⁻¹)) ᵥ* minor M i₀) j := by
    simp only [lker_succAbove]
    rfl
  rw [hS, Matrix.neg_vecMul, Matrix.vecMul_vecMul,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), Matrix.vecMul_one, Pi.neg_apply,
    add_neg_cancel, Pi.zero_apply]

/-! ## The left inverse from a nonzero minor -/

/-- The explicit left inverse `M⁺ z = (M_S)⁻¹ z_S`, `S` = all rows but `i₀`. -/
noncomputable def MplusVec (M : Matrix (Fin 7) (Fin 6) F) (i₀ : Fin 7) (z : Fin 7 → F) :
    Fin 6 → F :=
  (minor M i₀)⁻¹ *ᵥ (z ∘ i₀.succAbove)

/-- `M⁺ M = 1`. -/
theorem MplusVec_mulVec (M : Matrix (Fin 7) (Fin 6) F) {i₀ : Fin 7}
    (hd : (minor M i₀).det ≠ 0) (v : Fin 6 → F) : MplusVec M i₀ (M *ᵥ v) = v := by
  rw [MplusVec, ← minor_mulVec, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd), Matrix.one_mulVec]

/-- **`im M = ker ℓᵀ`**, with the explicit preimage `M⁺ z`. -/
theorem mulVec_MplusVec_of_dot_eq_zero (M : Matrix (Fin 7) (Fin 6) F) {i₀ : Fin 7}
    (hd : (minor M i₀).det ≠ 0) (z : Fin 7 → F) (hz : lker M i₀ ⬝ᵥ z = 0) :
    M *ᵥ MplusVec M i₀ z = z := by
  have hu : IsUnit (minor M i₀).det := isUnit_iff_ne_zero.mpr hd
  have ha : (M *ᵥ MplusVec M i₀ z) ∘ i₀.succAbove = z ∘ i₀.succAbove := by
    rw [← minor_mulVec, MplusVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mulVec]
  have ha' : ∀ k, (M *ᵥ MplusVec M i₀ z) (i₀.succAbove k) = z (i₀.succAbove k) :=
    fun k => congrFun ha k
  have hb : lker M i₀ ⬝ᵥ (M *ᵥ MplusVec M i₀ z) = 0 := by
    rw [Matrix.dotProduct_mulVec, lker_vecMul M hd, zero_dotProduct]
  rw [dotProduct_succAbove i₀] at hb hz
  have hrest : ∑ k, lker M i₀ (i₀.succAbove k) * (M *ᵥ MplusVec M i₀ z) (i₀.succAbove k)
      = ∑ k, lker M i₀ (i₀.succAbove k) * z (i₀.succAbove k) :=
    Finset.sum_congr rfl fun k _ => by rw [ha' k]
  rw [hrest] at hb
  have hi₀ : (M *ᵥ MplusVec M i₀ z) i₀ = z i₀ :=
    mul_left_cancel₀ (lker_ne_zero M i₀) (by linear_combination hb - hz)
  exact funext_succAbove hi₀ ha'

/-! ## The left kernel -/

theorem eq_zero_of_vecMul_eq_zero (M : Matrix (Fin 7) (Fin 6) F) {i₀ : Fin 7}
    (hd : (minor M i₀).det ≠ 0) (w : Fin 7 → F) (hw : w ᵥ* M = 0) (h0 : w i₀ = 0) : w = 0 := by
  have hres : (w ∘ i₀.succAbove) ᵥ* minor M i₀ = 0 := by
    funext j
    have hj := congrFun hw j
    rw [vecMul_succAbove i₀, h0, zero_mul, zero_add] at hj
    exact hj
  have hzero : w ∘ i₀.succAbove = 0 := by
    by_contra hne
    exact hd (Matrix.exists_vecMul_eq_zero_iff.mp ⟨w ∘ i₀.succAbove, hne, hres⟩)
  exact funext_succAbove h0 fun k => congrFun hzero k

/-- **The left kernel of `M` is spanned by `ℓ`.** -/
theorem eq_smul_lker_of_vecMul_eq_zero (M : Matrix (Fin 7) (Fin 6) F) {i₀ : Fin 7}
    (hd : (minor M i₀).det ≠ 0) (w : Fin 7 → F) (hw : w ᵥ* M = 0) :
    w = w i₀ • lker M i₀ := by
  have h1 : (w - w i₀ • lker M i₀) ᵥ* M = 0 := by
    rw [Matrix.sub_vecMul, Matrix.smul_vecMul, hw, lker_vecMul M hd, smul_zero, sub_zero]
  have h2 : (w - w i₀ • lker M i₀) i₀ = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, lker_same, mul_one, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_vecMul_eq_zero M hd _ h1 h2)

/-! ## All maximal minors zero ⇒ a kernel vector -/

/-- The standard basis vector `eᵢ ∈ F⁷`. -/
def e7 (i : Fin 7) : Fin 7 → F := fun k => if k = i then 1 else 0

theorem e7_same (i : Fin 7) : e7 (F := F) i i = 1 := by
  simp [e7]

theorem e7_ne {i k : Fin 7} (h : k ≠ i) : e7 (F := F) i k = 0 := by
  simp [e7, h]

/-- If every `6 × 6` minor of `M` vanishes then `M` has a nonzero kernel vector.  Explicit:
for each row `i` either the minor's kernel vector is a kernel vector of `M`, or its rescaling
`sᵢ` has `M sᵢ = eᵢ`; seven vectors `sᵢ ∈ F⁶` are dependent (the `7 × 7` matrix with rows
`0, s₀, …` has a zero row), and the dependence `∑ aᵢ sᵢ = 0` gives `a = M (∑ aᵢ sᵢ) = 0`. -/
theorem exists_mulVec_eq_zero_of_forall_minor (M : Matrix (Fin 7) (Fin 6) F)
    (h : ∀ i, (minor M i).det = 0) : ∃ v : Fin 6 → F, v ≠ 0 ∧ M *ᵥ v = 0 := by
  have key : ∀ i : Fin 7, (∃ v : Fin 6 → F, v ≠ 0 ∧ M *ᵥ v = 0)
      ∨ ∃ v : Fin 6 → F, M *ᵥ v = e7 i := by
    intro i
    obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (h i)
    have hrest : ∀ k, (M *ᵥ v) (i.succAbove k) = 0 := fun k => by
      have hk := congrFun hMv k
      rw [minor_mulVec] at hk
      exact hk
    by_cases ht : (M *ᵥ v) i = 0
    · exact Or.inl ⟨v, hv, funext_succAbove (i₀ := i) ht hrest⟩
    · refine Or.inr ⟨((M *ᵥ v) i)⁻¹ • v, ?_⟩
      rw [Matrix.mulVec_smul]
      refine funext_succAbove (i₀ := i) ?_ fun k => ?_
      · simp only [Pi.smul_apply, smul_eq_mul, e7_same]
        exact inv_mul_cancel₀ ht
      · simp only [Pi.smul_apply, smul_eq_mul, hrest k, mul_zero, e7_ne (Fin.succAbove_ne i k)]
  by_contra hno
  have hs : ∀ i : Fin 7, ∃ v : Fin 6 → F, M *ᵥ v = e7 i :=
    fun i => (key i).resolve_left hno
  choose s hs using hs
  set W : Matrix (Fin 7) (Fin 7) F :=
    Matrix.of fun r i => Fin.cases (0 : F) (fun r' : Fin 6 => s i r') r with hW
  have hW0 : W.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 0 fun i => by simp [hW]
  obtain ⟨a, ha, hWa⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hW0
  have hcoord : ∀ r' : Fin 6, ∑ i, s i r' * a i = 0 := fun r' => by
    have hr := congrFun hWa r'.succ
    simpa [hW, Matrix.mulVec, dotProduct] using hr
  set u : Fin 6 → F := fun r' => ∑ i, a i * s i r' with hu
  have hu0 : u = 0 := by
    funext r'
    simp only [hu, Pi.zero_apply]
    rw [← hcoord r']
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hMu : M *ᵥ u = a := by
    funext k
    have hk : ∀ i, ∑ r', M k r' * (a i * s i r') = a i * e7 i k := fun i => by
      rw [← congrFun (hs i) k]
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r' _ => by ring
    simp only [Matrix.mulVec, dotProduct, hu, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [hk, e7, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  exact ha (by rw [← hMu, hu0, Matrix.mulVec_zero])

/-! ## One affine equation in six unknowns -/

/-- `∑ᵢ wᵢ pᵢ + t₀ = t` with `w ≠ 0`: pivot on a nonzero coordinate of `w`. -/
theorem exists_solve_affine (w : Fin 6 → F) (hw : w ≠ 0) (t₀ t : F) :
    ∃ p : Fin 6 → F, ∑ i, w i * p i + t₀ = t := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
  have hi' : w i ≠ 0 := hi
  refine ⟨Pi.single i ((t - t₀) / w i), ?_⟩
  simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_div_cancel₀ _ hi']
  ring

end FastPoly.LowerBound.General
