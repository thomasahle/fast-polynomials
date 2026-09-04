import FastPoly.Examples.BarredPivot
import FastPoly.Polynomial.LowJet
import FastPoly.Section5.SlotSurj
import Mathlib.Algebra.Ring.Divisibility.Lemmas
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The general barred odd-degree gadget

This file formalizes the construction denoted `\bar Q_{8k+7}(x,H₂,H₄)` in the paper.
The proof is organized around the actual decoder:

* three unit top pivots;
* one four-variable block with determinant `-k²`;
* the scalar pivots `k·w` and `k·ρ`;
* an affine-monic transport of the `Rk2l` triangular remainder decoder;
* six unit low pivots.

The small `k = 1` circuit has its optimized standalone proof in `BarQ15.lean`.  The
construction below is stated for arbitrary `k`; its general decoder will use `2 ≤ k`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

namespace CoeffTriangular

variable {K V : Subalgebra R A} {alpha lam : ℕ → A} {lamR : ℕ → R}
variable {d hd : ℕ} {R₁ R₂ L₁ L₂ : A[X]}

/-- The pivot part of `CoeffTriangular.shift_pivot` survives an affine factor
`(X + c)L₁` on the first remainder.  The additional term `c L₁R₁` contains only
parameters strictly later than the pivot being decoded. -/
theorem affine_monic_shift_pivot
    (h : CoeffTriangular K alpha lamR d R₁ R₂)
    (hd1 : 1 ≤ hd)
    (hL₁ : L₁.Monic) (hdL₁ : L₁.natDegree = hd)
    (hL₂ : L₂.Monic) (hdL₂ : L₂.natDegree = hd)
    (hKL₁ : ∀ j, L₁.coeff j ∈ K) (hKL₂ : ∀ j, L₂.coeff j ∈ K)
    {c : A} (hc : c ∈ K) :
    ∀ j, j < d → ∃ F ∈ K ⊔ adjoin R (alpha '' Set.Ico (j + 1) d),
      (((X + C c) * L₁) * R₁ + L₂ * R₂).coeff (hd + j)
        = algebraMap R A (lamR j) * alpha j + F := by
  intro j hj
  obtain ⟨F, hF, hFeq⟩ := h.shift_pivot hd1 hL₁ hdL₁ hL₂ hdL₂ hKL₁ hKL₂ j hj
  have hL₁le : L₁.natDegree ≤ hd := hdL₁.le
  have htail := h.shift_supp₁ hL₁le hKL₁ (hd + j)
  have htail' : (L₁ * R₁).coeff (hd + j)
      ∈ K ⊔ adjoin R (alpha '' Set.Ico (j + 1) d) := by
    simpa [show hd + j + 1 - hd = j + 1 by omega] using htail
  refine ⟨F + c * (L₁ * R₁).coeff (hd + j),
    Subalgebra.add_mem _ hF
      (Subalgebra.mul_mem _ ((le_sup_left : K ≤ _) hc) htail'), ?_⟩
  have hsplit : ((X + C c) * L₁) * R₁ + L₂ * R₂
      = combined (L₁ * R₁) (L₂ * R₂) + C c * (L₁ * R₁) := by
    simp only [combined]
    ring
  rw [hsplit, coeff_add, coeff_C_mul, hFeq]
  ring

/-- Explicit descending decoder for the affine-monic transport above.  This is the
general mechanism used by the barred gadget to recover the internal `T_{k,8}` block
from `A R⁽¹⁾ + B R⁽²⁾`, where `deg A = deg B + 1`.

No solver or elimination principle is hidden here: at row `hd+j` the named unit
`lamR j` is inverted after all strictly later parameters have been decoded. -/
theorem param_mem_of_affine_monic_shift
    (h : CoeffTriangular K alpha lamR d R₁ R₂)
    (hd1 : 1 ≤ hd)
    (hL₁ : L₁.Monic) (hdL₁ : L₁.natDegree = hd)
    (hL₂ : L₂.Monic) (hdL₂ : L₂.natDegree = hd)
    (hKL₁ : ∀ j, L₁.coeff j ∈ K) (hKL₂ : ∀ j, L₂.coeff j ∈ K)
    {c : A} (hc : c ∈ K) (hKV : K ≤ V)
    (hrows : ∀ j, j < d →
      (((X + C c) * L₁) * R₁ + L₂ * R₂).coeff (hd + j) ∈ V) :
    ∀ j, j < d → alpha j ∈ V := by
  have main : ∀ fuel j, j < d → d - j ≤ fuel → alpha j ∈ V := by
    intro fuel
    induction fuel with
    | zero =>
        intro j hj hf
        omega
    | succ fuel ih =>
        intro j hj hf
        obtain ⟨u, hu⟩ := h.unit j hj
        obtain ⟨F, hF, hrow⟩ :=
          affine_monic_shift_pivot h hd1 hL₁ hdL₁ hL₂ hdL₂ hKL₁ hKL₂ hc j hj
        have hFV : F ∈ V := by
          refine SetLike.le_def.1 (sup_le hKV (adjoin_le ?_)) hF
          rintro _ ⟨i, ⟨hi1, hi2⟩, rfl⟩
          exact ih i hi2 (by omega)
        have hkey : alpha j = algebraMap R A ↑u⁻¹ *
            ((((X + C c) * L₁) * R₁ + L₂ * R₂).coeff (hd + j) - F) := by
          rw [hrow, add_sub_cancel_right, ← mul_assoc, ← map_mul, ← hu,
            Units.inv_mul, map_one, one_mul]
        rw [hkey]
        exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
          (Subalgebra.sub_mem _ (hrows j hj) hFV)
  exact fun j hj => main (d - j) j hj le_rfl

end CoeffTriangular

namespace BarQGeneral


/-- Divide a visible scalar pivot by a declared natural-number unit. -/
private theorem mem_of_nat_slope {V : Subalgebra R A} {m : ℕ}
    (hm : IsUnit (m : R)) {x y : A} (hx : x ∈ V) (hxy : (m : A) * y = x) :
    y ∈ V := by
  obtain ⟨u, hu⟩ := hm
  have hMA : (m : A) = algebraMap R A (m : R) := by rw [map_natCast]
  have hleft : algebraMap R A (↑u⁻¹ : R) * (m : A) = 1 := by
    rw [hMA, ← hu, ← map_mul, Units.inv_mul, map_one]
  have hkey : y = algebraMap R A (↑u⁻¹ : R) * x := by
    rw [← hxy, ← mul_assoc, hleft, one_mul]
  rw [hkey]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hx

/-- The synthesized octic used by every barred gadget. -/
noncomputable def H8 (H₂ H₄ : A[X]) (u v w : A) : A[X] :=
  (H₄ + (X + C u)) * (H₄ + (H₂ + C v)) + C w

/-- The power tower supplied to `T_{k,8}`.  Values outside levels `1,2,3` are
irrelevant to that call and are set to zero. -/
noncomputable def tower (H₂ H₄ H₈ : A[X]) : ℕ → A[X]
  | 1 => H₂
  | 2 => H₄
  | 3 => H₈
  | _ => 0

@[simp] theorem tower_one (H₂ H₄ H₈ : A[X]) : tower H₂ H₄ H₈ 1 = H₂ := rfl
@[simp] theorem tower_two (H₂ H₄ H₈ : A[X]) : tower H₂ H₄ H₈ 2 = H₄ := rfl
@[simp] theorem tower_three (H₂ H₄ H₈ : A[X]) : tower H₂ H₄ H₈ 3 = H₈ := rfl

/-- The low monic cubic in the final `A₄` crown. -/
noncomputable def Q3 (H₂ : A[X]) (a₃ a₄ a₅ : A) : A[X] :=
  (X + C a₅) * (H₂ + C a₄) + C a₃

/-- First degree-`8k+4` wire of the outer crown. -/
noncomputable def U0 (H₂ H₄ S₁ : A[X]) (a₃ a₄ a₅ b₃ : A) : A[X] :=
  (H₄ + C b₃) * S₁ + Q3 H₂ a₃ a₄ a₅

/-- Second degree-`8k+4` wire of the outer crown. -/
noncomputable def V0 (H₄ S₂ : A[X]) (a₂ b₄ : A) : A[X] :=
  (H₄ + C b₄) * S₂ + C a₂

noncomputable def C1 (H₂ H₄ S₁ : A[X])
    (a₁ a₃ a₄ a₅ b₁ b₃ : A) : A[X] :=
  (H₂ + C b₁) * U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃ + C a₁

noncomputable def C2 (H₂ H₄ S₂ : A[X]) (a₀ a₂ b₂ b₄ : A) : A[X] :=
  (H₂ + C b₂) * V0 H₄ S₂ a₂ b₄ + C a₀

/-- The outer `A₄` crown, separated from the internal `T` call. -/
noncomputable def outer (H₂ H₄ S₁ S₂ : A[X])
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  (X + C b₀) * C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃
    + C2 H₂ H₄ S₂ a₀ a₂ b₂ b₄

/-- The complete general barred gadget, with its parameter blocks kept separate.
`beta` is the internal block of length `8(k-1)`. -/
noncomputable def barQ (H₂ H₄ : A[X]) (k : ℕ) (beta : ℕ → A)
    (w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  let H₈ := H8 H₂ H₄ u v w
  let S := Tpair (tower H₂ H₄ H₈) (H₈ + C rho) k 3 beta
  outer H₂ H₄ S.1 S.2 a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄

/-- The two monic multipliers of the internal remainders. -/
noncomputable def crownA (H₂ H₄ : A[X]) (b₀ b₁ b₃ : A) : A[X] :=
  (X + C b₀) * (H₂ + C b₁) * (H₄ + C b₃)

noncomputable def crownB (H₂ H₄ : A[X]) (b₂ b₄ : A) : A[X] :=
  (H₂ + C b₂) * (H₄ + C b₄)

/-- The degree-six residual left after the two high `T` terms are removed. -/
noncomputable def lowCore (H₂ : A[X])
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) : A[X] :=
  (X + C b₀) * ((H₂ + C b₁) * Q3 H₂ a₃ a₄ a₅ + C a₁)
    + (H₂ + C b₂) * C a₂ + C a₀

noncomputable def lowL3 (H₂ : A[X]) (b₀ b₁ : A) : A[X] :=
  (X + C b₀) * (H₂ + C b₁)

noncomputable def lowL5 (H₂ : A[X]) (b₀ b₁ : A) : A[X] :=
  lowL3 H₂ b₀ b₁ * H₂

noncomputable def lowL4 (H₂ : A[X]) (a₅ b₀ b₁ : A) : A[X] :=
  lowL3 H₂ b₀ b₁ * (X + C a₅)

noncomputable def lowL2 (H₂ : A[X]) (b₂ : A) : A[X] := H₂ + C b₂
noncomputable def lowL1 (b₀ : A) : A[X] := X + C b₀

noncomputable def lowStage5 (H₂ : A[X]) (b₀ b₁ : A) : A[X] :=
  lowL3 H₂ b₀ b₁ * (X * H₂)

noncomputable def lowStage4 (H₂ : A[X]) (a₅ b₀ b₁ : A) : A[X] :=
  lowStage5 H₂ b₀ b₁ + C a₅ * lowL5 H₂ b₀ b₁

noncomputable def lowStage3 (H₂ : A[X]) (a₄ a₅ b₀ b₁ : A) : A[X] :=
  lowStage4 H₂ a₅ b₀ b₁ + C a₄ * lowL4 H₂ a₅ b₀ b₁

noncomputable def lowStage2 (H₂ : A[X]) (a₃ a₄ a₅ b₀ b₁ : A) : A[X] :=
  lowStage3 H₂ a₄ a₅ b₀ b₁ + C a₃ * lowL3 H₂ b₀ b₁

noncomputable def lowStage1 (H₂ : A[X])
    (a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) : A[X] :=
  lowStage2 H₂ a₃ a₄ a₅ b₀ b₁ + C a₂ * lowL2 H₂ b₂

noncomputable def lowStage0 (H₂ : A[X])
    (a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) : A[X] :=
  lowStage1 H₂ a₂ a₃ a₄ a₅ b₀ b₁ b₂ + C a₁ * lowL1 b₀

/-- The low residual is already in unitriangular normal form. -/
theorem lowCore_expansion (H₂ : A[X])
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ =
      lowStage0 H₂ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ + C a₀ := by
  simp only [lowCore, lowStage0, lowStage1, lowStage2, lowStage3, lowStage4,
    lowStage5, lowL1, lowL2, lowL3, lowL4, lowL5, Q3]
  ring

/-- Exact high/low decomposition of the outer crown. -/
theorem outer_eq_crowns_add_low (H₂ H₄ S₁ S₂ : A[X])
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    outer H₂ H₄ S₁ S₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ =
      crownA H₂ H₄ b₀ b₁ b₃ * S₁ + crownB H₂ H₄ b₂ b₄ * S₂
        + lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ := by
  simp only [outer, C1, C2, U0, V0, crownA, crownB, lowCore]
  ring

section structural

variable [Nontrivial A]

private theorem add_C_good {P : A[X]} {d : ℕ} (hPm : P.Monic)
    (hPd : P.natDegree = d) (z : A) (hd : 0 < d) :
    (P + C z).Monic ∧ (P + C z).natDegree = d := by
  obtain ⟨hm, hn⟩ := monic_add_low (P := P) (e := C z) hPm
    (Or.inr (by rw [natDegree_C, hPd]; omega))
  exact ⟨hm, hn.trans hPd⟩

/-- The synthesized `H₈` is a genuine monic octic. -/
theorem H8_good {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (u v w : A) :
    (H8 H₂ H₄ u v w).Monic ∧ (H8 H₂ H₄ u v w).natDegree = 8 := by
  obtain ⟨hLm, hLd⟩ := monic_add_low (P := H₄) (e := X + C u) hH₄m
    (Or.inr (by rw [natDegree_X_add_C, hH₄d]; omega))
  obtain ⟨hH₂vm, hH₂vd⟩ := add_C_good hH₂m hH₂d v (by omega)
  obtain ⟨hRm, hRd⟩ := monic_add_low (P := H₄) (e := H₂ + C v) hH₄m
    (Or.inr (by rw [hH₂vd, hH₄d]; omega))
  have hPm : ((H₄ + (X + C u)) * (H₄ + (H₂ + C v))).Monic := hLm.mul hRm
  have hPd : ((H₄ + (X + C u)) * (H₄ + (H₂ + C v))).natDegree = 8 := by
    rw [hLm.natDegree_mul hRm, hLd, hRd, hH₄d]
  rw [H8]
  exact add_C_good hPm hPd w (by omega)

/-- The internal-remainder multipliers have degrees seven and six, with the
first equal to `(X+b₀)` times a monic degree-six factor. -/
theorem crown_good {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (b₀ b₁ b₂ b₃ b₄ : A) :
    (crownA H₂ H₄ b₀ b₁ b₃).Monic ∧
      (crownA H₂ H₄ b₀ b₁ b₃).natDegree = 7 ∧
      (crownB H₂ H₄ b₂ b₄).Monic ∧
      (crownB H₂ H₄ b₂ b₄).natDegree = 6 := by
  obtain ⟨hH₂b₁m, hH₂b₁d⟩ := add_C_good hH₂m hH₂d b₁ (by omega)
  obtain ⟨hH₂b₂m, hH₂b₂d⟩ := add_C_good hH₂m hH₂d b₂ (by omega)
  obtain ⟨hH₄b₃m, hH₄b₃d⟩ := add_C_good hH₄m hH₄d b₃ (by omega)
  obtain ⟨hH₄b₄m, hH₄b₄d⟩ := add_C_good hH₄m hH₄d b₄ (by omega)
  have hXm : (X + C b₀ : A[X]).Monic := monic_X_add_C _
  have hXd : (X + C b₀ : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hAm : (crownA H₂ H₄ b₀ b₁ b₃).Monic := by
    rw [crownA]
    exact (hXm.mul hH₂b₁m).mul hH₄b₃m
  have hAd : (crownA H₂ H₄ b₀ b₁ b₃).natDegree = 7 := by
    rw [crownA, (hXm.mul hH₂b₁m).natDegree_mul hH₄b₃m,
      hXm.natDegree_mul hH₂b₁m, hXd, hH₂b₁d, hH₄b₃d]
  have hBm : (crownB H₂ H₄ b₂ b₄).Monic := by
    rw [crownB]
    exact hH₂b₂m.mul hH₄b₄m
  have hBd : (crownB H₂ H₄ b₂ b₄).natDegree = 6 := by
    rw [crownB, hH₂b₂m.natDegree_mul hH₄b₄m,
      hH₂b₂d, hH₄b₄d]
  exact ⟨hAm, hAd, hBm, hBd⟩

/-- Monicity and degrees of the six low-pivot multipliers. -/
theorem low_factors_good {H₂ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (a₅ b₀ b₁ b₂ : A) :
    (lowL5 H₂ b₀ b₁).Monic ∧ (lowL5 H₂ b₀ b₁).natDegree = 5 ∧
    (lowL4 H₂ a₅ b₀ b₁).Monic ∧ (lowL4 H₂ a₅ b₀ b₁).natDegree = 4 ∧
    (lowL3 H₂ b₀ b₁).Monic ∧ (lowL3 H₂ b₀ b₁).natDegree = 3 ∧
    (lowL2 H₂ b₂).Monic ∧ (lowL2 H₂ b₂).natDegree = 2 ∧
    (lowL1 b₀ : A[X]).Monic ∧ (lowL1 b₀ : A[X]).natDegree = 1 := by
  obtain ⟨hH₂b₁m, hH₂b₁d⟩ := add_C_good hH₂m hH₂d b₁ (by omega)
  obtain ⟨hH₂b₂m, hH₂b₂d⟩ := add_C_good hH₂m hH₂d b₂ (by omega)
  have hXb₀m : (X + C b₀ : A[X]).Monic := monic_X_add_C _
  have hXb₀d : (X + C b₀ : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hXa₅m : (X + C a₅ : A[X]).Monic := monic_X_add_C _
  have hXa₅d : (X + C a₅ : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hL₃m : (lowL3 H₂ b₀ b₁).Monic := by
    rw [lowL3]
    exact hXb₀m.mul hH₂b₁m
  have hL₃d : (lowL3 H₂ b₀ b₁).natDegree = 3 := by
    rw [lowL3, hXb₀m.natDegree_mul hH₂b₁m, hXb₀d, hH₂b₁d]
  have hL₅m : (lowL5 H₂ b₀ b₁).Monic := by
    rw [lowL5]
    exact hL₃m.mul hH₂m
  have hL₅d : (lowL5 H₂ b₀ b₁).natDegree = 5 := by
    rw [lowL5, hL₃m.natDegree_mul hH₂m, hL₃d, hH₂d]
  have hL₄m : (lowL4 H₂ a₅ b₀ b₁).Monic := by
    rw [lowL4]
    exact hL₃m.mul hXa₅m
  have hL₄d : (lowL4 H₂ a₅ b₀ b₁).natDegree = 4 := by
    rw [lowL4, hL₃m.natDegree_mul hXa₅m, hL₃d, hXa₅d]
  exact ⟨hL₅m, hL₅d, hL₄m, hL₄d, hL₃m, hL₃d,
    hH₂b₂m, hH₂b₂d, hXb₀m, hXb₀d⟩

/-- The low residual is monic of degree six, independently of its six
parameters.  Hence its row six is the known constant `1`, and every higher
row vanishes. -/
theorem lowCore_good {H₂ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).Monic ∧
      (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).natDegree = 6 := by
  obtain ⟨hH₂a₄m, hH₂a₄d⟩ := add_C_good hH₂m hH₂d a₄ (by omega)
  have hXa₅m : (X + C a₅ : A[X]).Monic := monic_X_add_C _
  have hXa₅d : (X + C a₅ : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hQprodM : ((X + C a₅) * (H₂ + C a₄)).Monic := hXa₅m.mul hH₂a₄m
  have hQprodD : ((X + C a₅) * (H₂ + C a₄)).natDegree = 3 := by
    rw [hXa₅m.natDegree_mul hH₂a₄m, hXa₅d, hH₂a₄d]
  have hQm : (Q3 H₂ a₃ a₄ a₅).Monic := by
    rw [Q3]
    exact (add_C_good hQprodM hQprodD a₃ (by omega)).1
  have hQd : (Q3 H₂ a₃ a₄ a₅).natDegree = 3 := by
    rw [Q3]
    exact (add_C_good hQprodM hQprodD a₃ (by omega)).2
  obtain ⟨hH₂b₁m, hH₂b₁d⟩ := add_C_good hH₂m hH₂d b₁ (by omega)
  have hinnerM : ((H₂ + C b₁) * Q3 H₂ a₃ a₄ a₅).Monic :=
    hH₂b₁m.mul hQm
  have hinnerD : ((H₂ + C b₁) * Q3 H₂ a₃ a₄ a₅).natDegree = 5 := by
    rw [hH₂b₁m.natDegree_mul hQm, hH₂b₁d, hQd]
  obtain ⟨hinner'M, hinner'D⟩ := add_C_good hinnerM hinnerD a₁ (by omega)
  have hXb₀m : (X + C b₀ : A[X]).Monic := monic_X_add_C _
  have hXb₀d : (X + C b₀ : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hmainM : ((X + C b₀) *
      ((H₂ + C b₁) * Q3 H₂ a₃ a₄ a₅ + C a₁)).Monic :=
    hXb₀m.mul hinner'M
  have hmainD : ((X + C b₀) *
      ((H₂ + C b₁) * Q3 H₂ a₃ a₄ a₅ + C a₁)).natDegree = 6 := by
    rw [hXb₀m.natDegree_mul hinner'M, hXb₀d, hinner'D]
  have hrestD : ((H₂ + C b₂) * C a₂ + C a₀).natDegree < 6 := by
    have h₁ := natDegree_add_le ((H₂ + C b₂) * C a₂) (C a₀)
    have h₂ : ((H₂ + C b₂) * C a₂).natDegree ≤
        (H₂ + C b₂).natDegree + (C a₂).natDegree := natDegree_mul_le
    have h₃ := natDegree_add_le H₂ (C b₂)
    simp only [natDegree_C, hH₂d] at h₁ h₂ h₃
    omega
  have hform :
      lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ =
        (X + C b₀) * ((H₂ + C b₁) * Q3 H₂ a₃ a₄ a₅ + C a₁)
          + ((H₂ + C b₂) * C a₂ + C a₀) := by
    rw [lowCore]
    ring
  rw [hform]
  obtain ⟨hm, hd⟩ := monic_add_low
    (e := (H₂ + C b₂) * C a₂ + C a₀) hmainM (Or.inr (by
      rw [hmainD]
      exact hrestD))
  exact ⟨hm, hd.trans hmainD⟩

omit [Nontrivial A] in
/-- The three relevant entries of `tower` have the required power degrees. -/
theorem tower_good {H₂ H₄ H₈ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (hH₈m : H₈.Monic) (hH₈d : H₈.natDegree = 8) :
    ∀ i, 1 ≤ i → i ≤ 3 →
      (tower H₂ H₄ H₈ i).Monic ∧ (tower H₂ H₄ H₈ i).natDegree = 2 ^ i := by
  intro i hi1 hi3
  have hi : i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hi with rfl | rfl | rfl <;> simp_all

/-- Structural endpoint for the internal `T_{k,8}` pair. -/
theorem T_good {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → A) (u v w rho : A) :
    let H₈ := H8 H₂ H₄ u v w
    let S := Tpair (tower H₂ H₄ H₈) (H₈ + C rho) k 3 beta
    (S.1.Monic ∧ S.1.natDegree = 8 * k) ∧
      (S.2.Monic ∧ S.2.natDegree = 8 * k) := by
  dsimp only
  obtain ⟨hH₈m, hH₈d⟩ := H8_good hH₂m hH₂d hH₄m hH₄d u v w
  obtain ⟨hHtm, hHtd⟩ := add_C_good hH₈m hH₈d rho (by omega)
  have h := Tpair_good (Hp := tower H₂ H₄ (H8 H₂ H₄ u v w))
    (Ht := H8 H₂ H₄ u v w + C rho) (k := k) (l := 3) (α := beta) hk (by omega)
    (fun _ _ => by omega)
    (tower_good hH₂m hH₂d hH₄m hH₄d hH₈m hH₈d) hHtm hHtd
  simpa [Nat.mul_comm] using h

private theorem outer_good {H₂ H₄ S₁ S₂ : A[X]} {N : ℕ}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (hS₁m : S₁.Monic) (hS₁d : S₁.natDegree = N)
    (hS₂m : S₂.Monic) (hS₂d : S₂.natDegree = N) (hN : 8 ≤ N)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    (outer H₂ H₄ S₁ S₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄).Monic ∧
      (outer H₂ H₄ S₁ S₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄).natDegree
        = N + 7 := by
  obtain ⟨hH₂a₄m, hH₂a₄d⟩ := add_C_good hH₂m hH₂d a₄ (by omega)
  have hXa₅m : (X + C a₅ : A[X]).Monic := monic_X_add_C _
  have hXa₅d : (X + C a₅ : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hQprodM : ((X + C a₅) * (H₂ + C a₄)).Monic := hXa₅m.mul hH₂a₄m
  have hQprodD : ((X + C a₅) * (H₂ + C a₄)).natDegree = 3 := by
    rw [hXa₅m.natDegree_mul hH₂a₄m, hXa₅d, hH₂a₄d]
  have hQgood : (Q3 H₂ a₃ a₄ a₅).Monic ∧ (Q3 H₂ a₃ a₄ a₅).natDegree = 3 := by
    rw [Q3]
    exact add_C_good hQprodM hQprodD a₃ (by omega)
  obtain ⟨hH₄b₃m, hH₄b₃d⟩ := add_C_good hH₄m hH₄d b₃ (by omega)
  have hUprodM : ((H₄ + C b₃) * S₁).Monic := hH₄b₃m.mul hS₁m
  have hUprodD : ((H₄ + C b₃) * S₁).natDegree = N + 4 := by
    rw [hH₄b₃m.natDegree_mul hS₁m, hH₄b₃d, hS₁d]
    omega
  have hUgood : (U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃).Monic ∧
      (U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃).natDegree = N + 4 := by
    rw [U0]
    obtain ⟨hm, hd⟩ := monic_add_low hUprodM (Or.inr (by rw [hQgood.2, hUprodD]; omega))
    exact ⟨hm, hd.trans hUprodD⟩
  obtain ⟨hH₄b₄m, hH₄b₄d⟩ := add_C_good hH₄m hH₄d b₄ (by omega)
  have hVprodM : ((H₄ + C b₄) * S₂).Monic := hH₄b₄m.mul hS₂m
  have hVprodD : ((H₄ + C b₄) * S₂).natDegree = N + 4 := by
    rw [hH₄b₄m.natDegree_mul hS₂m, hH₄b₄d, hS₂d]
    omega
  have hVgood : (V0 H₄ S₂ a₂ b₄).Monic ∧ (V0 H₄ S₂ a₂ b₄).natDegree = N + 4 := by
    rw [V0]
    exact add_C_good hVprodM hVprodD a₂ (by omega)
  obtain ⟨hH₂b₁m, hH₂b₁d⟩ := add_C_good hH₂m hH₂d b₁ (by omega)
  have hC1prodM : ((H₂ + C b₁) * U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃).Monic :=
    hH₂b₁m.mul hUgood.1
  have hC1prodD : ((H₂ + C b₁) * U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃).natDegree
      = N + 6 := by
    rw [hH₂b₁m.natDegree_mul hUgood.1, hH₂b₁d, hUgood.2]
    omega
  have hC1good : (C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃).Monic ∧
      (C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃).natDegree = N + 6 := by
    rw [C1]
    exact add_C_good hC1prodM hC1prodD a₁ (by omega)
  obtain ⟨hH₂b₂m, hH₂b₂d⟩ := add_C_good hH₂m hH₂d b₂ (by omega)
  have hC2prodM : ((H₂ + C b₂) * V0 H₄ S₂ a₂ b₄).Monic := hH₂b₂m.mul hVgood.1
  have hC2prodD : ((H₂ + C b₂) * V0 H₄ S₂ a₂ b₄).natDegree = N + 6 := by
    rw [hH₂b₂m.natDegree_mul hVgood.1, hH₂b₂d, hVgood.2]
    omega
  have hC2good : (C2 H₂ H₄ S₂ a₀ a₂ b₂ b₄).Monic ∧
      (C2 H₂ H₄ S₂ a₀ a₂ b₂ b₄).natDegree = N + 6 := by
    rw [C2]
    exact add_C_good hC2prodM hC2prodD a₀ (by omega)
  have hXb₀m : (X + C b₀ : A[X]).Monic := monic_X_add_C _
  have hXb₀d : (X + C b₀ : A[X]).natDegree = 1 := natDegree_X_add_C _
  have hTopM : ((X + C b₀) * C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃).Monic :=
    hXb₀m.mul hC1good.1
  have hTopD : ((X + C b₀) * C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃).natDegree
      = N + 7 := by
    rw [hXb₀m.natDegree_mul hC1good.1, hXb₀d, hC1good.2]
    omega
  rw [outer]
  obtain ⟨hm, hd'⟩ := monic_add_low hTopM (Or.inr (by rw [hC2good.2, hTopD]; omega))
  exact ⟨hm, hd'.trans hTopD⟩

/-- The complete barred circuit is monic of degree `8k+7`. -/
theorem barQ_good {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → A)
    (w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄).Monic ∧
      (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄).natDegree
        = 8 * k + 7 := by
  have hT := T_good hH₂m hH₂d hH₄m hH₄d k hk beta u v w rho
  have hout := outer_good hH₂m hH₂d hH₄m hH₄d
    hT.1.1 hT.1.2 hT.2.1 hT.2.2 (by omega)
    a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  simpa only [barQ] using hout

end structural

/-! ## Coefficient jets at infinity

For a degree-`D` polynomial, coefficient `i` of `reflect D` is its coefficient in
degree `D-i`.  Congruence modulo `X^m` therefore means equality of the first `m`
rows seen by the top-down decoder. -/


/-- If `E` begins in row `e`, every term of binomial order at least two begins in
row `2e`. -/
theorem X_pow_dvd_binTail {B E : A[X]} {e : ℕ} (hE : X ^ e ∣ E) (n : ℕ) :
    X ^ (2 * e) ∣ binTail B E n := by
  rw [binTail]
  refine Finset.dvd_sum ?_
  intro q hq
  obtain ⟨hq2, -⟩ := Finset.mem_Icc.1 hq
  have hEq : X ^ (2 * e) ∣ E ^ q := by
    have hpow : (X ^ e) ^ q ∣ E ^ q := pow_dvd_pow_of_dvd hE q
    have hle : 2 * e ≤ e * q := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left e hq2
    exact dvd_trans (by simpa [pow_mul] using pow_dvd_pow X hle) hpow
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hEq _) _

/-- First-order binomial expansion in an `X`-adic jet.  This is the formal-series
calculus used in the manuscript, stated purely as polynomial divisibility. -/
theorem pow_linear_mod {B E : A[X]} {e n : ℕ} (hE : X ^ e ∣ E)
    (hn : 1 ≤ n) :
    JetEq (2 * e) ((B + E) ^ n) (B ^ n + n • (E * B ^ (n - 1))) := by
  rw [JetEq]
  have hsplit := pow_add_eq B E hn
  rw [hsplit]
  have hkey : B ^ n + n • (E * B ^ (n - 1)) + binTail B E n
      - (B ^ n + n • (E * B ^ (n - 1))) = binTail B E n := by ring
  rw [hkey]
  exact X_pow_dvd_binTail hE n

/-- Product rule to first order in the `X`-adic filtration. -/
theorem mul_linear_mod {P Q E F : A[X]} {e : ℕ}
    (hE : X ^ e ∣ E) (hF : X ^ e ∣ F) :
    JetEq (2 * e) ((P + E) * (Q + F)) (P * Q + E * Q + P * F) := by
  rw [JetEq]
  have hEF : X ^ (2 * e) ∣ E * F := by
    obtain ⟨E', rfl⟩ := hE
    obtain ⟨F', rfl⟩ := hF
    refine ⟨E' * F', ?_⟩
    rw [show X ^ (2 * e) = X ^ e * X ^ e by
      rw [show 2 * e = e + e by ring, pow_add]]
    ring
  convert hEF using 1
  ring

/-- Padding a reflection by zero rows shifts its jet by the padding length. -/
theorem reflect_pad (P : A[X]) {d N : ℕ} (hP : P.natDegree ≤ d) (hdN : d ≤ N) :
    P.reflect N = P.reflect d * X ^ (N - d) := by
  calc
    P.reflect N = (P * 1).reflect (d + (N - d)) := by
      rw [mul_one, Nat.add_sub_of_le hdN]
    _ = P.reflect d * (1 : A[X]).reflect (N - d) :=
      reflect_mul P 1 hP (by rw [natDegree_one]; omega)
    _ = P.reflect d * X ^ (N - d) := by rw [reflect_one]

/-- The normalized quadratic and quartic jets. -/
noncomputable def jH2 (H₂ : A[X]) : A[X] := H₂.reflect 2
noncomputable def jH4 (H₄ : A[X]) : A[X] := H₄.reflect 4

noncomputable def jF1 (H₄ : A[X]) : A[X] := jH4 H₄ + X ^ 3
noncomputable def jF2 (H₂ H₄ : A[X]) : A[X] := jH4 H₄ + X ^ 2 * jH2 H₂
noncomputable def jH8Base (H₂ H₄ : A[X]) : A[X] := jF1 H₄ * jF2 H₂ H₄

/-- The exact normalized octic jet.  The three fresh parameters first occur in
rows `4,4,8`, respectively. -/
noncomputable def jH8 (H₂ H₄ : A[X]) (u v w : A) : A[X] :=
  (jF1 H₄ + C u * X ^ 4) * (jF2 H₂ H₄ + C v * X ^ 4) + C w * X ^ 8

/-- The first-order `u,v` perturbation of the base octic jet. -/
noncomputable def jH8Error (H₂ H₄ : A[X]) (u v : A) : A[X] :=
  C u * X ^ 4 * jF2 H₂ H₄ + C v * X ^ 4 * jF1 H₄

/-- The first-order power model used by the top eight rows. -/
noncomputable def jH8LinearPower (H₂ H₄ : A[X]) (k : ℕ) (u v : A) : A[X] :=
  jH8Base H₂ H₄ ^ k
    + k • (jH8Error H₂ H₄ u v * jH8Base H₂ H₄ ^ (k - 1))

/-- Modulo row eight, `w` and the bilinear term `uv` vanish, leaving an affine
perturbation in `u,v`. -/
theorem jH8_linear_mod_eight (H₂ H₄ : A[X]) (u v w : A) :
    JetEq 8 (jH8 H₂ H₄ u v w) (jH8Base H₂ H₄ + jH8Error H₂ H₄ u v) := by
  rw [JetEq]
  refine ⟨C (u * v + w), ?_⟩
  simp only [jH8, jH8Base, jH8Error]
  rw [map_add, map_mul]
  ring

theorem jH8Error_dvd_four (H₂ H₄ : A[X]) (u v : A) :
    X ^ 4 ∣ jH8Error H₂ H₄ u v := by
  refine ⟨C u * jF2 H₂ H₄ + C v * jF1 H₄, ?_⟩
  rw [jH8Error]
  ring

/-- The `k`-th power is affine in `u,v` through the top eight rows. -/
theorem jH8_pow_linear_mod_eight (H₂ H₄ : A[X]) (k : ℕ) (hk : 1 ≤ k)
    (u v w : A) :
    JetEq 8 (jH8 H₂ H₄ u v w ^ k) (jH8LinearPower H₂ H₄ k u v) := by
  have h₁ := (jH8_linear_mod_eight H₂ H₄ u v w).pow k
  have h₂ := pow_linear_mod (B := jH8Base H₂ H₄)
    (jH8Error_dvd_four H₂ H₄ u v) hk
  exact h₁.trans (by simpa [jH8LinearPower] using h₂)

/-- A scalar shift in row eight is invisible to the top-eight power jet. -/
theorem jH8_shift_pow_linear_mod_eight (H₂ H₄ : A[X]) (k : ℕ) (hk : 1 ≤ k)
    (u v w rho : A) :
    JetEq 8 ((jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k)
      (jH8LinearPower H₂ H₄ k u v) := by
  have hshift : JetEq 8 (jH8 H₂ H₄ u v w + C rho * X ^ 8)
      (jH8 H₂ H₄ u v w) := by
    rw [JetEq]
    refine ⟨C rho, ?_⟩
    ring
  exact (hshift.pow k).trans (jH8_pow_linear_mod_eight H₂ H₄ k hk u v w)

private theorem reflect_X_four : (X : A[X]).reflect 4 = X ^ 3 := by
  calc
    (X : A[X]).reflect 4 = (X ^ 1 : A[X]).reflect 4 := by rw [pow_one]
    _ = X ^ revAt 4 1 := reflect_monomial 4 1
    _ = X ^ 3 := by norm_num [revAt]

/-- Reflection of the synthesized octic is exactly the small jet `jH8`. -/
theorem H8_reflect {H₂ H₄ : A[X]} (hH₂d : H₂.natDegree = 2)
    (hH₄d : H₄.natDegree = 4) (u v w : A) :
    (H8 H₂ H₄ u v w).reflect 8 = jH8 H₂ H₄ u v w := by
  have hL : (H₄ + (X + C u)).natDegree ≤ 4 := by
    refine le_trans (natDegree_add_le _ _) (max_le hH₄d.le ?_)
    refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
    · exact le_trans (natDegree_X_le (R := A)) (by omega)
    · rw [natDegree_C]
      omega
  have hHv : (H₂ + C v).natDegree ≤ 2 := by
    refine le_trans (natDegree_add_le _ _) (max_le hH₂d.le ?_)
    rw [natDegree_C]
    omega
  have hR : (H₄ + (H₂ + C v)).natDegree ≤ 4 := by
    refine le_trans (natDegree_add_le _ _) (max_le hH₄d.le (le_trans hHv (by omega)))
  have hH₂4 : H₂.reflect 4 = X ^ 2 * jH2 H₂ := by
    rw [reflect_pad H₂ hH₂d.le (by omega), jH2]
    ring
  rw [H8, reflect_add, reflect_mul _ _ hL hR]
  simp only [reflect_add, jH2, jH4, reflect_C, reflect_X_four, hH₂4,
    jH8, jF1, jF2]
  ring

/-- Reflection commutes with a power when the advertised padding degree is used. -/
theorem reflect_pow_of_degree_le (P : A[X]) {D : ℕ} (hP : P.natDegree ≤ D) :
    ∀ n, (P ^ n).reflect (n * D) = (P.reflect D) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hPn : (P ^ n).natDegree ≤ n * D :=
        le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hP)
      rw [pow_succ, show (n + 1) * D = n * D + D by ring,
        reflect_mul _ _ hPn hP, ih, pow_succ]

/-- Exact reflected form of the internal `T_{k,8}` output.  Its remainder begins
precisely eight rows below the leading term. -/
theorem T_reflect_split [Nontrivial A] {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → A) (u v w rho : A) :
    let H₈ := H8 H₂ H₄ u v w
    let Ht := H₈ + C rho
    let Hp := tower H₂ H₄ H₈
    let S := Tpair Hp Ht k 3 beta
    let RR := Rpair Hp Ht k 3 beta
    S.1.reflect (k * 8) = (jH8 H₂ H₄ u v w) ^ k
        + RR.1.reflect ((k - 1) * 8) * X ^ 8 ∧
      S.2.reflect (k * 8) = (jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k
        + RR.2.reflect ((k - 1) * 8) * X ^ 8 := by
  dsimp only
  obtain ⟨hH₈m, hH₈d⟩ := H8_good hH₂m hH₂d hH₄m hH₄d u v w
  obtain ⟨hHtm, hHtd⟩ := add_C_good hH₈m hH₈d rho (by omega)
  have hTower := tower_good hH₂m hH₂d hH₄m hH₄d hH₈m hH₈d
  obtain ⟨hR₁d, hR₂d⟩ := Rk2l_deg k hk 3
    (tower H₂ H₄ (H8 H₂ H₄ u v w)) (H8 H₂ H₄ u v w + C rho) beta
    (by omega) hTower
    hHtm hHtd (fun h3 => by omega)
  norm_num at hR₁d hR₂d
  obtain ⟨hS₁, hS₂⟩ := Tpair_eq_pow_add_R
    (Hp := tower H₂ H₄ (H8 H₂ H₄ u v w))
    (Ht := H8 H₂ H₄ u v w + C rho) (k := k) (l := 3) (α := beta)
  have hpow₁ : ((H8 H₂ H₄ u v w) ^ k).reflect (k * 8)
      = (jH8 H₂ H₄ u v w) ^ k := by
    rw [reflect_pow_of_degree_le _ hH₈d.le k, H8_reflect hH₂d hH₄d]
  have hHtr : (H8 H₂ H₄ u v w + C rho).reflect 8
      = jH8 H₂ H₄ u v w + C rho * X ^ 8 := by
    rw [reflect_add, H8_reflect hH₂d hH₄d]
    simp only [reflect_C]
  have hpow₂ : ((H8 H₂ H₄ u v w + C rho) ^ k).reflect (k * 8)
      = (jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k := by
    rw [reflect_pow_of_degree_le _ hHtd.le k, hHtr]
  have hgap : k * 8 - (k - 1) * 8 = 8 := by omega
  constructor
  · rw [hS₁, tower_three, reflect_add, hpow₁,
      reflect_pad _ hR₁d (by omega), hgap]
  · rw [hS₂, reflect_add, hpow₂,
      reflect_pad _ hR₂d (by omega), hgap]

/-- Through row seven, the internal remainders are invisible. -/
theorem T_reflect_top_eight [Nontrivial A] {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → A) (u v w rho : A) :
    let H₈ := H8 H₂ H₄ u v w
    let S := Tpair (tower H₂ H₄ H₈) (H₈ + C rho) k 3 beta
    JetEq 8 (S.1.reflect (k * 8)) ((jH8 H₂ H₄ u v w) ^ k) ∧
      JetEq 8 (S.2.reflect (k * 8))
        ((jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k) := by
  dsimp only
  obtain ⟨h₁, h₂⟩ := T_reflect_split hH₂m hH₂d hH₄m hH₄d
    k hk beta u v w rho
  constructor
  · rw [h₁, JetEq]
    refine ⟨(Rpair (tower H₂ H₄ (H8 H₂ H₄ u v w))
      (H8 H₂ H₄ u v w + C rho) k 3 beta).1.reflect ((k - 1) * 8), ?_⟩
    ring
  · rw [h₂, JetEq]
    refine ⟨(Rpair (tower H₂ H₄ (H8 H₂ H₄ u v w))
      (H8 H₂ H₄ u v w + C rho) k 3 beta).2.reflect ((k - 1) * 8), ?_⟩
    ring

/-! The exact outer circuit at infinity. -/

noncomputable def jQ3 (H₂ : A[X]) (a₃ a₄ a₅ : A) : A[X] :=
  (1 + C a₅ * X) * (jH2 H₂ + C a₄ * X ^ 2) + C a₃ * X ^ 3

noncomputable def jU0 (N : ℕ) (H₂ H₄ jS₁ : A[X])
    (a₃ a₄ a₅ b₃ : A) : A[X] :=
  (jH4 H₄ + C b₃ * X ^ 4) * jS₁ + X ^ (N + 1) * jQ3 H₂ a₃ a₄ a₅

noncomputable def jV0 (N : ℕ) (H₄ jS₂ : A[X]) (a₂ b₄ : A) : A[X] :=
  (jH4 H₄ + C b₄ * X ^ 4) * jS₂ + C a₂ * X ^ (N + 4)

noncomputable def jC1 (N : ℕ) (H₂ H₄ jS₁ : A[X])
    (a₁ a₃ a₄ a₅ b₁ b₃ : A) : A[X] :=
  (jH2 H₂ + C b₁ * X ^ 2) * jU0 N H₂ H₄ jS₁ a₃ a₄ a₅ b₃
    + C a₁ * X ^ (N + 6)

noncomputable def jC2 (N : ℕ) (H₂ H₄ jS₂ : A[X])
    (a₀ a₂ b₂ b₄ : A) : A[X] :=
  (jH2 H₂ + C b₂ * X ^ 2) * jV0 N H₄ jS₂ a₂ b₄
    + C a₀ * X ^ (N + 6)

noncomputable def jOuter (N : ℕ) (H₂ H₄ jS₁ jS₂ : A[X])
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  (1 + C b₀ * X) * jC1 N H₂ H₄ jS₁ a₁ a₃ a₄ a₅ b₁ b₃
    + X * jC2 N H₂ H₄ jS₂ a₀ a₂ b₂ b₄

/-- The two normalized outer factors that remain in the top eight rows. -/
noncomputable def jP1 (H₂ : A[X]) (b₀ b₁ : A) : A[X] :=
  (1 + C b₀ * X) * (jH2 H₂ + C b₁ * X ^ 2)

noncomputable def jP2 (H₂ : A[X]) (b₂ : A) : A[X] :=
  X * (jH2 H₂ + C b₂ * X ^ 2)

/-- The affine top-eight model after the `T` remainders, `w`, `rho`, and all six
low `a`-parameters have disappeared. -/
noncomputable def jTopLinear (H₂ H₄ : A[X]) (k : ℕ) (u v : A)
    (b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  jP1 H₂ b₀ b₁ * (jH4 H₄ + C b₃ * X ^ 4) * jH8LinearPower H₂ H₄ k u v
    + jP2 H₂ b₂ * (jH4 H₄ + C b₄ * X ^ 4) * jH8LinearPower H₂ H₄ k u v

noncomputable def jOuterFactor (H₂ : A[X]) (b₀ b₁ b₂ : A) : A[X] :=
  jP1 H₂ b₀ b₁ + jP2 H₂ b₂

noncomputable def jTopBase (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  jOuterFactor H₂ b₀ b₁ b₂ * jH4 H₄ * (jH8Base H₂ H₄ ^ k)

noncomputable def jScalarBase (H₂ H₄ : A[X]) (k : ℕ) : A[X] :=
  (jH2 H₂ + X * jH2 H₂) * jH4 H₄ * (jH8Base H₂ H₄ ^ k)

noncomputable def jB0Col (H₂ H₄ : A[X]) (k : ℕ) : A[X] :=
  X ^ 1 * (jH2 H₂ * jH4 H₄ * (jH8Base H₂ H₄ ^ k))

noncomputable def jB1Col (H₂ H₄ : A[X]) (k : ℕ) (b₀ : A) : A[X] :=
  X ^ 2 * ((1 + C b₀ * X) * jH4 H₄ * (jH8Base H₂ H₄ ^ k))

noncomputable def jB2Col (H₂ H₄ : A[X]) (k : ℕ) : A[X] :=
  X ^ 3 * (jH4 H₄ * (jH8Base H₂ H₄ ^ k))

noncomputable def jScalarStage1 (H₂ H₄ : A[X]) (k : ℕ) (b₀ : A) : A[X] :=
  jScalarBase H₂ H₄ k + C b₀ * jB0Col H₂ H₄ k

noncomputable def jScalarStage2 (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ : A) : A[X] :=
  jScalarStage1 H₂ H₄ k b₀ + C b₁ * jB1Col H₂ H₄ k b₀

noncomputable def jScalarLinear (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  jScalarStage2 H₂ H₄ k b₀ b₁ + C b₂ * jB2Col H₂ H₄ k

noncomputable def jB3Col (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ : A) : A[X] :=
  X ^ 4 * (jP1 H₂ b₀ b₁ * (jH8Base H₂ H₄ ^ k))

noncomputable def jB4Col (H₂ H₄ : A[X]) (k : ℕ) (b₂ : A) : A[X] :=
  X ^ 4 * (jP2 H₂ b₂ * (jH8Base H₂ H₄ ^ k))

noncomputable def jURawCol (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  X ^ 4 * (jOuterFactor H₂ b₀ b₁ b₂ * jH4 H₄ *
    (jF2 H₂ H₄ * jH8Base H₂ H₄ ^ (k - 1)))

noncomputable def jVRawCol (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  X ^ 4 * (jOuterFactor H₂ b₀ b₁ b₂ * jH4 H₄ *
    (jF1 H₄ * jH8Base H₂ H₄ ^ (k - 1)))

noncomputable def jUCol (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  k • jURawCol H₂ H₄ k b₀ b₁ b₂

noncomputable def jVCol (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  k • jVRawCol H₂ H₄ k b₀ b₁ b₂

/-- The known correction that distinguishes the raw `u`-column from the sum of
the two scalar columns. -/
noncomputable def jUCorrection (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  jOuterFactor H₂ b₀ b₁ b₂ * jF2 H₂ H₄ * jH8Base H₂ H₄ ^ (k - 1)

/-- The analogous correction for the raw `v`-column. -/
noncomputable def jVCorrection (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A[X] :=
  jOuterFactor H₂ b₀ b₁ b₂ * jF1 H₄ * jH2 H₂ * jH8Base H₂ H₄ ^ (k - 1)

noncomputable def blockA1 (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ : A) : A :=
  (jB3Col H₂ H₄ k b₀ b₁).coeff 5

noncomputable def blockC (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ : A) : A :=
  (jB3Col H₂ H₄ k b₀ b₁).coeff 6

noncomputable def blockD (H₂ H₄ : A[X]) (k : ℕ) (b₂ : A) : A :=
  (jB4Col H₂ H₄ k b₂).coeff 6

noncomputable def blockE (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ : A) : A :=
  (jB3Col H₂ H₄ k b₀ b₁).coeff 7

noncomputable def blockF (H₂ H₄ : A[X]) (k : ℕ) (b₂ : A) : A :=
  (jB4Col H₂ H₄ k b₂).coeff 7

noncomputable def blockL (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) : A :=
  (jVCorrection H₂ H₄ k b₀ b₁ b₂).coeff 1

noncomputable def jBlockColumns (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) :
    Fin 4 → A[X] :=
  ![jB3Col H₂ H₄ k b₀ b₁, jB4Col H₂ H₄ k b₂,
    jUCol H₂ H₄ k b₀ b₁ b₂, jVCol H₂ H₄ k b₀ b₁ b₂]

noncomputable def jBlockMatrix (H₂ H₄ : A[X]) (k : ℕ) (b₀ b₁ b₂ : A) :
    Matrix (Fin 4) (Fin 4) A :=
  fun i j => (jBlockColumns H₂ H₄ k b₀ b₁ b₂ j).coeff (4 + i)

noncomputable def jBlockLinear (H₂ H₄ : A[X]) (k : ℕ) (u v : A)
    (b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  jTopBase H₂ H₄ k b₀ b₁ b₂
    + C b₃ * jB3Col H₂ H₄ k b₀ b₁
    + C b₄ * jB4Col H₂ H₄ k b₂
    + C u * jUCol H₂ H₄ k b₀ b₁ b₂
    + C v * jVCol H₂ H₄ k b₀ b₁ b₂

/-- Exact scalar decomposition of the base part. -/
theorem jTopBase_scalar_decomposition (H₂ H₄ : A[X]) (k : ℕ)
    (b₀ b₁ b₂ : A) :
    jTopBase H₂ H₄ k b₀ b₁ b₂ = jScalarLinear H₂ H₄ k b₀ b₁ b₂ := by
  simp only [jTopBase, jScalarLinear, jScalarStage2, jScalarStage1,
    jScalarBase, jB0Col, jB1Col, jB2Col, jOuterFactor, jP1, jP2]
  ring

set_option maxHeartbeats 1000000 in
/-- The top model is affine in `(b₃,b₄,u,v)` through row seven. -/
theorem jTopLinear_block_mod_eight (H₂ H₄ : A[X]) (k : ℕ)
    (u v b₀ b₁ b₂ b₃ b₄ : A) :
    JetEq 8 (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄)
      (jBlockLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄) := by
  let B := jH8Base H₂ H₄ ^ k
  let F := k • (jH8Error H₂ H₄ u v * jH8Base H₂ H₄ ^ (k - 1))
  let E₃ := C b₃ * X ^ 4
  let E₄ := C b₄ * X ^ 4
  have hF : X ^ 4 ∣ F := by
    dsimp only [F]
    exact dvd_nsmul_of_dvd k
      (dvd_mul_of_dvd_left (jH8Error_dvd_four H₂ H₄ u v) _)
  have hE₃ : X ^ 4 ∣ E₃ := by
    refine ⟨C b₃, ?_⟩
    dsimp only [E₃]
    ring
  have hE₄ : X ^ 4 ∣ E₄ := by
    refine ⟨C b₄, ?_⟩
    dsimp only [E₄]
    ring
  have h₃ := mul_linear_mod (P := jH4 H₄) (Q := B) hE₃ hF
  have h₄ := mul_linear_mod (P := jH4 H₄) (Q := B) hE₄ hF
  have h₃' := (JetEq.refl 8 (jP1 H₂ b₀ b₁)).mul (by simpa [E₃, B, F,
    jH8LinearPower] using h₃)
  have h₄' := (JetEq.refl 8 (jP2 H₂ b₂)).mul (by simpa [E₄, B, F,
    jH8LinearPower] using h₄)
  have hsum := h₃'.add h₄'
  have hstart : JetEq 8 (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄)
      (jP1 H₂ b₀ b₁ *
          ((jH4 H₄ + C b₃ * X ^ 4) *
            (jH8Base H₂ H₄ ^ k
              + (k : A[X]) * (jH8Error H₂ H₄ u v * jH8Base H₂ H₄ ^ (k - 1))))
        + jP2 H₂ b₂ *
          ((jH4 H₄ + C b₄ * X ^ 4) *
            (jH8Base H₂ H₄ ^ k
              + (k : A[X]) * (jH8Error H₂ H₄ u v * jH8Base H₂ H₄ ^ (k - 1))))) := by
    apply JetEq.of_eq
    simp only [jTopLinear, jH8LinearPower, nsmul_eq_mul]
    ring
  apply hstart.trans
  apply hsum.trans
  apply JetEq.of_eq
  simp only [jBlockLinear, jTopBase, jB3Col, jB4Col, jUCol, jVCol,
    jURawCol, jVRawCol,
    jOuterFactor, jH8Error]
  ring

/-- The four structural columns start in row four, so the first three nonleading
rows contain only the scalar parameters `b₀,b₁,b₂`. -/
theorem jTopLinear_scalar_mod_four (H₂ H₄ : A[X]) (k : ℕ)
    (u v b₀ b₁ b₂ b₃ b₄ : A) :
    JetEq 4 (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄)
      (jScalarLinear H₂ H₄ k b₀ b₁ b₂) := by
  have htop := JetEq.mono (n := 4) (m := 8) (by omega)
    (jTopLinear_block_mod_eight H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄)
  apply htop.trans
  have hdrop : JetEq 4 (jBlockLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄)
      (jTopBase H₂ H₄ k b₀ b₁ b₂) := by
    rw [JetEq]
    refine ⟨C b₃ * (jP1 H₂ b₀ b₁ * (jH8Base H₂ H₄ ^ k))
      + C b₄ * (jP2 H₂ b₂ * (jH8Base H₂ H₄ ^ k))
      + C u * (k • (jOuterFactor H₂ b₀ b₁ b₂ * jH4 H₄ *
          (jF2 H₂ H₄ * jH8Base H₂ H₄ ^ (k - 1))))
      + C v * (k • (jOuterFactor H₂ b₀ b₁ b₂ * jH4 H₄ *
          (jF1 H₄ * jH8Base H₂ H₄ ^ (k - 1)))), ?_⟩
    simp only [jBlockLinear, jB3Col, jB4Col, jUCol, jVCol,
      jURawCol, jVRawCol]
    ring
  exact hdrop.trans (JetEq.of_eq (jTopBase_scalar_decomposition H₂ H₄ k b₀ b₁ b₂))

private theorem jH2_coeff_zero {H₂ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) : (jH2 H₂).coeff 0 = 1 := by
  rw [jH2, coeff_reflect]
  norm_num [revAt]
  rw [← hH₂d, hH₂m.coeff_natDegree]

private theorem jH4_coeff_zero {H₄ : A[X]} (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) : (jH4 H₄).coeff 0 = 1 := by
  rw [jH4, coeff_reflect]
  norm_num [revAt]
  rw [← hH₄d, hH₄m.coeff_natDegree]

private theorem jH8Base_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) :
    (jH8Base H₂ H₄).coeff 0 = 1 := by
  rw [jH8Base, Polynomial.mul_coeff_zero, jF1, jF2, coeff_add, coeff_add,
    Polynomial.mul_coeff_zero, jH2_coeff_zero hH₂m hH₂d,
    jH4_coeff_zero hH₄m hH₄d]
  norm_num

private theorem jH8Base_pow_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (k : ℕ) :
    (jH8Base H₂ H₄ ^ k).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero,
    jH8Base_coeff_zero hH₂m hH₂d hH₄m hH₄d, one_pow]

theorem scalar_pivot_b0 {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (u v b₀ b₁ b₂ b₃ b₄ : A) :
    (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 1
      = b₀ + (jScalarBase H₂ H₄ k).coeff 1 := by
  rw [(jTopLinear_scalar_mod_four H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff_eq
    (by omega)]
  simp only [jScalarLinear, jScalarStage2, jScalarStage1, coeff_add, coeff_C_mul,
    jB0Col, jB1Col, jB2Col, coeff_X_pow_mul']
  norm_num [Polynomial.mul_coeff_zero]
  rw [jH2_coeff_zero hH₂m hH₂d, jH4_coeff_zero hH₄m hH₄d,
    jH8Base_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

theorem scalar_pivot_b1 {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (u v b₀ b₁ b₂ b₃ b₄ : A) :
    (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 2
      = b₁ + (jScalarStage1 H₂ H₄ k b₀).coeff 2 := by
  rw [(jTopLinear_scalar_mod_four H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff_eq
    (by omega)]
  simp only [jScalarLinear, jScalarStage2, coeff_add, coeff_C_mul,
    jB1Col, jB2Col, coeff_X_pow_mul']
  norm_num [Polynomial.mul_coeff_zero]
  rw [jH4_coeff_zero hH₄m hH₄d,
    jH8Base_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

theorem scalar_pivot_b2 {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (u v b₀ b₁ b₂ b₃ b₄ : A) :
    (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 3
      = b₂ + (jScalarStage2 H₂ H₄ k b₀ b₁).coeff 3 := by
  rw [(jTopLinear_scalar_mod_four H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff_eq
    (by omega)]
  simp only [jScalarLinear, coeff_add, coeff_C_mul, jB2Col, coeff_X_pow_mul']
  norm_num [Polynomial.mul_coeff_zero]
  rw [jH4_coeff_zero hH₄m hH₄d,
    jH8Base_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

/-! ## The four-variable barred block -/

theorem jURawCol_decomposition (H₂ H₄ : A[X]) (k : ℕ) (hk : 1 ≤ k)
    (b₀ b₁ b₂ : A) :
    jURawCol H₂ H₄ k b₀ b₁ b₂
      = jB3Col H₂ H₄ k b₀ b₁ + jB4Col H₂ H₄ k b₂
        - X ^ 7 * jUCorrection H₂ H₄ k b₀ b₁ b₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [jURawCol, jB3Col, jB4Col, jUCorrection, jOuterFactor,
    jH8Base, jF1, pow_succ]
  rw [Nat.add_sub_cancel]
  ring

theorem jVRawCol_decomposition (H₂ H₄ : A[X]) (k : ℕ) (hk : 1 ≤ k)
    (b₀ b₁ b₂ : A) :
    jVRawCol H₂ H₄ k b₀ b₁ b₂
      = jB3Col H₂ H₄ k b₀ b₁ + jB4Col H₂ H₄ k b₂
        - X ^ 6 * jVCorrection H₂ H₄ k b₀ b₁ b₂ := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [jVRawCol, jB3Col, jB4Col, jVCorrection, jOuterFactor,
    jH8Base, jF2, pow_succ]
  rw [Nat.add_sub_cancel]
  ring

private theorem jF1_coeff_zero {H₄ : A[X]}
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) : (jF1 H₄).coeff 0 = 1 := by
  rw [jF1, coeff_add, jH4_coeff_zero hH₄m hH₄d]
  norm_num

private theorem jF2_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) :
    (jF2 H₂ H₄).coeff 0 = 1 := by
  rw [jF2, coeff_add, Polynomial.mul_coeff_zero,
    jH4_coeff_zero hH₄m hH₄d, jH2_coeff_zero hH₂m hH₂d]
  norm_num

private theorem jOuterFactor_coeff_zero {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2) (b₀ b₁ b₂ : A) :
    (jOuterFactor H₂ b₀ b₁ b₂).coeff 0 = 1 := by
  have hP₁ : (jP1 H₂ b₀ b₁).coeff 0 = 1 := by
    rw [jP1, Polynomial.mul_coeff_zero]
    norm_num
    rw [jH2_coeff_zero hH₂m hH₂d]
  have hP₂ : (jP2 H₂ b₂).coeff 0 = 0 := by
    rw [jP2, Polynomial.mul_coeff_zero]
    norm_num
  rw [jOuterFactor, coeff_add, hP₁, hP₂, add_zero]

private theorem jP1_coeff_zero {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2) (b₀ b₁ : A) :
    (jP1 H₂ b₀ b₁).coeff 0 = 1 := by
  rw [jP1, Polynomial.mul_coeff_zero]
  norm_num
  rw [jH2_coeff_zero hH₂m hH₂d]

private theorem jP2_coeff_zero (H₂ : A[X]) (b₂ : A) :
    (jP2 H₂ b₂).coeff 0 = 0 := by
  rw [jP2, Polynomial.mul_coeff_zero]
  norm_num

private theorem jP2_coeff_one {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2) (b₂ : A) :
    (jP2 H₂ b₂).coeff 1 = 1 := by
  rw [jP2, coeff_X_mul]
  norm_num [jH2_coeff_zero hH₂m hH₂d]

private theorem jUCorrection_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (b₀ b₁ b₂ : A) :
    (jUCorrection H₂ H₄ k b₀ b₁ b₂).coeff 0 = 1 := by
  rw [jUCorrection, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero,
    jOuterFactor_coeff_zero hH₂m hH₂d,
    jF2_coeff_zero hH₂m hH₂d hH₄m hH₄d,
    jH8Base_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

private theorem jVCorrection_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (b₀ b₁ b₂ : A) :
    (jVCorrection H₂ H₄ k b₀ b₁ b₂).coeff 0 = 1 := by
  rw [jVCorrection, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_zero,
    Polynomial.mul_coeff_zero,
    jOuterFactor_coeff_zero hH₂m hH₂d,
    jF1_coeff_zero hH₄m hH₄d, jH2_coeff_zero hH₂m hH₂d,
    jH8Base_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

private theorem jB3Col_coeff_four {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (b₀ b₁ : A) : (jB3Col H₂ H₄ k b₀ b₁).coeff 4 = 1 := by
  rw [jB3Col, coeff_X_pow_mul']
  norm_num
  rw [jP1_coeff_zero hH₂m hH₂d,
    jH8Base_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

private theorem jB4Col_coeff_four (H₂ H₄ : A[X]) (k : ℕ) (b₂ : A) :
    (jB4Col H₂ H₄ k b₂).coeff 4 = 0 := by
  rw [jB4Col, coeff_X_pow_mul']
  norm_num [jP2, Polynomial.mul_coeff_zero]

private theorem jB4Col_coeff_five {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (b₂ : A) : (jB4Col H₂ H₄ k b₂).coeff 5 = 1 := by
  rw [jB4Col, coeff_X_pow_mul']
  norm_num
  rw [Polynomial.mul_coeff_one, jP2_coeff_zero,
    jP2_coeff_one hH₂m hH₂d,
    jH8Base_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

private theorem jURawCol_rows {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (b₀ b₁ b₂ : A) :
    (jURawCol H₂ H₄ k b₀ b₁ b₂).coeff 4 = 1 ∧
    (jURawCol H₂ H₄ k b₀ b₁ b₂).coeff 5
      = blockA1 H₂ H₄ k b₀ b₁ + 1 ∧
    (jURawCol H₂ H₄ k b₀ b₁ b₂).coeff 6
      = blockC H₂ H₄ k b₀ b₁ + blockD H₂ H₄ k b₂ ∧
    (jURawCol H₂ H₄ k b₀ b₁ b₂).coeff 7
      = blockE H₂ H₄ k b₀ b₁ + blockF H₂ H₄ k b₂ - 1 := by
  rw [jURawCol_decomposition H₂ H₄ k hk b₀ b₁ b₂]
  simp only [coeff_add, coeff_sub, coeff_X_pow_mul']
  norm_num [blockA1, blockC, blockD, blockE, blockF,
    jB3Col_coeff_four hH₂m hH₂d hH₄m hH₄d,
    jB4Col_coeff_four, jB4Col_coeff_five hH₂m hH₂d hH₄m hH₄d,
    jUCorrection_coeff_zero hH₂m hH₂d hH₄m hH₄d]

private theorem jVRawCol_rows {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (b₀ b₁ b₂ : A) :
    (jVRawCol H₂ H₄ k b₀ b₁ b₂).coeff 4 = 1 ∧
    (jVRawCol H₂ H₄ k b₀ b₁ b₂).coeff 5
      = blockA1 H₂ H₄ k b₀ b₁ + 1 ∧
    (jVRawCol H₂ H₄ k b₀ b₁ b₂).coeff 6
      = blockC H₂ H₄ k b₀ b₁ + blockD H₂ H₄ k b₂ - 1 ∧
    (jVRawCol H₂ H₄ k b₀ b₁ b₂).coeff 7
      = blockE H₂ H₄ k b₀ b₁ + blockF H₂ H₄ k b₂
        - blockL H₂ H₄ k b₀ b₁ b₂ := by
  rw [jVRawCol_decomposition H₂ H₄ k hk b₀ b₁ b₂]
  simp only [coeff_add, coeff_sub, coeff_X_pow_mul']
  norm_num [blockA1, blockC, blockD, blockE, blockF, blockL,
    jB3Col_coeff_four hH₂m hH₂d hH₄m hH₄d,
    jB4Col_coeff_four, jB4Col_coeff_five hH₂m hH₂d hH₄m hH₄d,
    jVCorrection_coeff_zero hH₂m hH₂d hH₄m hH₄d]

/-- The four structural columns are exactly the barred pivot matrix from the
manuscript.  The determinant therefore depends only on `k`, not on any of the
coefficients decoded in earlier rows. -/
theorem jBlockMatrix_eq_barred {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (b₀ b₁ b₂ : A) :
    jBlockMatrix H₂ H₄ k b₀ b₁ b₂ =
      barredPivotMatrix (k : R)
        (blockA1 H₂ H₄ k b₀ b₁)
        (blockC H₂ H₄ k b₀ b₁)
        (blockD H₂ H₄ k b₂)
        (blockE H₂ H₄ k b₀ b₁)
        (blockF H₂ H₄ k b₂)
        (blockL H₂ H₄ k b₀ b₁ b₂) := by
  obtain ⟨hu₄, hu₅, hu₆, hu₇⟩ :=
    jURawCol_rows hH₂m hH₂d hH₄m hH₄d k hk b₀ b₁ b₂
  obtain ⟨hv₄, hv₅, hv₆, hv₇⟩ :=
    jVRawCol_rows hH₂m hH₂d hH₄m hH₄d k hk b₀ b₁ b₂
  rw [barredPivotMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jBlockMatrix, jBlockColumns, jUCol, jVCol, nsmul_eq_mul,
      blockA1, blockC, blockD, blockE, blockF, blockL,
      hu₄, hu₅, hu₆, hu₇, hv₄, hv₅, hv₆, hv₇,
      jB3Col_coeff_four hH₂m hH₂d hH₄m hH₄d,
      jB4Col_coeff_four, jB4Col_coeff_five hH₂m hH₂d hH₄m hH₄d,
      map_natCast]

/-- The complete top-eight decoder.  It performs three scalar pivots followed
by the fixed barred block solve; its only non-unit slope is the declared
constant `k`. -/
theorem top_params_mem {V : Subalgebra R A} {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (hkR : IsUnit (k : R))
    (u v b₀ b₁ b₂ b₃ b₄ : A)
    (hH₂V : ∀ j, H₂.coeff j ∈ V) (hH₄V : ∀ j, H₄.coeff j ∈ V)
    (hobs : ∀ i, i < 8 →
      (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff i ∈ V) :
    b₀ ∈ V ∧ b₁ ∈ V ∧ b₂ ∈ V ∧ b₃ ∈ V ∧ b₄ ∈ V ∧ u ∈ V ∧ v ∈ V := by
  have hX : CoeffsIn V (X : A[X]) := CoeffsIn.X V
  have hOne : CoeffsIn V (1 : A[X]) := CoeffsIn.one V
  have hH₂ : CoeffsIn V (jH2 H₂) := by
    intro j
    rw [jH2, coeff_reflect]
    exact hH₂V _
  have hH₄ : CoeffsIn V (jH4 H₄) := by
    intro j
    rw [jH4, coeff_reflect]
    exact hH₄V _
  have hF₁ : CoeffsIn V (jF1 H₄) := by
    rw [jF1]
    exact hH₄.add (hX.pow 3)
  have hF₂ : CoeffsIn V (jF2 H₂ H₄) := by
    rw [jF2]
    exact hH₄.add ((hX.pow 2).mul hH₂)
  have hH₈base : CoeffsIn V (jH8Base H₂ H₄) := by
    rw [jH8Base]
    exact hF₁.mul hF₂
  have hH₈pow : CoeffsIn V (jH8Base H₂ H₄ ^ k) := hH₈base.pow k
  have hScalarBase : CoeffsIn V (jScalarBase H₂ H₄ k) := by
    rw [jScalarBase]
    exact ((hH₂.add (hX.mul hH₂)).mul hH₄).mul hH₈pow

  have hb₀ : b₀ ∈ V := by
    have hkey : b₀ =
        (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 1 -
          (jScalarBase H₂ H₄ k).coeff 1 := by
      rw [scalar_pivot_b0 hH₂m hH₂d hH₄m hH₄d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs 1 (by omega)) (hScalarBase 1)
  have hB₀ : CoeffsIn V (jB0Col H₂ H₄ k) := by
    rw [jB0Col]
    exact (hX.pow 1).mul ((hH₂.mul hH₄).mul hH₈pow)
  have hStage₁ : CoeffsIn V (jScalarStage1 H₂ H₄ k b₀) := by
    rw [jScalarStage1]
    exact hScalarBase.add ((CoeffsIn.C hb₀).mul hB₀)
  have hb₁ : b₁ ∈ V := by
    have hkey : b₁ =
        (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 2 -
          (jScalarStage1 H₂ H₄ k b₀).coeff 2 := by
      rw [scalar_pivot_b1 hH₂m hH₂d hH₄m hH₄d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs 2 (by omega)) (hStage₁ 2)
  have hB₁ : CoeffsIn V (jB1Col H₂ H₄ k b₀) := by
    rw [jB1Col]
    exact (hX.pow 2).mul
      (((hOne.add ((CoeffsIn.C hb₀).mul hX)).mul hH₄).mul hH₈pow)
  have hStage₂ : CoeffsIn V (jScalarStage2 H₂ H₄ k b₀ b₁) := by
    rw [jScalarStage2]
    exact hStage₁.add ((CoeffsIn.C hb₁).mul hB₁)
  have hb₂ : b₂ ∈ V := by
    have hkey : b₂ =
        (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 3 -
          (jScalarStage2 H₂ H₄ k b₀ b₁).coeff 3 := by
      rw [scalar_pivot_b2 hH₂m hH₂d hH₄m hH₄d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hobs 3 (by omega)) (hStage₂ 3)

  have hP₁ : CoeffsIn V (jP1 H₂ b₀ b₁) := by
    rw [jP1]
    exact (hOne.add ((CoeffsIn.C hb₀).mul hX)).mul
      (hH₂.add ((CoeffsIn.C hb₁).mul (hX.pow 2)))
  have hP₂ : CoeffsIn V (jP2 H₂ b₂) := by
    rw [jP2]
    exact hX.mul (hH₂.add ((CoeffsIn.C hb₂).mul (hX.pow 2)))
  have hOuter : CoeffsIn V (jOuterFactor H₂ b₀ b₁ b₂) := by
    rw [jOuterFactor]
    exact hP₁.add hP₂
  have hTopBase : CoeffsIn V (jTopBase H₂ H₄ k b₀ b₁ b₂) := by
    rw [jTopBase]
    exact (hOuter.mul hH₄).mul hH₈pow
  have hB₃ : CoeffsIn V (jB3Col H₂ H₄ k b₀ b₁) := by
    rw [jB3Col]
    exact (hX.pow 4).mul (hP₁.mul hH₈pow)
  have hB₄ : CoeffsIn V (jB4Col H₂ H₄ k b₂) := by
    rw [jB4Col]
    exact (hX.pow 4).mul (hP₂.mul hH₈pow)
  have hU : CoeffsIn V (jUCol H₂ H₄ k b₀ b₁ b₂) := by
    rw [jUCol, jURawCol]
    exact (((hX.pow 4).mul ((hOuter.mul hH₄).mul
      (hF₂.mul (hH₈base.pow (k - 1))))).nsmul k)
  have hV : CoeffsIn V (jVCol H₂ H₄ k b₀ b₁ b₂) := by
    rw [jVCol, jVRawCol]
    exact (((hX.pow 4).mul ((hOuter.mul hH₄).mul
      (hF₁.mul (hH₈base.pow (k - 1))))).nsmul k)

  let unknown : Fin 4 → A := ![b₃, b₄, u, v]
  let y : Fin 4 → A := fun i =>
    (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff (4 + i)
  let e : Fin 4 → A := fun i =>
    (jTopBase H₂ H₄ k b₀ b₁ b₂).coeff (4 + i)
  let M := barredPivotMatrix (k : R)
    (blockA1 H₂ H₄ k b₀ b₁) (blockC H₂ H₄ k b₀ b₁)
    (blockD H₂ H₄ k b₂) (blockE H₂ H₄ k b₀ b₁)
    (blockF H₂ H₄ k b₂) (blockL H₂ H₄ k b₀ b₁ b₂)
  have hM : ∀ i j, M i j ∈ V := by
    intro i j
    rw [show M = jBlockMatrix H₂ H₄ k b₀ b₁ b₂ from
      (jBlockMatrix_eq_barred hH₂m hH₂d hH₄m hH₄d k hk b₀ b₁ b₂).symm]
    fin_cases j
    · exact hB₃ (4 + i)
    · exact hB₄ (4 + i)
    · exact hU (4 + i)
    · exact hV (4 + i)
  have he : ∀ i, e i ∈ V := fun i => hTopBase (4 + i)
  have hy : ∀ i, y i = ∑ j, M i j * unknown j + e i := by
    intro i
    have hrow := (jTopLinear_block_mod_eight H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff_eq
      (show 4 + (i : ℕ) < 8 by omega)
    rw [show M = jBlockMatrix H₂ H₄ k b₀ b₁ b₂ from
      (jBlockMatrix_eq_barred hH₂m hH₂d hH₄m hH₄d k hk b₀ b₁ b₂).symm]
    fin_cases i <;>
      simp [y, e, unknown, jBlockMatrix, jBlockColumns, jBlockLinear,
        coeff_add, coeff_C_mul, Fin.sum_univ_four] at hrow ⊢ <;>
      (rw [hrow]; ring)
  have hblock := mem_of_barredPivotCert V unknown y e (k : R)
    (blockA1 H₂ H₄ k b₀ b₁) (blockC H₂ H₄ k b₀ b₁)
    (blockD H₂ H₄ k b₂) (blockE H₂ H₄ k b₀ b₁)
    (blockF H₂ H₄ k b₂) (blockL H₂ H₄ k b₀ b₁ b₂)
    hkR hM he hy
  have hyV : ∀ i, y i ∈ V := fun i => hobs (4 + i) (by omega)
  have hcollapse : V ⊔ adjoin R (Set.range y) ≤ V :=
    sup_le le_rfl (adjoin_le fun z hz => by obtain ⟨i, rfl⟩ := hz; exact hyV i)
  have hb₃ : b₃ ∈ V := by simpa [unknown] using hcollapse (hblock 0)
  have hb₄ : b₄ ∈ V := by simpa [unknown] using hcollapse (hblock 1)
  have hu : u ∈ V := by simpa [unknown] using hcollapse (hblock 2)
  have hv : v ∈ V := by simpa [unknown] using hcollapse (hblock 3)
  exact ⟨hb₀, hb₁, hb₂, hb₃, hb₄, hu, hv⟩

/-! ## The two boundary rows -/

noncomputable def jG1 (H₂ H₄ : A[X]) (b₀ b₁ b₃ : A) : A[X] :=
  jP1 H₂ b₀ b₁ * (jH4 H₄ + C b₃ * X ^ 4)

noncomputable def jG2 (H₂ H₄ : A[X]) (b₂ b₄ : A) : A[X] :=
  jP2 H₂ b₂ * (jH4 H₄ + C b₄ * X ^ 4)

/-- The reflected octic after `u,v` are decoded but before the scalar `w` is
inserted in row eight. -/
noncomputable def jH8NoW (H₂ H₄ : A[X]) (u v : A) : A[X] :=
  (jF1 H₄ + C u * X ^ 4) * (jF2 H₂ H₄ + C v * X ^ 4)

noncomputable def jMidBase (H₂ H₄ : A[X]) (k : ℕ)
    (JR₁ JR₂ : A[X]) (u v b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  (jG1 H₂ H₄ b₀ b₁ b₃ + jG2 H₂ H₄ b₂ b₄) *
      jH8NoW H₂ H₄ u v ^ k
    + X ^ 8 * (jG1 H₂ H₄ b₀ b₁ b₃ * JR₁
      + jG2 H₂ H₄ b₂ b₄ * JR₂)

noncomputable def jWCol (H₂ H₄ : A[X]) (k : ℕ)
    (u v b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  k • (X ^ 8 *
    ((jG1 H₂ H₄ b₀ b₁ b₃ + jG2 H₂ H₄ b₂ b₄) *
      jH8NoW H₂ H₄ u v ^ (k - 1)))

noncomputable def jRhoCol (H₂ H₄ : A[X]) (k : ℕ)
    (u v b₂ b₄ : A) : A[X] :=
  k • (X ^ 8 *
    (jG2 H₂ H₄ b₂ b₄ * jH8NoW H₂ H₄ u v ^ (k - 1)))

noncomputable def jMidLinear (H₂ H₄ : A[X]) (k : ℕ)
    (JR₁ JR₂ : A[X]) (w rho u v b₀ b₁ b₂ b₃ b₄ : A) : A[X] :=
  jMidBase H₂ H₄ k JR₁ JR₂ u v b₀ b₁ b₂ b₃ b₄
    + C w * jWCol H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄
    + C rho * jRhoCol H₂ H₄ k u v b₂ b₄

theorem jH8_eq_noW (H₂ H₄ : A[X]) (u v w : A) :
    jH8 H₂ H₄ u v w = jH8NoW H₂ H₄ u v + C w * X ^ 8 := by
  simp only [jH8, jH8NoW]

set_option maxHeartbeats 1000000 in
/-- First-order expansion in the row-eight scalar shifts.  Quadratic terms
start in row sixteen, so rows eight and nine are exact. -/
theorem jMain_mid_mod_ten (H₂ H₄ : A[X]) (k : ℕ) (hk : 1 ≤ k)
    (JR₁ JR₂ : A[X]) (w rho u v b₀ b₁ b₂ b₃ b₄ : A) :
    JetEq 10
      (jG1 H₂ H₄ b₀ b₁ b₃ *
          ((jH8 H₂ H₄ u v w) ^ k + JR₁ * X ^ 8)
        + jG2 H₂ H₄ b₂ b₄ *
          ((jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k + JR₂ * X ^ 8))
      (jMidLinear H₂ H₄ k JR₁ JR₂
        w rho u v b₀ b₁ b₂ b₃ b₄) := by
  let B := jH8NoW H₂ H₄ u v
  let E₁ : A[X] := C w * X ^ 8
  let E₂ : A[X] := C (w + rho) * X ^ 8
  have hE₁ : X ^ 8 ∣ E₁ := by
    refine ⟨C w, ?_⟩
    simp only [E₁]
    ring
  have hE₂ : X ^ 8 ∣ E₂ := by
    refine ⟨C (w + rho), ?_⟩
    simp only [E₂]
    ring
  have hp₁ := JetEq.mono (n := 10) (m := 16) (by omega)
    (pow_linear_mod (B := B) hE₁ hk)
  have hp₂ := JetEq.mono (n := 10) (m := 16) (by omega)
    (pow_linear_mod (B := B) hE₂ hk)
  have h₁ := (JetEq.refl 10 (jG1 H₂ H₄ b₀ b₁ b₃)).mul
    (hp₁.add (JetEq.refl 10 (JR₁ * X ^ 8)))
  have h₂ := (JetEq.refl 10 (jG2 H₂ H₄ b₂ b₄)).mul
    (hp₂.add (JetEq.refl 10 (JR₂ * X ^ 8)))
  have hstart :
      jG1 H₂ H₄ b₀ b₁ b₃ *
          ((jH8 H₂ H₄ u v w) ^ k + JR₁ * X ^ 8)
        + jG2 H₂ H₄ b₂ b₄ *
          ((jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k + JR₂ * X ^ 8)
        = jG1 H₂ H₄ b₀ b₁ b₃ * ((B + E₁) ^ k + JR₁ * X ^ 8)
          + jG2 H₂ H₄ b₂ b₄ * ((B + E₂) ^ k + JR₂ * X ^ 8) := by
    simp only [B, E₁, E₂, jH8_eq_noW, map_add]
    ring
  apply (JetEq.of_eq hstart).trans
  apply (h₁.add h₂).trans
  apply JetEq.of_eq
  simp only [jMidLinear, jMidBase, jWCol, jRhoCol,
    B, E₁, E₂, nsmul_eq_mul, map_add]
  ring

/-- Above row ten the six low crown parameters are invisible.  This is the
single support statement needed to expose the two internal `T` outputs. -/
theorem jOuter_main_mod_ten {N : ℕ} (hN : 10 ≤ N + 1)
    (H₂ H₄ jS₁ jS₂ : A[X])
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    JetEq 10
      (jOuter N H₂ H₄ jS₁ jS₂
        a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄)
      (jG1 H₂ H₄ b₀ b₁ b₃ * jS₁ + jG2 H₂ H₄ b₂ b₄ * jS₂) := by
  let F₃ := jH4 H₄ + C b₃ * X ^ 4
  let F₄ := jH4 H₄ + C b₄ * X ^ 4
  let P₁ := jH2 H₂ + C b₁ * X ^ 2
  let P₂ := jH2 H₂ + C b₂ * X ^ 2
  have hUprod : JetEq 10 (F₃ * jS₁) (F₃ * jS₁) := JetEq.refl 10 _
  have hUlow : JetEq 10 (X ^ (N + 1) * jQ3 H₂ a₃ a₄ a₅) 0 :=
    JetEq.zero_X_pow_mul_of_le hN _
  have hU : JetEq 10 (jU0 N H₂ H₄ jS₁ a₃ a₄ a₅ b₃) (F₃ * jS₁) := by
    simpa [jU0, F₃] using hUprod.add hUlow
  have hVprod : JetEq 10 (F₄ * jS₂) (F₄ * jS₂) := JetEq.refl 10 _
  have hVlow : JetEq 10 (C a₂ * X ^ (N + 4)) 0 := by
    rw [mul_comm]
    exact JetEq.zero_X_pow_mul_of_le (by omega) _
  have hV : JetEq 10 (jV0 N H₄ jS₂ a₂ b₄) (F₄ * jS₂) := by
    simpa [jV0, F₄] using hVprod.add hVlow
  have hC₁prod : JetEq 10 (P₁ * jU0 N H₂ H₄ jS₁ a₃ a₄ a₅ b₃)
      (P₁ * (F₃ * jS₁)) := (JetEq.refl 10 P₁).mul hU
  have hC₁low : JetEq 10 (C a₁ * X ^ (N + 6)) 0 := by
    rw [mul_comm]
    exact JetEq.zero_X_pow_mul_of_le (by omega) _
  have hC₁ : JetEq 10 (jC1 N H₂ H₄ jS₁ a₁ a₃ a₄ a₅ b₁ b₃)
      (P₁ * (F₃ * jS₁)) := by
    simpa [jC1, P₁] using hC₁prod.add hC₁low
  have hC₂prod : JetEq 10 (P₂ * jV0 N H₄ jS₂ a₂ b₄)
      (P₂ * (F₄ * jS₂)) := (JetEq.refl 10 P₂).mul hV
  have hC₂low : JetEq 10 (C a₀ * X ^ (N + 6)) 0 := by
    rw [mul_comm]
    exact JetEq.zero_X_pow_mul_of_le (by omega) _
  have hC₂ : JetEq 10 (jC2 N H₂ H₄ jS₂ a₀ a₂ b₂ b₄)
      (P₂ * (F₄ * jS₂)) := by
    simpa [jC2, P₂] using hC₂prod.add hC₂low
  have hleft := (JetEq.refl 10 (1 + C b₀ * X)).mul hC₁
  have hright := (JetEq.refl 10 X).mul hC₂
  apply (hleft.add hright).trans
  apply JetEq.of_eq
  simp only [jG1, jG2, jP1, jP2, P₁, P₂, F₃, F₄]
  ring

private theorem jG1_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (b₀ b₁ b₃ : A) : (jG1 H₂ H₄ b₀ b₁ b₃).coeff 0 = 1 := by
  rw [jG1, Polynomial.mul_coeff_zero, jP1_coeff_zero hH₂m hH₂d,
    coeff_add, jH4_coeff_zero hH₄m hH₄d]
  norm_num

private theorem jG2_coeff_zero (H₂ H₄ : A[X]) (b₂ b₄ : A) :
    (jG2 H₂ H₄ b₂ b₄).coeff 0 = 0 := by
  rw [jG2, Polynomial.mul_coeff_zero, jP2_coeff_zero]
  ring

private theorem jG2_coeff_one {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (b₂ b₄ : A) : (jG2 H₂ H₄ b₂ b₄).coeff 1 = 1 := by
  rw [jG2, Polynomial.mul_coeff_one, jP2_coeff_zero,
    jP2_coeff_one hH₂m hH₂d]
  norm_num
  rw [jH4_coeff_zero hH₄m hH₄d]

private theorem jH8NoW_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (u v : A) : (jH8NoW H₂ H₄ u v).coeff 0 = 1 := by
  rw [jH8NoW, Polynomial.mul_coeff_zero, coeff_add, coeff_add,
    jF1_coeff_zero hH₄m hH₄d,
    jF2_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  norm_num

private theorem jH8NoW_pow_coeff_zero {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (u v : A) (m : ℕ) : (jH8NoW H₂ H₄ u v ^ m).coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero,
    jH8NoW_coeff_zero hH₂m hH₂d hH₄m hH₄d, one_pow]

private theorem jWCol_coeff_eight {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (u v b₀ b₁ b₂ b₃ b₄ : A) :
    (jWCol H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 8 = (k : A) := by
  rw [jWCol, coeff_smul, nsmul_eq_mul, coeff_X_pow_mul']
  norm_num
  rw [jG1_coeff_zero hH₂m hH₂d hH₄m hH₄d,
    jG2_coeff_zero, add_zero,
    jH8NoW_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

private theorem jRhoCol_coeff_eight (H₂ H₄ : A[X]) (k : ℕ)
    (u v b₂ b₄ : A) :
    (jRhoCol H₂ H₄ k u v b₂ b₄).coeff 8 = 0 := by
  rw [jRhoCol, coeff_smul, nsmul_eq_mul, coeff_X_pow_mul']
  norm_num [Polynomial.mul_coeff_zero, jG2_coeff_zero]

private theorem jRhoCol_coeff_nine {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (u v b₂ b₄ : A) :
    (jRhoCol H₂ H₄ k u v b₂ b₄).coeff 9 = (k : A) := by
  rw [jRhoCol, coeff_smul, nsmul_eq_mul, coeff_X_pow_mul']
  norm_num
  rw [Polynomial.mul_coeff_one, jG2_coeff_zero,
    jG2_coeff_one hH₂m hH₂d hH₄m hH₄d,
    jH8NoW_pow_coeff_zero hH₂m hH₂d hH₄m hH₄d]
  ring

theorem mid_pivot_w {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (JR₁ JR₂ : A[X]) (w rho u v b₀ b₁ b₂ b₃ b₄ : A) :
    (jMidLinear H₂ H₄ k JR₁ JR₂ w rho u v b₀ b₁ b₂ b₃ b₄).coeff 8
      = (k : A) * w +
        (jMidBase H₂ H₄ k JR₁ JR₂ u v b₀ b₁ b₂ b₃ b₄).coeff 8 := by
  rw [jMidLinear, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
    jWCol_coeff_eight hH₂m hH₂d hH₄m hH₄d,
    jRhoCol_coeff_eight]
  ring

theorem mid_pivot_rho {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (JR₁ JR₂ : A[X]) (w rho u v b₀ b₁ b₂ b₃ b₄ : A) :
    (jMidLinear H₂ H₄ k JR₁ JR₂ w rho u v b₀ b₁ b₂ b₃ b₄).coeff 9
      = (k : A) * rho
        + w * (jWCol H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 9
        + (jMidBase H₂ H₄ k JR₁ JR₂ u v b₀ b₁ b₂ b₃ b₄).coeff 9 := by
  rw [jMidLinear, coeff_add, coeff_add, coeff_C_mul, coeff_C_mul,
    jRhoCol_coeff_nine hH₂m hH₂d hH₄m hH₄d]
  ring

/-- Only the first two coefficients of each reflected remainder can enter the
two boundary rows. -/
private theorem jMidBase_boundary_mem {V : Subalgebra R A}
    (H₂ H₄ : A[X]) (k : ℕ) (JR₁ JR₂ : A[X])
    (u v b₀ b₁ b₂ b₃ b₄ : A)
    (hG₁ : CoeffsIn V (jG1 H₂ H₄ b₀ b₁ b₃))
    (hG₂ : CoeffsIn V (jG2 H₂ H₄ b₂ b₄))
    (hB : CoeffsIn V (jH8NoW H₂ H₄ u v))
    (hR₁₀ : JR₁.coeff 0 ∈ V) (hR₁₁ : JR₁.coeff 1 ∈ V)
    (hR₂₀ : JR₂.coeff 0 ∈ V) (hR₂₁ : JR₂.coeff 1 ∈ V) :
    (jMidBase H₂ H₄ k JR₁ JR₂ u v b₀ b₁ b₂ b₃ b₄).coeff 8 ∈ V ∧
      (jMidBase H₂ H₄ k JR₁ JR₂ u v b₀ b₁ b₂ b₃ b₄).coeff 9 ∈ V := by
  have hmain : CoeffsIn V
      ((jG1 H₂ H₄ b₀ b₁ b₃ + jG2 H₂ H₄ b₂ b₄) *
        jH8NoW H₂ H₄ u v ^ k) := (hG₁.add hG₂).mul (hB.pow k)
  have hrem₀ :
      (jG1 H₂ H₄ b₀ b₁ b₃).coeff 0 * JR₁.coeff 0
        + (jG2 H₂ H₄ b₂ b₄).coeff 0 * JR₂.coeff 0 ∈ V :=
    Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hG₁ 0) hR₁₀)
      (Subalgebra.mul_mem _ (hG₂ 0) hR₂₀)
  have hrem₁ :
      ((jG1 H₂ H₄ b₀ b₁ b₃).coeff 0 * JR₁.coeff 1
          + (jG1 H₂ H₄ b₀ b₁ b₃).coeff 1 * JR₁.coeff 0)
        + ((jG2 H₂ H₄ b₂ b₄).coeff 0 * JR₂.coeff 1
          + (jG2 H₂ H₄ b₂ b₄).coeff 1 * JR₂.coeff 0) ∈ V :=
    Subalgebra.add_mem _
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hG₁ 0) hR₁₁)
        (Subalgebra.mul_mem _ (hG₁ 1) hR₁₀))
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hG₂ 0) hR₂₁)
        (Subalgebra.mul_mem _ (hG₂ 1) hR₂₀))
  constructor
  · rw [jMidBase, coeff_add, coeff_X_pow_mul']
    norm_num
    exact Subalgebra.add_mem _ (hmain 8) hrem₀
  · rw [jMidBase, coeff_add, coeff_X_pow_mul']
    norm_num
    rw [Polynomial.mul_coeff_one, Polynomial.mul_coeff_one]
    exact Subalgebra.add_mem _ (hmain 9) hrem₁

/-- Explicit recovery of the two seam scalars from rows eight and nine. -/
theorem mid_params_mem {V : Subalgebra R A} {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hkR : IsUnit (k : R)) (JR₁ JR₂ : A[X])
    (w rho u v b₀ b₁ b₂ b₃ b₄ : A)
    (hH₂V : ∀ j, H₂.coeff j ∈ V) (hH₄V : ∀ j, H₄.coeff j ∈ V)
    (hb₀ : b₀ ∈ V) (hb₁ : b₁ ∈ V) (hb₂ : b₂ ∈ V)
    (hb₃ : b₃ ∈ V) (hb₄ : b₄ ∈ V) (hu : u ∈ V) (hv : v ∈ V)
    (hR₁₀ : JR₁.coeff 0 ∈ V) (hR₁₁ : JR₁.coeff 1 ∈ V)
    (hR₂₀ : JR₂.coeff 0 ∈ V) (hR₂₁ : JR₂.coeff 1 ∈ V)
    (hobs₈ : (jMidLinear H₂ H₄ k JR₁ JR₂
      w rho u v b₀ b₁ b₂ b₃ b₄).coeff 8 ∈ V)
    (hobs₉ : (jMidLinear H₂ H₄ k JR₁ JR₂
      w rho u v b₀ b₁ b₂ b₃ b₄).coeff 9 ∈ V) :
    w ∈ V ∧ rho ∈ V := by
  have hX : CoeffsIn V (X : A[X]) := CoeffsIn.X V
  have hOne : CoeffsIn V (1 : A[X]) := CoeffsIn.one V
  have hH₂ : CoeffsIn V (jH2 H₂) := by
    intro j
    rw [jH2, coeff_reflect]
    exact hH₂V _
  have hH₄ : CoeffsIn V (jH4 H₄) := by
    intro j
    rw [jH4, coeff_reflect]
    exact hH₄V _
  have hP₁ : CoeffsIn V (jP1 H₂ b₀ b₁) := by
    rw [jP1]
    exact (hOne.add ((CoeffsIn.C hb₀).mul hX)).mul
      (hH₂.add ((CoeffsIn.C hb₁).mul (hX.pow 2)))
  have hP₂ : CoeffsIn V (jP2 H₂ b₂) := by
    rw [jP2]
    exact hX.mul (hH₂.add ((CoeffsIn.C hb₂).mul (hX.pow 2)))
  have hG₁ : CoeffsIn V (jG1 H₂ H₄ b₀ b₁ b₃) := by
    rw [jG1]
    exact hP₁.mul (hH₄.add ((CoeffsIn.C hb₃).mul (hX.pow 4)))
  have hG₂ : CoeffsIn V (jG2 H₂ H₄ b₂ b₄) := by
    rw [jG2]
    exact hP₂.mul (hH₄.add ((CoeffsIn.C hb₄).mul (hX.pow 4)))
  have hF₁ : CoeffsIn V (jF1 H₄) := by
    rw [jF1]
    exact hH₄.add (hX.pow 3)
  have hF₂ : CoeffsIn V (jF2 H₂ H₄) := by
    rw [jF2]
    exact hH₄.add ((hX.pow 2).mul hH₂)
  have hB : CoeffsIn V (jH8NoW H₂ H₄ u v) := by
    rw [jH8NoW]
    exact (hF₁.add ((CoeffsIn.C hu).mul (hX.pow 4))).mul
      (hF₂.add ((CoeffsIn.C hv).mul (hX.pow 4)))
  obtain ⟨hbase₈, hbase₉⟩ := jMidBase_boundary_mem H₂ H₄ k JR₁ JR₂
    u v b₀ b₁ b₂ b₃ b₄ hG₁ hG₂ hB hR₁₀ hR₁₁ hR₂₀ hR₂₁
  have hw : w ∈ V := by
    have hx :
        (jMidLinear H₂ H₄ k JR₁ JR₂
          w rho u v b₀ b₁ b₂ b₃ b₄).coeff 8
          - (jMidBase H₂ H₄ k JR₁ JR₂
            u v b₀ b₁ b₂ b₃ b₄).coeff 8 ∈ V :=
      Subalgebra.sub_mem _ hobs₈ hbase₈
    apply mem_of_nat_slope hkR hx
    rw [mid_pivot_w hH₂m hH₂d hH₄m hH₄d]
    ring
  have hW : CoeffsIn V (jWCol H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄) := by
    rw [jWCol]
    exact ((hX.pow 8).mul ((hG₁.add hG₂).mul (hB.pow (k - 1)))).nsmul k
  have hrho : rho ∈ V := by
    have hx :
        (jMidLinear H₂ H₄ k JR₁ JR₂
          w rho u v b₀ b₁ b₂ b₃ b₄).coeff 9
          - w * (jWCol H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff 9
          - (jMidBase H₂ H₄ k JR₁ JR₂
            u v b₀ b₁ b₂ b₃ b₄).coeff 9 ∈ V :=
      Subalgebra.sub_mem _
        (Subalgebra.sub_mem _ hobs₉ (Subalgebra.mul_mem _ hw (hW 9))) hbase₉
    apply mem_of_nat_slope hkR hx
    rw [mid_pivot_rho hH₂m hH₂d hH₄m hH₄d]
    ring
  exact ⟨hw, hrho⟩

/-- The two reflected boundary coefficients of each internal remainder are
already known before `w,rho` are decoded.  This is the precise use of
`Rk2l_top_two` in the barred construction. -/
theorem remainder_boundary_mem [Nontrivial A] {V : Subalgebra R A}
    {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℕ → A) (u v w rho : A)
    (hH₂V : ∀ j, H₂.coeff j ∈ V) (hH₄V : ∀ j, H₄.coeff j ∈ V)
    (hu : u ∈ V) (hv : v ∈ V) :
    let H₈ := H8 H₂ H₄ u v w
    let Ht := H₈ + C rho
    let Hp := tower H₂ H₄ H₈
    let RR := Rpair Hp Ht k 3 beta
    let D := (k - 1) * 8
    (RR.1.reflect D).coeff 0 ∈ V ∧ (RR.1.reflect D).coeff 1 ∈ V ∧
      (RR.2.reflect D).coeff 0 ∈ V ∧ (RR.2.reflect D).coeff 1 ∈ V := by
  dsimp only
  let H₈ := H8 H₂ H₄ u v w
  let Ht := H₈ + C rho
  let Hp := tower H₂ H₄ H₈
  let RR := Rpair Hp Ht k 3 beta
  let D := (k - 1) * 8
  obtain ⟨hH₈m, hH₈d⟩ := H8_good hH₂m hH₂d hH₄m hH₄d u v w
  obtain ⟨hHtm, hHtd⟩ := add_C_good hH₈m hH₈d rho (by omega)
  have hTower := tower_good hH₂m hH₂d hH₄m hH₄d hH₈m hH₈d
  have hX : CoeffsIn V (X : A[X]) := CoeffsIn.X V
  have hH₂c : CoeffsIn V H₂ := hH₂V
  have hH₄c : CoeffsIn V H₄ := hH₄V
  have hbase : CoeffsIn V
      ((H₄ + (X + C u)) * (H₄ + (H₂ + C v))) :=
    (hH₄c.add (hX.add (CoeffsIn.C hu))).mul
      (hH₄c.add (hH₂c.add (CoeffsIn.C hv)))
  have hH₈sub : H₈.coeff 7 ∈ V := by
    simp only [H₈, H8, coeff_add, coeff_C]
    norm_num
    exact hbase 7
  have hHtsub : Ht.coeff 7 ∈ V := by
    simp only [Ht, coeff_add, coeff_C]
    norm_num
    exact hH₈sub
  have hH₄sub : (Hp 2).coeff (2 ^ 2 - 1) ∈ V := by
    simp only [Hp, tower_two]
    norm_num
    exact hH₄V 3
  obtain ⟨hR₁₀, hR₁₁, hR₂₀, hR₂₁⟩ :=
    Rk2l_top_two (K := V) (Hp := Hp) (Ht := Ht) (k := k) (l := 3)
      (α := beta) (by omega) (by omega) hTower hHtm hHtd
      (by intro h; omega) hH₄sub (by simpa only [Hp, tower_three] using hH₈sub) hHtsub
  norm_num at hR₁₀ hR₁₁ hR₂₀ hR₂₁
  have hjR₁₀ : (RR.1.reflect D).coeff 0 ∈ V := by
    rw [coeff_reflect]
    simpa only [D, revAt, Nat.sub_zero] using hR₁₀
  have hjR₁₁ : (RR.1.reflect D).coeff 1 ∈ V := by
    rw [coeff_reflect]
    rw [show revAt D 1 = D - 1 by simp [revAt, D]; omega]
    simpa only [D, RR] using hR₁₁
  have hjR₂₀ : (RR.2.reflect D).coeff 0 ∈ V := by
    rw [coeff_reflect]
    simpa only [D, revAt, Nat.sub_zero] using hR₂₀
  have hjR₂₁ : (RR.2.reflect D).coeff 1 ∈ V := by
    rw [coeff_reflect]
    rw [show revAt D 1 = D - 1 by simp [revAt, D]; omega]
    simpa only [D, RR] using hR₂₁
  exact ⟨hjR₁₀, hjR₁₁, hjR₂₀, hjR₂₁⟩

/-! ## The six low unit pivots -/

theorem low_pivot_a5 [Nontrivial A] {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 5 =
      a₅ + (lowStage5 H₂ b₀ b₁).coeff 5 := by
  obtain ⟨hL₅m, hL₅d, hL₄m, hL₄d, hL₃m, hL₃d,
    hL₂m, hL₂d, hL₁m, hL₁d⟩ :=
    low_factors_good hH₂m hH₂d a₅ b₀ b₁ b₂
  have hz₄ : (lowL4 H₂ a₅ b₀ b₁).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz₃ : (lowL3 H₂ b₀ b₁).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz₂ : (lowL2 H₂ b₂).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz₁ : (lowL1 b₀ : A[X]).coeff 5 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [lowCore_expansion, lowStage0, lowStage1, lowStage2, lowStage3, lowStage4,
    coeff_add, coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_C, hz₄, hz₃, hz₂, hz₁]
  norm_num
  rw [← hL₅d, hL₅m.coeff_natDegree]
  ring

theorem low_pivot_a4 [Nontrivial A] {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 4 =
      a₄ + (lowStage4 H₂ a₅ b₀ b₁).coeff 4 := by
  obtain ⟨-, -, hL₄m, hL₄d, hL₃m, hL₃d,
    hL₂m, hL₂d, hL₁m, hL₁d⟩ :=
    low_factors_good hH₂m hH₂d a₅ b₀ b₁ b₂
  have hz₃ : (lowL3 H₂ b₀ b₁).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz₂ : (lowL2 H₂ b₂).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz₁ : (lowL1 b₀ : A[X]).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [lowCore_expansion, lowStage0, lowStage1, lowStage2, lowStage3,
    coeff_add, coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_C_mul, coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_C, hz₃, hz₂, hz₁]
  norm_num
  rw [← hL₄d, hL₄m.coeff_natDegree]
  ring

theorem low_pivot_a3 [Nontrivial A] {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 3 =
      a₃ + (lowStage3 H₂ a₄ a₅ b₀ b₁).coeff 3 := by
  obtain ⟨-, -, -, -, hL₃m, hL₃d, hL₂m, hL₂d, hL₁m, hL₁d⟩ :=
    low_factors_good hH₂m hH₂d a₅ b₀ b₁ b₂
  have hz₂ : (lowL2 H₂ b₂).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  have hz₁ : (lowL1 b₀ : A[X]).coeff 3 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [lowCore_expansion, lowStage0, lowStage1, lowStage2,
    coeff_add, coeff_add, coeff_add, coeff_add,
    coeff_C_mul, coeff_C_mul, coeff_C_mul,
    coeff_C, hz₂, hz₁]
  norm_num
  rw [← hL₃d, hL₃m.coeff_natDegree]
  ring

theorem low_pivot_a2 [Nontrivial A] {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 2 =
      a₂ + (lowStage2 H₂ a₃ a₄ a₅ b₀ b₁).coeff 2 := by
  obtain ⟨-, -, -, -, -, -, hL₂m, hL₂d, hL₁m, hL₁d⟩ :=
    low_factors_good hH₂m hH₂d a₅ b₀ b₁ b₂
  have hz₁ : (lowL1 b₀ : A[X]).coeff 2 = 0 :=
    coeff_eq_zero_of_natDegree_lt (by omega)
  rw [lowCore_expansion, lowStage0, lowStage1,
    coeff_add, coeff_add, coeff_add,
    coeff_C_mul, coeff_C_mul,
    coeff_C, hz₁]
  norm_num
  rw [← hL₂d, hL₂m.coeff_natDegree]
  ring

theorem low_pivot_a1 [Nontrivial A] {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 1 =
      a₁ + (lowStage1 H₂ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hL₁m, hL₁d⟩ :=
    low_factors_good hH₂m hH₂d a₅ b₀ b₁ b₂
  rw [lowCore_expansion, lowStage0, coeff_add, coeff_add, coeff_C_mul,
    coeff_C]
  norm_num
  rw [← hL₁d, hL₁m.coeff_natDegree]
  ring

theorem low_pivot_a0 (H₂ : A[X])
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A) :
    (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 0 =
      a₀ + (lowStage0 H₂ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 0 := by
  rw [lowCore_expansion, coeff_add, coeff_C]
  norm_num
  ring

/-- Descending decoder for the six low crown parameters. -/
theorem low_params_mem [Nontrivial A] {V : Subalgebra R A} {H₂ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ : A)
    (hH₂V : ∀ j, H₂.coeff j ∈ V) (hb₀ : b₀ ∈ V) (hb₁ : b₁ ∈ V)
    (hb₂ : b₂ ∈ V)
    (hlow : ∀ j,
      (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff j ∈ V) :
    a₅ ∈ V ∧ a₄ ∈ V ∧ a₃ ∈ V ∧ a₂ ∈ V ∧ a₁ ∈ V ∧ a₀ ∈ V := by
  have hX : CoeffsIn V (X : A[X]) := CoeffsIn.X V
  have hOne : CoeffsIn V (1 : A[X]) := CoeffsIn.one V
  have hH₂ : CoeffsIn V H₂ := hH₂V
  have hL₃ : CoeffsIn V (lowL3 H₂ b₀ b₁) := by
    rw [lowL3]
    exact (hX.add (CoeffsIn.C hb₀)).mul (hH₂.add (CoeffsIn.C hb₁))
  have hL₅ : CoeffsIn V (lowL5 H₂ b₀ b₁) := by
    rw [lowL5]
    exact hL₃.mul hH₂
  have hStage₅ : CoeffsIn V (lowStage5 H₂ b₀ b₁) := by
    rw [lowStage5]
    exact hL₃.mul (hX.mul hH₂)
  have ha₅ : a₅ ∈ V := by
    have hkey : a₅ =
        (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 5
          - (lowStage5 H₂ b₀ b₁).coeff 5 := by
      rw [low_pivot_a5 hH₂m hH₂d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hlow 5) (hStage₅ 5)
  have hStage₄ : CoeffsIn V (lowStage4 H₂ a₅ b₀ b₁) := by
    rw [lowStage4]
    exact hStage₅.add ((CoeffsIn.C ha₅).mul hL₅)
  have ha₄ : a₄ ∈ V := by
    have hkey : a₄ =
        (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 4
          - (lowStage4 H₂ a₅ b₀ b₁).coeff 4 := by
      rw [low_pivot_a4 hH₂m hH₂d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hlow 4) (hStage₄ 4)
  have hL₄ : CoeffsIn V (lowL4 H₂ a₅ b₀ b₁) := by
    rw [lowL4]
    exact hL₃.mul (hX.add (CoeffsIn.C ha₅))
  have hStage₃ : CoeffsIn V (lowStage3 H₂ a₄ a₅ b₀ b₁) := by
    rw [lowStage3]
    exact hStage₄.add ((CoeffsIn.C ha₄).mul hL₄)
  have ha₃ : a₃ ∈ V := by
    have hkey : a₃ =
        (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 3
          - (lowStage3 H₂ a₄ a₅ b₀ b₁).coeff 3 := by
      rw [low_pivot_a3 hH₂m hH₂d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hlow 3) (hStage₃ 3)
  have hStage₂ : CoeffsIn V (lowStage2 H₂ a₃ a₄ a₅ b₀ b₁) := by
    rw [lowStage2]
    exact hStage₃.add ((CoeffsIn.C ha₃).mul hL₃)
  have hL₂ : CoeffsIn V (lowL2 H₂ b₂) := by
    rw [lowL2]
    exact hH₂.add (CoeffsIn.C hb₂)
  have ha₂ : a₂ ∈ V := by
    have hkey : a₂ =
        (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 2
          - (lowStage2 H₂ a₃ a₄ a₅ b₀ b₁).coeff 2 := by
      rw [low_pivot_a2 hH₂m hH₂d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hlow 2) (hStage₂ 2)
  have hStage₁ : CoeffsIn V
      (lowStage1 H₂ a₂ a₃ a₄ a₅ b₀ b₁ b₂) := by
    rw [lowStage1]
    exact hStage₂.add ((CoeffsIn.C ha₂).mul hL₂)
  have hL₁ : CoeffsIn V (lowL1 b₀ : A[X]) := by
    rw [lowL1]
    exact hX.add (CoeffsIn.C hb₀)
  have ha₁ : a₁ ∈ V := by
    have hkey : a₁ =
        (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 1
          - (lowStage1 H₂ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 1 := by
      rw [low_pivot_a1 hH₂m hH₂d]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hlow 1) (hStage₁ 1)
  have hStage₀ : CoeffsIn V
      (lowStage0 H₂ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂) := by
    rw [lowStage0]
    exact hStage₁.add ((CoeffsIn.C ha₁).mul hL₁)
  have ha₀ : a₀ ∈ V := by
    have hkey : a₀ =
        (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 0
          - (lowStage0 H₂ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff 0 := by
      rw [low_pivot_a0]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hlow 0) (hStage₀ 0)
  exact ⟨ha₅, ha₄, ha₃, ha₂, ha₁, ha₀⟩

/-! ## Internal remainder descent -/

/-- After the nine high parameters are known, the weighted remainder rows
decode the internal `T_{k,8}` block through the affine triangular transport.
The reconstructed `T` outputs then expose the exact low residual. -/
theorem internal_and_low_mem [Nontrivial A] {V : Subalgebra R A}
    {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℕ → A)
    (w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R))
    (hH₂V : ∀ j, H₂.coeff j ∈ V) (hH₄V : ∀ j, H₄.coeff j ∈ V)
    (hw : w ∈ V) (hu : u ∈ V) (hv : v ∈ V) (hrho : rho ∈ V)
    (hb₀ : b₀ ∈ V) (hb₁ : b₁ ∈ V) (hb₂ : b₂ ∈ V)
    (hb₃ : b₃ ∈ V) (hb₄ : b₄ ∈ V)
    (hQ : ∀ j, (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
      b₀ b₁ b₂ b₃ b₄).coeff j ∈ V) :
    (∀ t, t < (k - 1) * 8 → beta t ∈ V) ∧
      (∀ j, (lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂).coeff j ∈ V) := by
  let H₈ := H8 H₂ H₄ u v w
  let Ht := H₈ + C rho
  let Hp := tower H₂ H₄ H₈
  let RR := Rpair Hp Ht k 3 beta
  let S := Tpair Hp Ht k 3 beta
  let L₁ : A[X] := (H₂ + C b₁) * (H₄ + C b₃)
  let L₂ : A[X] := (H₂ + C b₂) * (H₄ + C b₄)
  let A₇ : A[X] := (X + C b₀) * L₁
  let F := lowCore H₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂
  have h2R : IsUnit (2 : R) := by
    simpa only [Int.cast_natCast] using hadm 2 (by omega) (by omega)
  have hX : CoeffsIn V (X : A[X]) := CoeffsIn.X V
  have hH₂c : CoeffsIn V H₂ := hH₂V
  have hH₄c : CoeffsIn V H₄ := hH₄V
  have hH₈c : CoeffsIn V H₈ := by
    simp only [H₈, H8]
    exact ((hH₄c.add (hX.add (CoeffsIn.C hu))).mul
      (hH₄c.add (hH₂c.add (CoeffsIn.C hv)))).add (CoeffsIn.C hw)
  have hHtc : CoeffsIn V Ht := by
    simp only [Ht]
    exact hH₈c.add (CoeffsIn.C hrho)
  obtain ⟨hH₈m, hH₈d⟩ := H8_good hH₂m hH₂d hH₄m hH₄d u v w
  obtain ⟨hHtm, hHtd⟩ := add_C_good hH₈m hH₈d rho (by omega)
  have hTower0 := tower_good hH₂m hH₂d hH₄m hH₄d hH₈m hH₈d
  have hTower : ∀ i, 1 ≤ i → i ≤ 3 →
      (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧ (∀ j, (Hp i).coeff j ∈ V) := by
    intro i hi h3
    have hi' : i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases hi' with rfl | rfl | rfl
    · obtain ⟨hm, hd⟩ := hTower0 1 (by omega) (by omega)
      simpa only [Hp, tower_one] using And.intro hm (And.intro hd hH₂V)
    · obtain ⟨hm, hd⟩ := hTower0 2 (by omega) (by omega)
      simpa only [Hp, tower_two] using And.intro hm (And.intro hd hH₄V)
    · obtain ⟨hm, hd⟩ := hTower0 3 (by omega) (by omega)
      simpa only [Hp, tower_three] using And.intro hm (And.intro hd hH₈c)
  obtain ⟨hH₂b₁m, hH₂b₁d⟩ := add_C_good hH₂m hH₂d b₁ (by omega)
  obtain ⟨hH₂b₂m, hH₂b₂d⟩ := add_C_good hH₂m hH₂d b₂ (by omega)
  obtain ⟨hH₄b₃m, hH₄b₃d⟩ := add_C_good hH₄m hH₄d b₃ (by omega)
  obtain ⟨hH₄b₄m, hH₄b₄d⟩ := add_C_good hH₄m hH₄d b₄ (by omega)
  have hL₁m : L₁.Monic := by
    simp only [L₁]
    exact hH₂b₁m.mul hH₄b₃m
  have hL₁d : L₁.natDegree = 6 := by
    simp only [L₁]
    rw [hH₂b₁m.natDegree_mul hH₄b₃m, hH₂b₁d, hH₄b₃d]
  have hL₂m : L₂.Monic := by
    simp only [L₂]
    exact hH₂b₂m.mul hH₄b₄m
  have hL₂d : L₂.natDegree = 6 := by
    simp only [L₂]
    rw [hH₂b₂m.natDegree_mul hH₄b₄m, hH₂b₂d, hH₄b₄d]
  have hL₁c : CoeffsIn V L₁ := by
    simp only [L₁]
    exact (hH₂c.add (CoeffsIn.C hb₁)).mul (hH₄c.add (CoeffsIn.C hb₃))
  have hL₂c : CoeffsIn V L₂ := by
    simp only [L₂]
    exact (hH₂c.add (CoeffsIn.C hb₂)).mul (hH₄c.add (CoeffsIn.C hb₄))
  have hA₇c : CoeffsIn V A₇ := by
    simp only [A₇]
    exact (hX.add (CoeffsIn.C hb₀)).mul hL₁c
  have hmainc : CoeffsIn V (A₇ * H₈ ^ k + L₂ * Ht ^ k) :=
    (hA₇c.mul (hH₈c.pow k)).add (hL₂c.mul (hHtc.pow k))
  obtain ⟨hFm, hFd⟩ := lowCore_good hH₂m hH₂d
    a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂
  have hFmF : F.Monic := by simpa only [F] using hFm
  have hFdF : F.natDegree = 6 := by simpa only [F] using hFd
  obtain ⟨hS₁eq, hS₂eq⟩ := Tpair_eq_pow_add_R
    (Hp := Hp) (Ht := Ht) (k := k) (l := 3) (α := beta)
  have hQdecomp :
      barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ =
        A₇ * S.1 + L₂ * S.2 + F := by
    simp only [barQ, H₈, Ht, Hp, S]
    rw [outer_eq_crowns_add_low]
    simp only [A₇, L₁, L₂, F, crownA, crownB]
    ring
  have hQinternal :
      barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ =
        (A₇ * H₈ ^ k + L₂ * Ht ^ k) + (A₇ * RR.1 + L₂ * RR.2) + F := by
    rw [hQdecomp, hS₁eq, hS₂eq]
    simp only [Hp, tower_three, RR]
    ring
  have hFhigh : ∀ j, j < (k - 1) * 8 → F.coeff (6 + j) ∈ V := by
    intro j hj
    rcases eq_or_ne j 0 with rfl | hj0
    · simp only [Nat.add_zero]
      rw [← hFdF, hFmF.coeff_natDegree]
      exact Subalgebra.one_mem _
    · have hz : F.coeff (6 + j) = 0 := coeff_eq_zero_of_natDegree_lt (by
        rw [hFdF]
        omega)
      rw [hz]
      exact Subalgebra.zero_mem _
  have hweighted : ∀ j, j < (k - 1) * 8 →
      (A₇ * RR.1 + L₂ * RR.2).coeff (6 + j) ∈ V := by
    intro j hj
    have hrow := congrArg (fun P : A[X] => P.coeff (6 + j)) hQinternal
    change (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
      b₀ b₁ b₂ b₃ b₄).coeff (6 + j) =
        ((A₇ * H₈ ^ k + L₂ * Ht ^ k) + (A₇ * RR.1 + L₂ * RR.2) + F).coeff
          (6 + j) at hrow
    have hkey : (A₇ * RR.1 + L₂ * RR.2).coeff (6 + j) =
        (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
          b₀ b₁ b₂ b₃ b₄).coeff (6 + j)
          - (A₇ * H₈ ^ k + L₂ * Ht ^ k).coeff (6 + j) - F.coeff (6 + j) := by
      simp only [coeff_add] at hrow ⊢
      rw [hrow]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (hQ (6 + j)) (hmainc (6 + j)))
      (hFhigh j hj)
  have hcert := Rk2l_triangular k (by omega) 3 Hp Ht beta V (by omega)
    hTower hHtm hHtd hHtc (by intro h; omega) hadm
  have hrows : ∀ j, j < (k - 1) * 8 →
      (((X + C b₀) * L₁) * RR.1 + L₂ * RR.2).coeff (6 + j) ∈ V := by
    intro j hj
    simpa only [A₇, mul_assoc] using hweighted j hj
  have hslots : ∀ j, j < (k - 1) * 8 → rSlot k 3 beta (A := A) j ∈ V :=
    hcert.param_mem_of_affine_monic_shift (hd := 6) (by omega)
      hL₁m hL₁d hL₂m hL₂d hL₁c hL₂c hb₀ le_rfl hrows
  have hbeta : ∀ t, t < (k - 1) * 8 → beta t ∈ V :=
    rSlot_param_mem h2R k (by omega) 3 Hp beta (by omega) hTower hslots
  have hR₁c : CoeffsIn V RR.1 := by
    intro j
    refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) (hcert.supp₁ j)
    rintro _ ⟨r, hr, rfl⟩
    exact hslots r hr.2
  have hR₂c : CoeffsIn V RR.2 := by
    intro j
    refine SetLike.le_def.1 (sup_le le_rfl (adjoin_le ?_)) (hcert.supp₂ j)
    rintro _ ⟨r, hr, rfl⟩
    exact hslots r hr.2
  have hS₁c : CoeffsIn V S.1 := by
    rw [hS₁eq]
    exact (hH₈c.pow k).add hR₁c
  have hS₂c : CoeffsIn V S.2 := by
    rw [hS₂eq]
    exact (hHtc.pow k).add hR₂c
  have hhighc : CoeffsIn V (A₇ * S.1 + L₂ * S.2) :=
    (hA₇c.mul hS₁c).add (hL₂c.mul hS₂c)
  have hlow : CoeffsIn V F := by
    intro j
    have hrow := congrArg (fun P : A[X] => P.coeff j) hQdecomp
    change (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
      b₀ b₁ b₂ b₃ b₄).coeff j = (A₇ * S.1 + L₂ * S.2 + F).coeff j at hrow
    have hkey : F.coeff j =
        (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
          b₀ b₁ b₂ b₃ b₄).coeff j - (A₇ * S.1 + L₂ * S.2).coeff j := by
      rw [hrow, coeff_add]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hQ j) (hhighc j)
  exact ⟨hbeta, by simpa only [F] using hlow⟩

/-- The exact reflected outer circuit agrees with `jTopLinear` through row seven
whenever its two degree-`8k` inputs have the `T_{k,8}` top jets. -/
theorem jOuter_top_linear {H₂ H₄ jS₁ jS₂ : A[X]} {N k : ℕ}
    (hN : 8 ≤ N)
    (hS₁ : JetEq 8 jS₁ (jH8LinearPower H₂ H₄ k u v))
    (hS₂ : JetEq 8 jS₂ (jH8LinearPower H₂ H₄ k u v))
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    JetEq 8
      (jOuter N H₂ H₄ jS₁ jS₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄)
      (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄) := by
  let F₃ := jH4 H₄ + C b₃ * X ^ 4
  let F₄ := jH4 H₄ + C b₄ * X ^ 4
  let P₁ := jH2 H₂ + C b₁ * X ^ 2
  let P₂ := jH2 H₂ + C b₂ * X ^ 2
  let L := jH8LinearPower H₂ H₄ k u v
  have hUprod : JetEq 8 (F₃ * jS₁) (F₃ * L) := (JetEq.refl 8 F₃).mul hS₁
  have hUlow : JetEq 8 (X ^ (N + 1) * jQ3 H₂ a₃ a₄ a₅) 0 :=
    JetEq.zero_X_pow_mul_of_le (by omega) _
  have hU : JetEq 8 (jU0 N H₂ H₄ jS₁ a₃ a₄ a₅ b₃) (F₃ * L) := by
    simpa [jU0, F₃] using hUprod.add hUlow
  have hVprod : JetEq 8 (F₄ * jS₂) (F₄ * L) := (JetEq.refl 8 F₄).mul hS₂
  have hVlow : JetEq 8 (C a₂ * X ^ (N + 4)) 0 := by
    rw [mul_comm]
    exact JetEq.zero_X_pow_mul_of_le (by omega) _
  have hV : JetEq 8 (jV0 N H₄ jS₂ a₂ b₄) (F₄ * L) := by
    simpa [jV0, F₄] using hVprod.add hVlow
  have hC1prod : JetEq 8 (P₁ * jU0 N H₂ H₄ jS₁ a₃ a₄ a₅ b₃)
      (P₁ * (F₃ * L)) := (JetEq.refl 8 P₁).mul hU
  have hC1low : JetEq 8 (C a₁ * X ^ (N + 6)) 0 := by
    rw [mul_comm]
    exact JetEq.zero_X_pow_mul_of_le (by omega) _
  have hC1 : JetEq 8 (jC1 N H₂ H₄ jS₁ a₁ a₃ a₄ a₅ b₁ b₃)
      (P₁ * (F₃ * L)) := by
    simpa [jC1, P₁] using hC1prod.add hC1low
  have hC2prod : JetEq 8 (P₂ * jV0 N H₄ jS₂ a₂ b₄)
      (P₂ * (F₄ * L)) := (JetEq.refl 8 P₂).mul hV
  have hC2low : JetEq 8 (C a₀ * X ^ (N + 6)) 0 := by
    rw [mul_comm]
    exact JetEq.zero_X_pow_mul_of_le (by omega) _
  have hC2 : JetEq 8 (jC2 N H₂ H₄ jS₂ a₀ a₂ b₂ b₄)
      (P₂ * (F₄ * L)) := by
    simpa [jC2, P₂] using hC2prod.add hC2low
  have hleft := (JetEq.refl 8 (1 + C b₀ * X)).mul hC1
  have hright := (JetEq.refl 8 X).mul hC2
  have heq : (1 + C b₀ * X) * (P₁ * (F₃ * L)) + X * (P₂ * (F₄ * L))
      = jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄ := by
    simp only [jTopLinear, jP1, jP2, P₁, P₂, F₃, F₄, L]
    ring
  exact (by simpa only [jOuter] using (hleft.add hright).trans (JetEq.of_eq heq))

private theorem degree_C_le (z : A) (d : ℕ) : (C z).natDegree ≤ d := by
  rw [natDegree_C]
  omega

private theorem degree_add_le {P Q : A[X]} {d : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) : (P + Q).natDegree ≤ d :=
  le_trans (natDegree_add_le _ _) (max_le hP hQ)

private theorem degree_mul_le {P Q : A[X]} {d e : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ e) : (P * Q).natDegree ≤ d + e :=
  le_trans natDegree_mul_le (Nat.add_le_add hP hQ)

private theorem reflect_X_one : (X : A[X]).reflect 1 = 1 := reflect_one_X

/-- Reversal at infinity is exact for the whole outer crown. -/
theorem outer_reflect {H₂ H₄ S₁ S₂ : A[X]} {N : ℕ}
    (hH₂d : H₂.natDegree = 2) (hH₄d : H₄.natDegree = 4)
    (hS₁d : S₁.natDegree = N) (hS₂d : S₂.natDegree = N) (hN : 3 ≤ N)
    (a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    (outer H₂ H₄ S₁ S₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄).reflect (N + 7)
      = jOuter N H₂ H₄ (S₁.reflect N) (S₂.reflect N)
          a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ := by
  have hH₂ : H₂.natDegree ≤ 2 := hH₂d.le
  have hH₄ : H₄.natDegree ≤ 4 := hH₄d.le
  have hS₁ : S₁.natDegree ≤ N := hS₁d.le
  have hS₂ : S₂.natDegree ≤ N := hS₂d.le
  have hXa₅ : (X + C a₅ : A[X]).natDegree ≤ 1 :=
    degree_add_le natDegree_X_le (degree_C_le _ _)
  have hH₂a₄ : (H₂ + C a₄).natDegree ≤ 2 := degree_add_le hH₂ (degree_C_le _ _)
  have hQ3 : (Q3 H₂ a₃ a₄ a₅).natDegree ≤ 3 := by
    rw [Q3]
    exact degree_add_le (degree_mul_le hXa₅ hH₂a₄) (degree_C_le _ _)
  have hH₄b₃ : (H₄ + C b₃).natDegree ≤ 4 := degree_add_le hH₄ (degree_C_le _ _)
  have hH₄b₄ : (H₄ + C b₄).natDegree ≤ 4 := degree_add_le hH₄ (degree_C_le _ _)
  have hU : (U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃).natDegree ≤ N + 4 := by
    rw [U0]
    exact degree_add_le (by simpa [Nat.add_comm] using degree_mul_le hH₄b₃ hS₁)
      (le_trans hQ3 (by omega))
  have hV : (V0 H₄ S₂ a₂ b₄).natDegree ≤ N + 4 := by
    rw [V0]
    exact degree_add_le (by simpa [Nat.add_comm] using degree_mul_le hH₄b₄ hS₂)
      (degree_C_le _ _)
  have hH₂b₁ : (H₂ + C b₁).natDegree ≤ 2 := degree_add_le hH₂ (degree_C_le _ _)
  have hH₂b₂ : (H₂ + C b₂).natDegree ≤ 2 := degree_add_le hH₂ (degree_C_le _ _)
  have hC1 : (C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃).natDegree ≤ N + 6 := by
    rw [C1]
    exact degree_add_le (le_trans (degree_mul_le hH₂b₁ hU) (by omega))
      (degree_C_le _ _)
  have hC2 : (C2 H₂ H₄ S₂ a₀ a₂ b₂ b₄).natDegree ≤ N + 6 := by
    rw [C2]
    exact degree_add_le (le_trans (degree_mul_le hH₂b₂ hV) (by omega))
      (degree_C_le _ _)
  have hXb₀ : (X + C b₀ : A[X]).natDegree ≤ 1 :=
    degree_add_le natDegree_X_le (degree_C_le _ _)
  have hH₂4 : H₂.reflect 4 = jH2 H₂ * X ^ 2 := by
    rw [reflect_pad H₂ hH₂ (by omega), jH2]
  have hQ3r : (Q3 H₂ a₃ a₄ a₅).reflect 3 = jQ3 H₂ a₃ a₄ a₅ := by
    rw [Q3, reflect_add, reflect_mul _ _ hXa₅ hH₂a₄]
    simp only [reflect_add, reflect_C, reflect_X_one, jQ3]
    rw [show H₂.reflect 2 = jH2 H₂ from rfl, pow_one]
  have hUr : (U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃).reflect (N + 4)
      = jU0 N H₂ H₄ (S₁.reflect N) a₃ a₄ a₅ b₃ := by
    rw [U0, reflect_add,
      show (H₄ + C b₃) * S₁ = S₁ * (H₄ + C b₃) by ring,
      reflect_mul _ _ hS₁ hH₄b₃,
      reflect_pad (Q3 H₂ a₃ a₄ a₅) hQ3 (by omega), hQ3r]
    simp only [reflect_add, jH4, reflect_C, jU0]
    rw [show N + 4 - 3 = N + 1 by omega]
    ring
  have hVr : (V0 H₄ S₂ a₂ b₄).reflect (N + 4)
      = jV0 N H₄ (S₂.reflect N) a₂ b₄ := by
    rw [V0, reflect_add,
      show (H₄ + C b₄) * S₂ = S₂ * (H₄ + C b₄) by ring,
      reflect_mul _ _ hS₂ hH₄b₄]
    simp only [reflect_add, jH4, reflect_C, jV0]
    ring
  have hC1r : (C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃).reflect (N + 6)
      = jC1 N H₂ H₄ (S₁.reflect N) a₁ a₃ a₄ a₅ b₁ b₃ := by
    rw [C1, reflect_add,
      show (H₂ + C b₁) * U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃
        = U0 H₂ H₄ S₁ a₃ a₄ a₅ b₃ * (H₂ + C b₁) by ring,
      reflect_mul _ _ hU hH₂b₁]
    simp only [reflect_add, jH2, reflect_C, hUr, jC1]
    ring
  have hC2r : (C2 H₂ H₄ S₂ a₀ a₂ b₂ b₄).reflect (N + 6)
      = jC2 N H₂ H₄ (S₂.reflect N) a₀ a₂ b₂ b₄ := by
    rw [C2, reflect_add,
      show (H₂ + C b₂) * V0 H₄ S₂ a₂ b₄
        = V0 H₄ S₂ a₂ b₄ * (H₂ + C b₂) by ring,
      reflect_mul _ _ hV hH₂b₂]
    simp only [reflect_add, jH2, reflect_C, hVr, jC2]
    ring
  rw [outer, reflect_add,
    show (X + C b₀) * C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃
      = C1 H₂ H₄ S₁ a₁ a₃ a₄ a₅ b₁ b₃ * (X + C b₀) by ring,
    reflect_mul _ _ hC1 hXb₀,
    reflect_pad (C2 H₂ H₄ S₂ a₀ a₂ b₂ b₄) hC2 (by omega)]
  simp only [reflect_add, reflect_C, reflect_X_one, hC1r, hC2r, jOuter]
  rw [show N + 7 - (N + 6) = 1 by omega, pow_one]
  ring

/-- The actual barred circuit has the explicit affine top-eight model. -/
theorem barQ_reflect_top_linear [Nontrivial A] {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (beta : ℕ → A)
    (w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    JetEq 8
      ((barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
        b₀ b₁ b₂ b₃ b₄).reflect (k * 8 + 7))
      (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄) := by
  let H₈ := H8 H₂ H₄ u v w
  let S := Tpair (tower H₂ H₄ H₈) (H₈ + C rho) k 3 beta
  have hT := T_good hH₂m hH₂d hH₄m hH₄d k hk beta u v w rho
  have href := outer_reflect hH₂d hH₄d hT.1.2 hT.2.2 (by omega)
    a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  have htop := T_reflect_top_eight hH₂m hH₂d hH₄m hH₄d
    k hk beta u v w rho
  have hS₁ : JetEq 8 (S.1.reflect (k * 8)) (jH8LinearPower H₂ H₄ k u v) :=
    htop.1.trans (jH8_pow_linear_mod_eight H₂ H₄ k hk u v w)
  have hS₂ : JetEq 8 (S.2.reflect (k * 8)) (jH8LinearPower H₂ H₄ k u v) :=
    htop.2.trans (jH8_shift_pow_linear_mod_eight H₂ H₄ k hk u v w rho)
  have hj := jOuter_top_linear (N := k * 8) (k := k) (u := u) (v := v)
    (by omega) hS₁ hS₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  have href' :
      (outer H₂ H₄ S.1 S.2 a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄).reflect
          (k * 8 + 7)
        = jOuter (k * 8) H₂ H₄ (S.1.reflect (k * 8)) (S.2.reflect (k * 8))
            a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ := by
    simpa only [H₈, S, Nat.mul_comm] using href
  rw [show barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
      = outer H₂ H₄ S.1 S.2 a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ from by
        simp only [barQ, H₈, S], href']
  exact hj

/-- Rows eight and nine of the actual barred circuit have the explicit affine
model used by the `w,rho` decoder, including the two reflected remainder
boundaries. -/
theorem barQ_reflect_mid_linear [Nontrivial A] {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℕ → A)
    (w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A) :
    let H₈ := H8 H₂ H₄ u v w
    let Ht := H₈ + C rho
    let Hp := tower H₂ H₄ H₈
    let RR := Rpair Hp Ht k 3 beta
    JetEq 10
      ((barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
        b₀ b₁ b₂ b₃ b₄).reflect (k * 8 + 7))
      (jMidLinear H₂ H₄ k
        (RR.1.reflect ((k - 1) * 8)) (RR.2.reflect ((k - 1) * 8))
        w rho u v b₀ b₁ b₂ b₃ b₄) := by
  dsimp only
  let H₈ := H8 H₂ H₄ u v w
  let Ht := H₈ + C rho
  let Hp := tower H₂ H₄ H₈
  let S := Tpair Hp Ht k 3 beta
  let RR := Rpair Hp Ht k 3 beta
  have hT := T_good hH₂m hH₂d hH₄m hH₄d k (by omega) beta u v w rho
  have href := outer_reflect hH₂d hH₄d hT.1.2 hT.2.2 (by omega)
    a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  have hsplit := T_reflect_split hH₂m hH₂d hH₄m hH₄d
    k (by omega) beta u v w rho
  have hmain := jOuter_main_mod_ten (N := k * 8) (by omega)
    H₂ H₄ (S.1.reflect (k * 8)) (S.2.reflect (k * 8))
    a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  have hsplit₁ : S.1.reflect (k * 8) = (jH8 H₂ H₄ u v w) ^ k
      + RR.1.reflect ((k - 1) * 8) * X ^ 8 := by
    simpa only [H₈, Ht, Hp, S, RR] using hsplit.1
  have hsplit₂ : S.2.reflect (k * 8) =
      (jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k
        + RR.2.reflect ((k - 1) * 8) * X ^ 8 := by
    simpa only [H₈, Ht, Hp, S, RR] using hsplit.2
  have hmain' : JetEq 10
      (jOuter (k * 8) H₂ H₄ (S.1.reflect (k * 8)) (S.2.reflect (k * 8))
        a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄)
      (jG1 H₂ H₄ b₀ b₁ b₃ *
          ((jH8 H₂ H₄ u v w) ^ k + RR.1.reflect ((k - 1) * 8) * X ^ 8)
        + jG2 H₂ H₄ b₂ b₄ *
          ((jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k
            + RR.2.reflect ((k - 1) * 8) * X ^ 8)) := by
    have htarget :
        jG1 H₂ H₄ b₀ b₁ b₃ * S.1.reflect (k * 8)
            + jG2 H₂ H₄ b₂ b₄ * S.2.reflect (k * 8)
          = jG1 H₂ H₄ b₀ b₁ b₃ *
              ((jH8 H₂ H₄ u v w) ^ k + RR.1.reflect ((k - 1) * 8) * X ^ 8)
            + jG2 H₂ H₄ b₂ b₄ *
              ((jH8 H₂ H₄ u v w + C rho * X ^ 8) ^ k
                + RR.2.reflect ((k - 1) * 8) * X ^ 8) := by
      rw [hsplit₁, hsplit₂]
    exact hmain.trans (JetEq.of_eq htarget)
  have hlin := jMain_mid_mod_ten H₂ H₄ k (by omega)
    (RR.1.reflect ((k - 1) * 8)) (RR.2.reflect ((k - 1) * 8))
    w rho u v b₀ b₁ b₂ b₃ b₄
  have href' :
      (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄).reflect
          (k * 8 + 7)
        = jOuter (k * 8) H₂ H₄ (S.1.reflect (k * 8)) (S.2.reflect (k * 8))
            a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ := by
    simpa only [barQ, H₈, Ht, Hp, S, Nat.mul_comm] using href
  exact (JetEq.of_eq href').trans (hmain'.trans hlin)

/-! ## Public decoder -/

/-- V-relative decoder for the general barred gadget (`k ≥ 2`).  The proof
order is exactly the manuscript decoder:

`b₀,b₁,b₂ | (b₃,b₄,u,v) | w,rho | beta | a₅,…,a₀`.
-/
theorem recover [Nontrivial A] {V : Subalgebra R A} {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 2 ≤ k) (beta : ℕ → A)
    (w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R))
    (hH₂V : ∀ j, H₂.coeff j ∈ V) (hH₄V : ∀ j, H₄.coeff j ∈ V)
    (hQ : ∀ j, (barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅
      b₀ b₁ b₂ b₃ b₄).coeff j ∈ V) :
    (∀ t, t < (k - 1) * 8 → beta t ∈ V) ∧
      w ∈ V ∧ u ∈ V ∧ v ∈ V ∧ rho ∈ V ∧
      a₀ ∈ V ∧ a₁ ∈ V ∧ a₂ ∈ V ∧ a₃ ∈ V ∧ a₄ ∈ V ∧ a₅ ∈ V ∧
      b₀ ∈ V ∧ b₁ ∈ V ∧ b₂ ∈ V ∧ b₃ ∈ V ∧ b₄ ∈ V := by
  let Q := barQ H₂ H₄ k beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  let H₈ := H8 H₂ H₄ u v w
  let Ht := H₈ + C rho
  let Hp := tower H₂ H₄ H₈
  let RR := Rpair Hp Ht k 3 beta
  let D := (k - 1) * 8
  have hkR : IsUnit (k : R) := by
    simpa only [Int.cast_natCast] using hadm k (by omega) le_rfl
  have hQref : ∀ i, (Q.reflect (k * 8 + 7)).coeff i ∈ V := by
    intro i
    rw [coeff_reflect]
    exact hQ _
  have htop := barQ_reflect_top_linear hH₂m hH₂d hH₄m hH₄d
    k (by omega) beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  have htopobs : ∀ i, i < 8 →
      (jTopLinear H₂ H₄ k u v b₀ b₁ b₂ b₃ b₄).coeff i ∈ V := by
    intro i hi
    have heq := htop.coeff_eq hi
    rw [← heq]
    simpa only [Q] using hQref i
  obtain ⟨hb₀, hb₁, hb₂, hb₃, hb₄, hu, hv⟩ :=
    top_params_mem hH₂m hH₂d hH₄m hH₄d k (by omega) hkR
      u v b₀ b₁ b₂ b₃ b₄ hH₂V hH₄V htopobs
  obtain ⟨hJR₁₀, hJR₁₁, hJR₂₀, hJR₂₁⟩ :=
    remainder_boundary_mem hH₂m hH₂d hH₄m hH₄d k hk beta u v w rho
      hH₂V hH₄V hu hv
  have hmid := barQ_reflect_mid_linear hH₂m hH₂d hH₄m hH₄d
    k hk beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
  have hmid₈ : (jMidLinear H₂ H₄ k
      (RR.1.reflect D) (RR.2.reflect D) w rho u v b₀ b₁ b₂ b₃ b₄).coeff 8 ∈ V := by
    have heq := hmid.coeff_eq (show 8 < 10 by omega)
    rw [← heq]
    simpa only [Q, H₈, Ht, Hp, RR, D] using hQref 8
  have hmid₉ : (jMidLinear H₂ H₄ k
      (RR.1.reflect D) (RR.2.reflect D) w rho u v b₀ b₁ b₂ b₃ b₄).coeff 9 ∈ V := by
    have heq := hmid.coeff_eq (show 9 < 10 by omega)
    rw [← heq]
    simpa only [Q, H₈, Ht, Hp, RR, D] using hQref 9
  obtain ⟨hw, hrho⟩ := mid_params_mem hH₂m hH₂d hH₄m hH₄d k hkR
    (RR.1.reflect D) (RR.2.reflect D) w rho u v b₀ b₁ b₂ b₃ b₄
    hH₂V hH₄V hb₀ hb₁ hb₂ hb₃ hb₄ hu hv
    (by simpa only [H₈, Ht, Hp, RR, D] using hJR₁₀)
    (by simpa only [H₈, Ht, Hp, RR, D] using hJR₁₁)
    (by simpa only [H₈, Ht, Hp, RR, D] using hJR₂₀)
    (by simpa only [H₈, Ht, Hp, RR, D] using hJR₂₁) hmid₈ hmid₉
  obtain ⟨hbeta, hlow⟩ := internal_and_low_mem hH₂m hH₂d hH₄m hH₄d
    k hk beta w u v rho a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄
    hadm hH₂V hH₄V hw hu hv hrho hb₀ hb₁ hb₂ hb₃ hb₄ hQ
  obtain ⟨ha₅, ha₄, ha₃, ha₂, ha₁, ha₀⟩ :=
    low_params_mem hH₂m hH₂d a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂
      hH₂V hb₀ hb₁ hb₂ hlow
  exact ⟨hbeta, hw, hu, hv, hrho, ha₀, ha₁, ha₂, ha₃, ha₄, ha₅,
    hb₀, hb₁, hb₂, hb₃, hb₄⟩

/-- Consecutive-parameter presentation matching the manuscript: the octic
parameters occupy rows `0,…,3`, the internal block rows `4,…,8k-5`, then the
six low and five scalar crown parameters. -/
noncomputable def gadget (H₂ H₄ : A[X]) (k : ℕ) (theta : ℕ → A) : A[X] :=
  barQ H₂ H₄ k (fun t => theta (4 + t))
    (theta 0) (theta 1) (theta 2) (theta 3)
    (theta (8 * k - 4)) (theta (8 * k - 3)) (theta (8 * k - 2))
    (theta (8 * k - 1)) (theta (8 * k)) (theta (8 * k + 1))
    (theta (8 * k + 2)) (theta (8 * k + 3)) (theta (8 * k + 4))
    (theta (8 * k + 5)) (theta (8 * k + 6))

theorem gadget_good [Nontrivial A] {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 1 ≤ k) (theta : ℕ → A) :
    (gadget H₂ H₄ k theta).Monic ∧ (gadget H₂ H₄ k theta).natDegree = 8 * k + 7 := by
  rw [gadget]
  exact barQ_good hH₂m hH₂d hH₄m hH₄d k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem gadget_recover [Nontrivial A] {V : Subalgebra R A} {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4)
    (k : ℕ) (hk : 2 ≤ k) (theta : ℕ → A)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R))
    (hH₂V : ∀ j, H₂.coeff j ∈ V) (hH₄V : ∀ j, H₄.coeff j ∈ V)
    (hQ : ∀ j, (gadget H₂ H₄ k theta).coeff j ∈ V) :
    ∀ t, t < 8 * k + 7 → theta t ∈ V := by
  have hraw := recover hH₂m hH₂d hH₄m hH₄d k hk (fun t => theta (4 + t))
    (theta 0) (theta 1) (theta 2) (theta 3)
    (theta (8 * k - 4)) (theta (8 * k - 3)) (theta (8 * k - 2))
    (theta (8 * k - 1)) (theta (8 * k)) (theta (8 * k + 1))
    (theta (8 * k + 2)) (theta (8 * k + 3)) (theta (8 * k + 4))
    (theta (8 * k + 5)) (theta (8 * k + 6)) hadm hH₂V hH₄V (by
      simpa only [gadget] using hQ)
  obtain ⟨hbeta, hw, hu, hv, hrho, ha₀, ha₁, ha₂, ha₃, ha₄, ha₅,
    hb₀, hb₁, hb₂, hb₃, hb₄⟩ := hraw
  intro t ht
  rcases Nat.lt_or_ge t 4 with ht4 | h4
  · have hcases : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 := by omega
    rcases hcases with rfl | rfl | rfl | rfl
    · exact hw
    · exact hu
    · exact hv
    · exact hrho
  · rcases Nat.lt_or_ge t (8 * k - 4) with hinner | houter
    · have h := hbeta (t - 4) (by omega)
      simpa only [show 4 + (t - 4) = t by omega] using h
    · have hcases : t = 8 * k - 4 ∨ t = 8 * k - 3 ∨ t = 8 * k - 2 ∨
          t = 8 * k - 1 ∨ t = 8 * k ∨ t = 8 * k + 1 ∨ t = 8 * k + 2 ∨
          t = 8 * k + 3 ∨ t = 8 * k + 4 ∨ t = 8 * k + 5 ∨ t = 8 * k + 6 := by
        omega
      rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ha₀
      · exact ha₁
      · exact ha₂
      · exact ha₃
      · exact ha₄
      · exact ha₅
      · exact hb₀
      · exact hb₁
      · exact hb₂
      · exact hb₃
      · exact hb₄

end BarQGeneral

end FastPoly
