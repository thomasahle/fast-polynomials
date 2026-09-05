import FastPoly.Section4.FillRec
import FastPoly.Section5.FourKPlusOne

/-!
# Special cases: degree 3

`lem:base-three-compatible`: the pair `T⁽¹⁾ = H₂ = (x+α₂)x + α₁`, `T⁽²⁾ = H₂ + α₀` is a
compatible splittable pair for `3` — compatible on `rng 3` with no auxiliary data, with
the explicit decoder `α₂ = Φ₂ - 1`, `α₁ = Φ₁ - α₂`, `α₀ = Φ₀ - α₁`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

section baseThree

variable {K : Subalgebra R A} (a₀ a₁ a₂ : A)

private lemma bt_c0 : (((X + C a₂) * X + C a₁ : A[X])).coeff 0 = a₁ :=
  crownH2_coeff_zero (b := a₂) (c := a₁)

private lemma bt_c1 : (((X + C a₂) * X + C a₁ : A[X])).coeff 1 = a₂ :=
  crownH2_coeff_one (b := a₂) (c := a₁)

private lemma bt_c2 : (((X + C a₂) * X + C a₁ : A[X])).coeff 2 = 1 :=
  crownH2_coeff_two (b := a₂) (c := a₁)

private lemma bt_monic : (((X + C a₂) * X + C a₁ : A[X])).Monic ∧
    (((X + C a₂) * X + C a₁ : A[X])).natDegree = 2 :=
  crownH2_monic (b := a₂) (c := a₁)

private lemma bt_chigh (j : ℕ) (hj : 3 ≤ j) :
    (((X + C a₂) * X + C a₁ : A[X])).coeff j = 0 :=
  coeff_eq_zero_of_natDegree_lt (by rw [(bt_monic a₁ a₂).2]; omega)

/-- **`lem:base-three-compatible`**: the degree-3 base pair is compatible on `rng 3`
with no auxiliary data. -/
theorem base_three_compatible :
    CompatiblePair K ((X + C a₂) * X + C a₁)
      ((X + C a₂) * X + C a₁ + C a₀) 2 (Finset.range 3) := by
  set T₁ : A[X] := (X + C a₂) * X + C a₁ with hT₁
  set T₂ : A[X] := (X + C a₂) * X + C a₁ + C a₀ with hT₂
  obtain ⟨hm₁, hd₁⟩ := bt_monic (A := A) a₁ a₂
  obtain ⟨hm₂, hd₂⟩ := monic_add_low (e := C a₀) hm₁
    (Or.inr (by rw [natDegree_C, hd₁]; omega))
  set φ := combined T₁ T₂ with hφ
  have hT₂c : ∀ j, T₂.coeff j = T₁.coeff j + (if j = 0 then a₀ else 0) := by
    intro j
    rw [hT₂, coeff_add, coeff_C]
  have hφ0 : φ.coeff 0 = a₁ + a₀ := by
    rw [hφ, coeff_combined_zero, hT₂c, bt_c0, if_pos rfl]
  have hφ1 : φ.coeff 1 = a₁ + a₂ := by
    rw [hφ, show (1:ℕ) = 0 + 1 from rfl, coeff_combined, hT₂c, bt_c0, bt_c1,
      if_neg (by omega), add_zero, add_comm]
  have hφ2 : φ.coeff 2 = a₂ + 1 := by
    rw [hφ, show (2:ℕ) = 1 + 1 from rfl, coeff_combined, hT₂c, bt_c1, bt_c2,
      if_neg (by omega), add_zero]
  refine
    { mem₁ := ?_
      mem₂ := ?_
      monic₁ := hm₁
      monic₂ := hm₂
      natDegree₁ := hd₁
      natDegree₂ := hd₂.trans hd₁
      window := fun i hi => hi }
  · intro j
    match j with
    | 0 =>
      have hkey : T₁.coeff 0 = (φ.coeff 1 - φ.coeff 2) + 1 := by
        rw [bt_c0, hφ1, hφ2]
        ring
      rw [hkey]
      exact Subalgebra.add_mem _ (Subalgebra.sub_mem _
        (coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega))
        (coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega)))
        (Subalgebra.one_mem _)
    | 1 =>
      have hkey : T₁.coeff 1 = φ.coeff 2 - 1 := by
        rw [bt_c1, hφ2]
        ring
      rw [hkey]
      exact Subalgebra.sub_mem _
        (coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega))
        (Subalgebra.one_mem _)
    | 2 =>
      have hkey : T₁.coeff 2 = 1 := bt_c2 a₁ a₂
      rw [hkey]
      exact Subalgebra.one_mem _
    | (m + 3) =>
      rw [bt_chigh a₁ a₂ (m + 3) (by omega)]
      exact Subalgebra.zero_mem _
  · intro j
    match j with
    | 0 =>
      have hkey : T₂.coeff 0 = φ.coeff 0 := by
        rw [hT₂c, bt_c0, if_pos rfl, hφ0]
      rw [hkey]
      exact coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega)
    | 1 =>
      have hkey : T₂.coeff 1 = φ.coeff 2 - 1 := by
        rw [hT₂c, bt_c1, if_neg (by omega), add_zero, hφ2]
        ring
      rw [hkey]
      exact Subalgebra.sub_mem _
        (coeff_mem_Vis (Finset.mem_range.2 (by omega)) (by omega))
        (Subalgebra.one_mem _)
    | 2 =>
      have hkey : T₂.coeff 2 = 1 := by
        rw [hT₂c, bt_c2, if_neg (by omega), add_zero]
      rw [hkey]
      exact Subalgebra.one_mem _
    | (m + 3) =>
      have hkey : T₂.coeff (m + 3) = 0 := by
        rw [hT₂c, bt_chigh a₁ a₂ (m + 3) (by omega), if_neg (by omega), add_zero]
      rw [hkey]
      exact Subalgebra.zero_mem _

end baseThree

end FastPoly
