/-
The characteristic-two lower bound (`sections/lower_char2.md`): the exceptional case
`n = 1`, which shows the theorem is sharp and its model non-vacuous.
-/
import FastPoly.LowerBoundChar2.Main

/-!
# `n = 1` really is a construction

The write-up closes with: *"The case `n = 1` is exceptional and does exist:
`f_{a,b}(x) = a x + b` uses one multiplication and is bijective on evaluations at any two
distinct points."*  This file proves that inside the very same model.

The circuit is `G₁ = (0·x + u₁)(1·x + v₁)`, `f = 0·x + 1·G₁ + w`, with the parameter map
`(a₀, a₁) ↦ (u₁, v₁, w) = (a₀, 0, a₁)`, so `f_a(x) = a₀ x + a₁` (`oneGate_family`).
Evaluation at two distinct points is then the invertible map
`(a₀, a₁) ↦ (a₀x₀ + a₁, a₀x₁ + a₁)` (`oneGate_isConstruction`).

Two consequences worth recording:

* **`no_construction` is sharp**: its hypothesis `1 < n` cannot be relaxed to `0 < n`
  (`exists_isConstruction_one`).
* **the model is not vacuous**: `IsConstruction` is satisfiable, so the impossibility for
  `n > 1` is not an artefact of a definition that no circuit could meet.

Nothing in this file uses characteristic `2` — the `n = 1` construction exists over every
finite field.
-/

namespace FastPoly.LowerBoundChar2

variable {F : Type*} [Field F]

/-- The one-gate circuit `G₁ = (0·x + u₁)(1·x + v₁)`, `f = G₁ + w`. -/
def oneGate (F : Type*) [Field F] : Circuit F 1 where
  α := fun _ => 0
  β := fun _ => 1
  p := fun _ _ => 0
  q := fun _ _ => 0
  γ := 0
  r := fun _ => 1

/-- The parameter map `a ↦ (u₁, v₁, w) = (a₀, 0, a₁)`. -/
def oneGateParams (F : Type*) [Field F] : ParamMap F 1 where
  cu := fun _ k => if k = 0 then 1 else 0
  du := fun _ => 0
  cv := fun _ _ => 0
  dv := fun _ => 0
  cw := fun k => if k = 1 then 1 else 0
  dw := 0

@[simp] theorem oneGate_alpha : (oneGate F).α 0 = 0 := rfl
@[simp] theorem oneGate_beta : (oneGate F).β 0 = 1 := rfl
@[simp] theorem oneGate_gamma : (oneGate F).γ = 0 := rfl
@[simp] theorem oneGate_rr : (oneGate F).r 0 = 1 := rfl

theorem oneGateParams_U (a : Fin (2 * 1) → F) : (oneGateParams F).slots a (U 0) = a 0 := by
  simp [ParamMap.slots, oneGateParams]

theorem oneGateParams_V (a : Fin (2 * 1) → F) : (oneGateParams F).slots a (V 0) = 0 := by
  simp [ParamMap.slots, oneGateParams]

theorem oneGateParams_W (a : Fin (2 * 1) → F) :
    (oneGateParams F).slots a (W : SlotIdx 1) = a 1 := by
  simp [ParamMap.slots, oneGateParams]

/-- The one-gate family is `f_a(x) = a₀ x + a₁`. -/
theorem oneGate_family (a : Fin (2 * 1) → F) (x : F) :
    family (oneGate F) (oneGateParams F) a x = a 0 * x + a 1 := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  rw [family, eval, Fin.sum_univ_one, gate_zero, oneGateParams_U, oneGateParams_V,
    oneGateParams_W, oneGate_alpha, oneGate_beta, oneGate_gamma, oneGate_rr]
  ring

/-- **`f_{a,b}(x) = a x + b` is a `(2, 1)` construction.**  Evaluation at any two distinct
points is a bijection `F² → F²`, because the `2 × 2` matrix `[[x₀, 1], [x₁, 1]]` has
determinant `x₀ - x₁ ≠ 0`. -/
theorem oneGate_isConstruction [Fintype F] :
    IsConstruction (oneGate F) (oneGateParams F) := by
  intro X hX
  rw [← Finite.injective_iff_bijective]
  intro a a' hEq
  have hx : X 0 ≠ X 1 := fun hh => (by decide : (0 : Fin (2 * 1)) ≠ 1) (hX hh)
  have e0 : family (oneGate F) (oneGateParams F) a (X 0)
      = family (oneGate F) (oneGateParams F) a' (X 0) := congrFun hEq 0
  have e1 : family (oneGate F) (oneGateParams F) a (X 1)
      = family (oneGate F) (oneGateParams F) a' (X 1) := congrFun hEq 1
  rw [oneGate_family, oneGate_family] at e0 e1
  have ha0 : a 0 = a' 0 := by
    have hsub : (a 0 - a' 0) * (X 0 - X 1) = 0 := by linear_combination e0 - e1
    rcases mul_eq_zero.mp hsub with hh | hh
    · exact sub_eq_zero.mp hh
    · exact absurd (sub_eq_zero.mp hh) hx
  have ha1 : a 1 = a' 1 := by linear_combination e0 - X 0 * ha0
  funext k
  have hk : k.val = 0 ∨ k.val = 1 := by have := k.isLt; omega
  rcases hk with h | h
  · have : k = 0 := Fin.val_injective (by simpa using h)
    rw [this]; exact ha0
  · have : k = 1 := Fin.val_injective (by simpa using h)
    rw [this]; exact ha1

/-- **The hypothesis `1 < n` of `no_construction` is necessary.**  For `n = 1` there *is* a
circuit and a parameter map whose evaluation at every two distinct points is a bijection —
so the model is also non-vacuous: `IsConstruction` is satisfiable. -/
theorem exists_isConstruction_one [Fintype F] :
    ∃ (c : Circuit F 1) (P : ParamMap F 1), IsConstruction c P :=
  ⟨oneGate F, oneGateParams F, oneGate_isConstruction⟩

end FastPoly.LowerBoundChar2
