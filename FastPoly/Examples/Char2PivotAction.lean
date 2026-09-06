import FastPoly.Examples.Char2CoefficientAction

/-! A supplied unit action whose explicitly modified coordinates lie in an
interval. Passing it through an earlier coefficient shear removes that
coordinate correction. Once the interval is a singleton the action is
literally a unit-coordinate translation. -/
namespace FastPoly.Char2PivotAction

open Polynomial Char2CoefficientShear Char2CoefficientShearTransport
  Char2CoefficientAction Char2Degree19InnerTail
set_option maxHeartbeats 20000
variable {R : Type*} [CommRing R] [CharP R 2] {n : ℕ}

structure Action (f : (Fin n → R) → R[X]) (lo : ℕ) (p : Fin n) (r : ℕ) where
  shift : (Fin n → R) → R → (Fin n → R)
  unit : ∀ q δ, UnitDifference (f q) (f (shift q δ)) r δ
  before : ∀ q δ k, k.val < lo → shift q δ k = q k
  after : ∀ q δ k, p < k → shift q δ k = q k
  pivot : ∀ q δ, shift q δ p = q p + δ

variable {f : (Fin n → R) → R[X]} {lo r : ℕ} {p : Fin n}

/-- The next action is a conjugate by the displayed self-inverse shear. -/
def Action.normalize (a : Action f lo p r) (j : Fin n) (m : ℕ)
    (hlo : j.val ≤ lo) (hjp : j < p) (hrm : r < m)
    (hj : ∀ q δ, UnitDifference (f q) (f (increment q j δ)) m δ) :
    Action (fun q => f (coordinateShear f j m q)) (j.val + 1) p r where
  shift := lift f j m a.shift
  unit := lift_unit f j m a.shift r a.unit
  before := by
    intro q δ k hk
    have hb : ∀ q δ k, k < j → a.shift q δ k = q k := by
      intro q δ k hk
      exact a.before q δ k (lt_of_lt_of_le hk hlo)
    by_cases hkj : k = j
    · subst k
      exact lift_pivot f j m a.shift hj r hrm a.unit hb q δ
    · exact lift_before f j m a.shift hb q δ k (by omega)
  after := by
    intro q δ k hk
    exact lift_preserves f j m a.shift k (by omega) (fun q δ => a.after q δ k hk) q δ
  pivot := lift_increments f j m a.shift p hjp a.pivot

theorem Action.shift_eq_increment (a : Action f lo p r) (hlo : p.val ≤ lo)
    (q : Fin n → R) (δ : R) : a.shift q δ = increment q p δ := by
  funext k
  change a.shift q δ k = Function.update q p (q p + δ) k
  rcases lt_trichotomy k p with hk | hk | hk
  · rw [Function.update_of_ne (ne_of_lt hk)]
    exact a.before q δ k (lt_of_lt_of_le hk hlo)
  · subst k
    rw [Function.update_self]
    exact a.pivot q δ
  · rw [Function.update_of_ne (ne_of_gt hk)]
    exact a.after q δ k hk

theorem Action.unit_increment (a : Action f lo p r) (hlo : p.val ≤ lo)
    (q : Fin n → R) (δ : R) :
    UnitDifference (f q) (f (increment q p δ)) r δ := by
  rw [← a.shift_eq_increment hlo q δ]
  exact a.unit q δ

end FastPoly.Char2PivotAction
