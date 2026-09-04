import Mathlib.Data.Nat.Basic

/-!
# Arithmetic gate counts

The neutral gate-count record shared by the numerical schedules and the semantic
circuit language. Multiplication by a fixed scalar is free; `multiplications` counts
only products of two computed ring values.
-/

namespace FastPoly.Cost

/-- Top-level additions/subtractions and nonscalar multiplications. -/
@[ext]
structure GateCount where
  additions : ℕ
  multiplications : ℕ
deriving DecidableEq, Repr

instance : Zero GateCount := ⟨⟨0, 0⟩⟩

instance : Add GateCount where
  add a b := ⟨a.additions + b.additions, a.multiplications + b.multiplications⟩

/-- Charge `n` additions and no multiplications. -/
def GateCount.adds (n : ℕ) : GateCount := ⟨n, 0⟩

/-- Charge `n` nonscalar multiplications and no additions. -/
def GateCount.muls (n : ℕ) : GateCount := ⟨0, n⟩

/-- Charge both kinds of gate at once. -/
def GateCount.of (a m : ℕ) : GateCount := ⟨a, m⟩

@[simp] theorem GateCount.zero_additions : (0 : GateCount).additions = 0 := rfl
@[simp] theorem GateCount.zero_multiplications : (0 : GateCount).multiplications = 0 := rfl
@[simp] theorem GateCount.add_additions (a b : GateCount) :
    (a + b).additions = a.additions + b.additions := rfl
@[simp] theorem GateCount.add_multiplications (a b : GateCount) :
    (a + b).multiplications = a.multiplications + b.multiplications := rfl
@[simp] theorem GateCount.adds_additions (n : ℕ) : (GateCount.adds n).additions = n := rfl
@[simp] theorem GateCount.adds_multiplications (n : ℕ) :
    (GateCount.adds n).multiplications = 0 := rfl
@[simp] theorem GateCount.muls_additions (n : ℕ) :
    (GateCount.muls n).additions = 0 := rfl
@[simp] theorem GateCount.muls_multiplications (n : ℕ) :
    (GateCount.muls n).multiplications = n := rfl
@[simp] theorem GateCount.of_additions (a m : ℕ) : (GateCount.of a m).additions = a := rfl
@[simp] theorem GateCount.of_multiplications (a m : ℕ) :
    (GateCount.of a m).multiplications = m := rfl

end FastPoly.Cost
