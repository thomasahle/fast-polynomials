import FastPoly.Cost.OddGadgetCrownBundleOptimized

/-!
# Literal addition count of the barred odd gadget

The barred circuit already binds every shared column.  This file records its exact
fixed additions and joins them to the level-three `tAdd` theorem, proving the
selected ledger for the very circuit carried by `barredRealized`.
-/

namespace FastPoly.Cost.OddGadget

universe u

namespace BarredAdditions

variable {R : Type u} [CommRing R]

omit [CommRing R] in
@[simp] theorem powerPair_additions :
    (barredPowerPair (R := R)).gates.additions = 6 := by
  simp only [barredPowerPair, Circuit.gates_bind,
    Circuit.gates, GateCount.add_additions, GateCount.zero_additions,
    GateCount.adds_additions, GateCount.muls_additions,
    Circuit.gates_liftLeft, Circuit.gates_rightInput,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]

omit [CommRing R] in
@[simp] theorem outer_additions (k : ℕ) :
    (barredOuter (R := R) k).gates.additions = 13 := by
  rfl

/-- Exact additions of the same circuit used by `barredRealized`. -/
theorem circuit_additions (k : ℕ) :
    (barredCircuit (R := R) k).gates.additions = tAdd k 3 + 19 := by
  have hT := tCircuitF_additions_eq_tAdd_of_three_le
    (R := R) k k 3 le_rfl (by omega)
  have hT' : (tCircuit (R := R) k 3).gates.additions = tAdd k 3 := by
    simpa only [tCircuit] using hT
  simp only [barredCircuit, barredTCircuit, Circuit.gates_bind,
    Circuit.gates_relabel, GateCount.add_additions,
    powerPair_additions, outer_additions]
  rw [hT']
  omega

end BarredAdditions

end FastPoly.Cost.OddGadget
