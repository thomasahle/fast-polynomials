import FastPoly.Cost.Instantiate
import FastPoly.Cost.RetainedShiftTCompiler

/-!
# Instantiating the retained-shift `T` compiler

This is the call-site seam for the optimized shared bases.  A construction wiring is
extended by designating one existing wire as the retained scalar shift; no arithmetic
gate is introduced.  The semantic theorem below keeps the surrounding producer
abstract, so Crown, odd-gadget, and finite-base realizations use the same adapter.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- Replace source component zero by an already available wire.  Component one is
preserved for clients which use the source pair for another purpose. -/
def ConstructionWiring.withRetainedShift {m : ℕ} (w : ConstructionWiring m)
    (rho : Sum PolyInput (Fin m)) : ConstructionWiring m where
  power := w.power
  shiftedPower := w.shiftedPower
  parameter := w.parameter
  source i := if i = 0 then rho else w.source i

@[simp] theorem ConstructionWiring.withRetainedShift_power {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) :
    (w.withRetainedShift rho).power = w.power := rfl

@[simp] theorem ConstructionWiring.withRetainedShift_shiftedPower {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) :
    (w.withRetainedShift rho).shiftedPower = w.shiftedPower := rfl

@[simp] theorem ConstructionWiring.withRetainedShift_parameter {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) :
    (w.withRetainedShift rho).parameter = w.parameter := rfl

@[simp] theorem ConstructionWiring.withRetainedShift_source_zero {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) :
    (w.withRetainedShift rho).source 0 = rho := by
  simp only [ConstructionWiring.withRetainedShift, if_pos]

@[simp] theorem ConstructionWiring.withRetainedShift_source_one {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) :
    (w.withRetainedShift rho).source 1 = w.source 1 := by
  simp only [ConstructionWiring.withRetainedShift,
    if_neg (by omega : (1 : Fin 2) ≠ 0)]

@[simp] theorem ConstructionWiring.withRetainedShift_powerValues
    {A : Type v} [CommRing A] {m : ℕ} (w : ConstructionWiring m)
    (rho : Sum PolyInput (Fin m)) (theta : ℕ → A) (values : Fin m → A[X]) :
    (w.withRetainedShift rho).powerValues theta values =
      w.powerValues theta values := rfl

@[simp] theorem ConstructionWiring.withRetainedShift_shiftedValue
    {A : Type v} [CommRing A] {m : ℕ} (w : ConstructionWiring m)
    (rho : Sum PolyInput (Fin m)) (theta : ℕ → A) (values : Fin m → A[X]) :
    (w.withRetainedShift rho).shiftedValue theta values =
      w.shiftedValue theta values := rfl

@[simp] theorem ConstructionWiring.withRetainedShift_sourceValue_zero
    {A : Type v} [CommRing A] {m : ℕ} (w : ConstructionWiring m)
    (rho : Sum PolyInput (Fin m)) (theta : ℕ → A) (values : Fin m → A[X]) :
    (w.withRetainedShift rho).sourceValues theta values 0 =
      Sum.elim (polyEnv theta) values rho := by
  rw [ConstructionWiring.sourceValues,
    ConstructionWiring.withRetainedShift_source_zero]

namespace Circuit

/-- Instantiate the retained-shift compiler after designating its scalar side wire. -/
def instantiateRetainedT {R : Type u} [CommRing R] {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) (k l : ℕ) :
    Circuit R (Sum PolyInput (Fin m)) 2 :=
  (RetainedShiftT.compiler k l).instantiateConstruction
    (w.withRetainedShift rho)

@[simp] theorem gates_instantiateRetainedT {R : Type u} [CommRing R] {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) (k l : ℕ) :
    (instantiateRetainedT (R := R) w rho k l).gates =
      (RetainedShiftT.compiler (R := R) k l).gates := by
  rw [instantiateRetainedT, Circuit.gates_instantiateConstruction]

/-- Instantiation does not change the retained compiler's multiplication count. -/
theorem instantiateRetainedT_multiplications {R : Type u} [CommRing R] {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) (k l : ℕ) :
    (instantiateRetainedT (R := R) w rho k l).gates.multiplications =
      (tCircuit (R := R) k l).gates.multiplications := by
  rw [gates_instantiateRetainedT,
    RetainedShiftT.compiler_multiplications]

/-- Exact number of additions saved after call-site instantiation. -/
theorem instantiateRetainedT_additions {R : Type u} [CommRing R] {m : ℕ}
    (w : ConstructionWiring m) (rho : Sum PolyInput (Fin m)) (k l : ℕ) :
    (instantiateRetainedT (R := R) w rho k l).gates.additions +
        RetainedShiftT.savings k l =
      (tCircuit (R := R) k l).gates.additions := by
  rw [gates_instantiateRetainedT, RetainedShiftT.compiler_additions]

section Semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Replacing the ordinary call by its retained-shift compiler preserves the complete
local pair.  The retained input is one of the surrounding producer's existing wires. -/
theorem eval_instantiateRetainedT_eq {m : ℕ} (w : ConstructionWiring m)
    (rho : Sum PolyInput (Fin m)) (theta : ℕ → A) (values : Fin m → A[X])
    (k l : ℕ) (hvalid : ValidTCall k l)
    (hshift : w.shiftedValue theta values =
      w.powerValues theta values l + Sum.elim (polyEnv theta) values rho) :
    (instantiateRetainedT (R := R) w rho k l).eval
        (Sum.elim (polyEnv theta) values) =
      ((tCircuit (R := R) k l).instantiateConstruction
        (w.withRetainedShift rho)).eval (Sum.elim (polyEnv theta) values) := by
  rw [instantiateRetainedT, Circuit.eval_instantiateConstruction,
    Circuit.eval_instantiateConstruction]
  apply RetainedShiftT.eval_compiler_eq k l _ hvalid
  simpa only [ConstructionWiring.withRetainedShift_powerValues,
    ConstructionWiring.withRetainedShift_shiftedValue,
    ConstructionWiring.withRetainedShift_sourceValue_zero] using hshift

end Semantics

end Circuit

end FastPoly.Cost
