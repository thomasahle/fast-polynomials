import FastPoly.Cost.OddGadgetAfterBundle
import FastPoly.Cost.RealizedOddGadgetOptimized

/-!
# Addition counts through relative odd-gadget wiring

Relative gadget adapters bind one zero wire and relabel the local circuit.  Neither
operation adds arithmetic gates.  The equations below expose that fact at the generic
circuit layer and at each semantic wrapper used by the two recursive pair branches.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace OddGadget

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Binding the relative adapter's zero wire preserves every local addition. -/
@[simp] theorem relativeCircuit_additions {q : ℕ}
    (gadget : Circuit R ConstructionInput q) (offset : ℕ) :
    (relativeCircuit gadget offset).gates.additions = gadget.gates.additions := by
  simp only [relativeCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.gates, GateCount.add_additions, GateCount.zero_additions,
    Nat.zero_add]

/-- Binding the after-bundle adapter's zero wire preserves every local addition. -/
@[simp] theorem afterBundleCircuit_additions
    (gadget : Circuit R ConstructionInput 1) (offset : ℕ) :
    (afterBundleCircuit gadget offset).gates.additions = gadget.gates.additions := by
  simp only [afterBundleCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.gates, GateCount.add_additions, GateCount.zero_additions,
    Nat.zero_add]

namespace BundleRealization

/-- A relative multi-output bundle inherits the exact local addition equality. -/
theorem relative_additions
    {q additions : ℕ} {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]}
    {sourceM localM offset : ℕ} {output : Fin q → A[X]}
    (source : JointPairRealization (R := R) theta T₁ T₂ H₂ H₄ sourceM)
    (gadget : BundleRealization (R := R) H₂ H₄
      (fun i => theta (offset + i)) output localM)
    (hadd : gadget.circuit.gates.additions = additions) :
    (relative source gadget).circuit.gates.additions = additions := by
  change (relativeCircuit gadget.circuit offset).gates.additions = additions
  rw [relativeCircuit_additions, hadd]

end BundleRealization

namespace Realization

/-- A gadget evaluated after a retained bundle inherits the exact local addition
equality. -/
theorem afterBundle_additions
    {additions : ℕ} {theta : ℕ → A} {T₁ T₂ H₂ H₄ Q : A[X]}
    {sourceM bundleM localM offset : ℕ} {output : Fin 2 → A[X]}
    (source : JointPairRealization (R := R) theta T₁ T₂ H₂ H₄ sourceM)
    (bundle : MultiplicationRealization (R := R) (sourceEnv source) output bundleM)
    (gadget : Realization (R := R) H₂ (output 1)
      (fun i => theta (offset + i)) Q localM)
    (hadd : gadget.circuit.gates.additions = additions) :
    (afterBundle source bundle gadget).circuit.gates.additions = additions := by
  change (afterBundleCircuit gadget.circuit offset).gates.additions = additions
  rw [afterBundleCircuit_additions, hadd]

end Realization

end OddGadget

namespace AdditionRealizedOddGadget

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

omit [Nontrivial A] in
/-- Converting an addition-certified gadget to the ordinary decoder package and
wiring it relative to a source preserves its certified additions. -/
theorem relative_additions
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM offset d additions : ℕ}
    (source : JointPairRealization (R := R) theta T₁ T₂ H₂ H₄ sourceM)
    (gadget : AdditionRealizedOddGadget (R := R) H₂ H₄
      (fun i => theta (offset + i)) d additions) :
    (RealizedOddGadget.relative source gadget.toRealized).circuit.gates.additions =
      additions := by
  change (OddGadget.relativeCircuit gadget.realization.circuit offset).gates.additions =
    additions
  rw [OddGadget.relativeCircuit_additions, gadget.addition_count]

omit [Nontrivial A] in
/-- Evaluating an addition-certified gadget after a retained bundle preserves its
certified additions. -/
theorem afterBundle_additions
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM bundleM offset d additions : ℕ}
    {output : Fin 2 → A[X]}
    (source : JointPairRealization (R := R) theta T₁ T₂ H₂ H₄ sourceM)
    (bundle : MultiplicationRealization (R := R)
      (OddGadget.sourceEnv source) output bundleM)
    (gadget : AdditionRealizedOddGadget (R := R) H₂ (output 1)
      (fun i => theta (offset + i)) d additions) :
    (OddGadget.Realization.afterBundle source bundle
      gadget.realization).circuit.gates.additions = additions :=
  OddGadget.Realization.afterBundle_additions source bundle gadget.realization
    gadget.addition_count

end AdditionRealizedOddGadget

end FastPoly.Cost
