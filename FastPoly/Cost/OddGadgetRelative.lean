import FastPoly.Cost.OddGadgetCircuit
import FastPoly.Cost.RelativeRealization

/-!
# Wiring an odd gadget to a realized source pair

The auxiliary gadgets in the odd induction are compiled over `ConstructionInput`:
their quadratic and quartic are symbolic input wires, and their fresh parameters start
at zero.  This file supplies the characteristic-independent adapter which connects
those wires to outputs two and three of one `JointPairRealization` and shifts the local
parameter block into the global parameter supply.

The extra bound constant is the zero wire used for deliberately irrelevant
`ConstructionInput.source` labels.  It carries no arithmetic cost.  Consequently the
result is a `RelativeRealization` over the *literal circuit* of the source pair, which
is exactly the sharing invariant required by the two outer induction combinators.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace OddGadget

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Relabel a local odd-gadget input after binding a zero wire.  The left environment
contains the free polynomial inputs and the four outputs of the source realization;
the right environment contains only the new zero wire. -/
def relativeLabel (offset : ℕ) :
    ConstructionInput → Sum (Sum PolyInput (Fin 4)) (Fin 1)
  | .variable => .inl (.inl .variable)
  | .power i => if i = 1 then .inl (.inr 2) else .inl (.inr 3)
  | .shiftedPower => .inl (.inr 3)
  | .parameter i => .inl (.inl (.parameter (offset + i)))
  | .source _ => .inr 0

/-- The local gadget circuit wired to one realized source, without duplicating the
source circuit. -/
def relativeCircuit {q : ℕ}
    (gadget : Circuit R ConstructionInput q) (offset : ℕ) :
    Circuit R (Sum PolyInput (Fin 4)) q :=
  .bind (.const 0) (gadget.relabel (relativeLabel offset))

@[simp] theorem relativeCircuit_multiplications
    {q : ℕ} (gadget : Circuit R ConstructionInput q) (offset : ℕ) :
    (relativeCircuit gadget offset).gates.multiplications =
      gadget.gates.multiplications := by
  simp only [relativeCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.gates, GateCount.add_multiplications, GateCount.zero_multiplications,
    Nat.zero_add]

/-- Wiring a local gadget to a realized source preserves its canonical-environment
depth bound, provided the recorded quadratic and quartic sit at depths one and two. -/
theorem multDepth_relativeCircuit_le {q : ℕ}
    (gadget : Circuit R ConstructionInput q) (offset : ℕ)
    (dsrc : Fin 4 → ℕ) (h2 : dsrc 2 ≤ 1) (h4 : dsrc 3 ≤ 2) (j : Fin q) :
    (relativeCircuit (R := R) gadget offset).multDepth
        (Sum.elim (fun _ : PolyInput => 0) dsrc) j
      ≤ gadget.multDepth Height.gadgetDepthEnv j := by
  rw [relativeCircuit, Circuit.multDepth_bind, Circuit.multDepth_relabel]
  refine Circuit.multDepth_mono _ ?_ j
  intro input
  cases input with
  | «variable» => exact le_rfl
  | power i =>
      by_cases hi : i = 1
      · subst hi; simpa [relativeLabel] using h2
      · simpa [relativeLabel, hi, Height.gadgetDp] using h4
  | shiftedPower => simpa [relativeLabel] using h4
  | parameter i => exact le_rfl
  | source i => simp [relativeLabel]

/-- The environment seen immediately after binding the four outputs of a realized
source pair. -/
noncomputable def sourceEnv
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM : ℕ}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM) :
    Sum PolyInput (Fin 4) → A[X] :=
  Sum.elim (polyEnv θ) (source.circuit.eval (polyEnv θ))

/-- Extend `sourceEnv` by the cost-free zero wire used for irrelevant local source
labels. -/
noncomputable def zeroExtendedEnv
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM : ℕ}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM) :
    Sum (Sum PolyInput (Fin 4)) (Fin 1) → A[X] :=
  Sum.elim (sourceEnv source)
    ((.const 0 : Circuit R (Sum PolyInput (Fin 4)) 1).eval (sourceEnv source))

/-- Semantic content of `relativeLabel`: it presents precisely the local gadget
environment with the source's recorded quadratic and quartic and a shifted parameter
block. -/
theorem zeroExtendedEnv_comp_relativeLabel
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM : ℕ}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (offset : ℕ) :
    zeroExtendedEnv source ∘ relativeLabel offset =
      env H₂ H₄ (fun i => θ (offset + i)) := by
  funext input
  cases input with
  | «variable» => rfl
  | power i =>
      by_cases hi : i = 1
      · subst i
        simp only [zeroExtendedEnv, relativeLabel, if_pos, Function.comp_apply,
          Sum.elim_inl, sourceEnv, Sum.elim_inr, env, constructionEnv_power,
          suppliedPowers_one, source.evalH₂]
      · simp only [zeroExtendedEnv, relativeLabel, hi, if_false, Function.comp_apply,
          Sum.elim_inl, sourceEnv, Sum.elim_inr, env, constructionEnv_power,
          suppliedPowers, source.evalH₄]
  | shiftedPower =>
      simp only [zeroExtendedEnv, relativeLabel, Function.comp_apply, Sum.elim_inl,
        sourceEnv, Sum.elim_inr, env, constructionEnv_shiftedPower, source.evalH₄]
  | parameter i => rfl
  | source i =>
      change algebraMap R A[X] 0 = 0
      exact map_zero (algebraMap R A[X])

/-- Every local odd-gadget realization becomes a realization relative to the exact
circuit which produced its quadratic and quartic inputs.  No characteristic or
invertibility assumption is introduced by this wiring step. -/
def Realization.relative
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ Q : A[X]} {sourceM localM : ℕ}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (offset : ℕ)
    (gadget : Realization (R := R) H₂ H₄ (fun i => θ (offset + i)) Q localM) :
    RelativeRealization (R := R) θ source.circuit Q localM where
  circuit := relativeCircuit gadget.circuit offset
  eval_eq := by
    rw [relativeCircuit, Circuit.eval_bind, Circuit.eval_relabel]
    change gadget.circuit.eval
        (zeroExtendedEnv source ∘ relativeLabel offset) 0 = Q
    rw [zeroExtendedEnv_comp_relativeLabel, gadget.eval_eq]
  multiplication_count := by
    rw [relativeCircuit_multiplications, gadget.multiplication_count]

end OddGadget

end FastPoly.Cost
