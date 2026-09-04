import FastPoly.Cost.OddGadgetBundle

/-!
# Wiring an odd gadget after a two-output bundle

The sequential `8k+3` branch first produces `(S₂,H₄')`, then evaluates `S₃` from the
source quadratic and the new quartic `H₄'`.  These definitions express that dataflow
directly, while still binding each producer exactly once.
-/

namespace FastPoly.Cost.OddGadget

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private abbrev BundleInput := Sum (Sum PolyInput (Fin 4)) (Fin 2)

/-- Environment after the source pair and a two-output relative bundle have both been
bound. -/
noncomputable def bundleEnv
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM bundleM : ℕ}
    {output : Fin 2 → A[X]}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (bundle : MultiplicationRealization (R := R) (sourceEnv source) output bundleM) :
    BundleInput → A[X] :=
  Sum.elim (sourceEnv source) (bundle.circuit.eval (sourceEnv source))

/-- The input wiring for a gadget which consumes the source quadratic and output one
of the preceding bundle as its quartic. -/
def afterBundleLabel (offset : ℕ) :
    ConstructionInput → Sum BundleInput (Fin 1)
  | .variable => .inl (.inl (.inl .variable))
  | .power i => if i = 1 then .inl (.inl (.inr 2)) else .inl (.inr 1)
  | .shiftedPower => .inl (.inr 1)
  | .parameter i => .inl (.inl (.inl (.parameter (offset + i))))
  | .source _ => .inr 0

/-- Bind the cost-free zero wire required by the local source-label convention. -/
def afterBundleCircuit (gadget : Circuit R ConstructionInput 1) (offset : ℕ) :
    Circuit R BundleInput 1 :=
  .bind (.const 0) (gadget.relabel (afterBundleLabel offset))

@[simp] theorem afterBundleCircuit_multiplications
    (gadget : Circuit R ConstructionInput 1) (offset : ℕ) :
    (afterBundleCircuit gadget offset).gates.multiplications =
      gadget.gates.multiplications := by
  simp only [afterBundleCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.gates, GateCount.add_multiplications, GateCount.zero_multiplications,
    Nat.zero_add]

/-- Depth bound for a gadget consuming the source quadratic and the bundle's
retained quartic: the canonical-environment bound survives the wiring. -/
theorem multDepth_afterBundleCircuit_le
    (gadget : Circuit R ConstructionInput 1) (offset : ℕ)
    (dsrc : Fin 4 → ℕ) (dbun : Fin 2 → ℕ)
    (h2 : dsrc 2 ≤ 1) (h4 : dbun 1 ≤ 2) :
    (afterBundleCircuit (R := R) gadget offset).multDepth
        (Sum.elim (Sum.elim (fun _ : PolyInput => 0) dsrc) dbun) 0
      ≤ gadget.multDepth Height.gadgetDepthEnv 0 := by
  rw [afterBundleCircuit, Circuit.multDepth_bind, Circuit.multDepth_relabel]
  refine Circuit.multDepth_mono _ ?_ 0
  intro input
  cases input with
  | «variable» => exact le_rfl
  | power i =>
      by_cases hi : i = 1
      · subst hi; simpa [afterBundleLabel] using h2
      · simpa [afterBundleLabel, hi, Height.gadgetDp] using h4
  | shiftedPower => simpa [afterBundleLabel] using h4
  | parameter i => exact le_rfl
  | source i => simp [afterBundleLabel]

private noncomputable def zeroExtendedBundleEnv
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM bundleM : ℕ}
    {output : Fin 2 → A[X]}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (bundle : MultiplicationRealization (R := R) (sourceEnv source) output bundleM) :
    Sum BundleInput (Fin 1) → A[X] :=
  Sum.elim (bundleEnv source bundle)
    ((.const 0 : Circuit R BundleInput 1).eval (bundleEnv source bundle))

private theorem zeroExtendedBundleEnv_comp_label
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM bundleM offset : ℕ}
    {output : Fin 2 → A[X]}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (bundle : MultiplicationRealization (R := R) (sourceEnv source) output bundleM) :
    zeroExtendedBundleEnv source bundle ∘ afterBundleLabel offset =
      env H₂ (output 1) (fun i => θ (offset + i)) := by
  funext input
  cases input with
  | «variable» => rfl
  | power i =>
      by_cases hi : i = 1
      · subst i
        simp only [zeroExtendedBundleEnv, afterBundleLabel, if_pos,
          Function.comp_apply, Sum.elim_inl, bundleEnv, sourceEnv, Sum.elim_inr,
          env, constructionEnv_power, suppliedPowers, source.evalH₂]
      · simp only [zeroExtendedBundleEnv, afterBundleLabel, hi, if_false,
          Function.comp_apply, Sum.elim_inl, bundleEnv, Sum.elim_inr,
          MultiplicationRealization.eval_at, env, constructionEnv_power,
          suppliedPowers]
  | shiftedPower =>
      simp only [zeroExtendedBundleEnv, afterBundleLabel, Function.comp_apply,
        Sum.elim_inl, bundleEnv, Sum.elim_inr, MultiplicationRealization.eval_at,
        env, constructionEnv_shiftedPower]
  | parameter i => rfl
  | source i =>
      change algebraMap R A[X] 0 = 0
      exact map_zero (algebraMap R A[X])

namespace Realization

/-- Evaluate a one-output local odd gadget after a shared two-output bundle. -/
def afterBundle
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ Q : A[X]}
    {sourceM bundleM localM offset : ℕ} {output : Fin 2 → A[X]}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (bundle : MultiplicationRealization (R := R) (sourceEnv source) output bundleM)
    (gadget : Realization (R := R) H₂ (output 1)
      (fun i => θ (offset + i)) Q localM) :
    MultiplicationRealization (R := R) (bundleEnv source bundle)
      (fun _ : Fin 1 => Q) localM where
  circuit := afterBundleCircuit gadget.circuit offset
  eval_eq := by
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    rw [afterBundleCircuit, Circuit.eval_bind, Circuit.eval_relabel]
    change gadget.circuit.eval
      (zeroExtendedBundleEnv source bundle ∘ afterBundleLabel offset) 0 = Q
    rw [zeroExtendedBundleEnv_comp_label, gadget.eval_eq]
  multiplication_count := by
    rw [afterBundleCircuit_multiplications, gadget.multiplication_count]

end Realization

end FastPoly.Cost.OddGadget
