import FastPoly.Cost.MultiplicationRealization
import FastPoly.Cost.OddGadgetRelative

/-!
# Multi-output local odd-gadget realizations

Some gadgets expose a power byproduct which a later gadget consumes.  This module
extends the existing one-output realization only at that seam: a finite bundle is wired
to one shared source exactly as before, with no extra multiplication gates.
-/

namespace FastPoly.Cost.OddGadget

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A finite bundle produced by one local odd-gadget circuit. -/
abbrev BundleRealization {q : ℕ} (H₂ H₄ : A[X]) (θ : ℕ → A)
    (output : Fin q → A[X]) (multiplications : ℕ) :=
  MultiplicationRealization (R := R) (env H₂ H₄ θ) output multiplications

namespace BundleRealization

/-- Wire a multi-output local realization to the exact circuit of a recursively
realized source pair. -/
def relative
    {q : ℕ} {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM localM offset : ℕ}
    {output : Fin q → A[X]}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (gadget : BundleRealization (R := R) H₂ H₄
      (fun i => θ (offset + i)) output localM) :
    MultiplicationRealization (R := R) (sourceEnv source) output localM where
  circuit := relativeCircuit gadget.circuit offset
  eval_eq := by
    rw [relativeCircuit, Circuit.eval_bind, Circuit.eval_relabel]
    change gadget.circuit.eval
      (zeroExtendedEnv source ∘ relativeLabel offset) = output
    rw [zeroExtendedEnv_comp_relativeLabel, gadget.eval_eq]
  multiplication_count := by
    rw [relativeCircuit_multiplications, gadget.multiplication_count]

end BundleRealization

end FastPoly.Cost.OddGadget
