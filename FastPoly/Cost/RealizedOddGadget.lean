import FastPoly.Cost.OddGadgetRelative
import FastPoly.Recover.Context

/-!
# A decoded odd gadget with its actual circuit

`RealizedOddGadget` is the cost-sensitive replacement for an existential decoded
polynomial in the present large-characteristic family.  It packages one explicit
polynomial, its structural facts and conditional decoder, and the circuit which
evaluates to that same polynomial.  The definition itself has no characteristic
assumption, but its fixed quadratic/quartic payload is family-specific.  A future
characteristic-two family should reuse the lower, finite-output
`MultiplicationProgram` / `MultiplicationRealization` interfaces and define its own
thin payload wrapper rather than add exceptional cases here.
-/

namespace FastPoly.Cost

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A degree-`d` auxiliary polynomial which is explicitly decodable given the supplied
quadratic and quartic, and is computed by an actual `d / 2`-product local circuit. -/
structure RealizedOddGadget (H₂ H₄ : A[X]) (θ : ℕ → A) (d : ℕ) where
  Q : A[X]
  monic : Q.Monic
  natDegree : Q.natDegree = d
  recover : ∀ V : Subalgebra R A,
    (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
      (∀ j, Q.coeff j ∈ V) → ∀ t, t < d → θ t ∈ V
  realization : OddGadget.Realization (R := R) H₂ H₄ θ Q (d / 2)

namespace RealizedOddGadget

/-- Wire a realized gadget to the literal circuit of a recursively realized source
pair.  Its decoder fields are unchanged; this operation only supplies the shared
evaluation witness needed by an outer induction step. -/
def relative
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM offset d : ℕ}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (gadget : RealizedOddGadget (R := R) H₂ H₄
      (fun i => θ (offset + i)) d) :
    RelativeRealization (R := R) θ source.circuit gadget.Q (d / 2) :=
  gadget.realization.relative source offset

/-- Height of the wired gadget over the source's output depths: the gadget's own
canonical bound survives the relative wiring. -/
theorem relative_circuit_multDepth_le
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {sourceM offset d : ℕ}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ sourceM)
    (gadget : RealizedOddGadget (R := R) H₂ H₄
      (fun i => θ (offset + i)) d)
    (hd : d % 2 = 1)
    (h2 : source.circuit.multDepth (fun _ => 0) 2 ≤ 1)
    (h4 : source.circuit.multDepth (fun _ => 0) 3 ≤ 2) :
    (RealizedOddGadget.relative source gadget).circuit.multDepth
        (Sum.elim (fun _ : PolyInput => 0)
          (source.circuit.multDepth (fun _ => 0))) 0
      ≤ 2 * Nat.clog 2 d + 1 := by
  have h := (OddGadget.multDepth_relativeCircuit_le _ offset
    (source.circuit.multDepth (fun _ => 0)) h2 h4 0).trans
    gadget.realization.depth_le
  rwa [show 2 * (d / 2) + 1 = d from by omega] at h

end RealizedOddGadget

end FastPoly.Cost
