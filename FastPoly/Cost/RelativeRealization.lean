import FastPoly.Cost.RealizationComposition

/-!
# Circuits relative to a shared producer

Auxiliary odd gadgets in the master induction use the quadratic and quartic returned by
the smaller pair.  `RelativeRealization` records exactly that situation: its circuit is
evaluated after one fixed producer has been bound, and its multiplication count charges
only the new body.  No algebraic or characteristic hypothesis occurs here.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- A single polynomial output computed relative to the outputs of a shared producer. -/
structure RelativeRealization {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {p : ℕ}
    (θ : ℕ → A) (producer : Circuit R PolyInput p) (output : A[X])
    (multiplications : ℕ) where
  circuit : Circuit R (Sum PolyInput (Fin p)) 1
  eval_eq : circuit.eval
      (Sum.elim (polyEnv θ) (producer.eval (polyEnv θ))) 0 = output
  multiplication_count : circuit.gates.multiplications = multiplications

end FastPoly.Cost
