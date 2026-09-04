import FastPoly.Cost.RetainedShiftTInstantiate

/-!
# Semantic endpoint for instantiated retained-shift `T` circuits

`RetainedShiftTInstantiate` proves that the optimized compiler agrees with the
ordinary `tCircuit` under the same call-site wiring.  The ordinary circuit's public
source-irrelevance theorem then identifies that value with the mathematical `Tpair`.
This module packages the two facts into the direct endpoint needed by realization
constructors; the retained source wire is selected without introducing a gate.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace Circuit

section Semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- An instantiated retained-shift compiler evaluates to the mathematical `Tpair`.

The hypothesis names the already-produced scalar difference carried in `rho`.  The
source component is irrelevant to the ordinary `T` semantics, so the conclusion has
exactly the same parameter and power environments as an ordinary call. -/
theorem eval_instantiateRetainedT_eq_Tpair {m : ℕ} (w : ConstructionWiring m)
    (rho : Sum PolyInput (Fin m)) (theta : ℕ → A) (values : Fin m → A[X])
    (k l : ℕ) (hvalid : ValidTCall k l)
    (hshift : w.shiftedValue theta values =
      w.powerValues theta values l + Sum.elim (polyEnv theta) values rho) :
    ((instantiateRetainedT (R := R) w rho k l).eval
        (Sum.elim (polyEnv theta) values) 0,
      (instantiateRetainedT (R := R) w rho k l).eval
        (Sum.elim (polyEnv theta) values) 1) =
      FastPoly.Tpair (w.powerValues theta values) (w.shiftedValue theta values)
        k l (fun i => theta (w.parameter i)) := by
  calc
    _ = (((tCircuit (R := R) k l).instantiateConstruction
          (w.withRetainedShift rho)).eval (Sum.elim (polyEnv theta) values) 0,
        ((tCircuit (R := R) k l).instantiateConstruction
          (w.withRetainedShift rho)).eval (Sum.elim (polyEnv theta) values) 1) :=
      congrArg (fun output => (output 0, output 1))
        (eval_instantiateRetainedT_eq w rho theta values k l hvalid hshift)
    _ = ((tCircuit (R := R) k l).eval
          (constructionEnv
            ((w.withRetainedShift rho).powerValues theta values)
            ((w.withRetainedShift rho).shiftedValue theta values)
            (fun i => theta ((w.withRetainedShift rho).parameter i))
            ((w.withRetainedShift rho).sourceValues theta values)) 0,
        (tCircuit (R := R) k l).eval
          (constructionEnv
            ((w.withRetainedShift rho).powerValues theta values)
            ((w.withRetainedShift rho).shiftedValue theta values)
            (fun i => theta ((w.withRetainedShift rho).parameter i))
            ((w.withRetainedShift rho).sourceValues theta values)) 1) :=
      congrArg (fun output => (output 0, output 1))
        (eval_instantiateConstruction (w.withRetainedShift rho)
          (tCircuit (R := R) k l) theta values)
    _ = _ := by
      simpa only [ConstructionWiring.withRetainedShift_powerValues,
        ConstructionWiring.withRetainedShift_shiftedValue,
        ConstructionWiring.withRetainedShift_parameter] using
        (eval_tCircuit_with_source (R := R)
          ((w.withRetainedShift rho).powerValues theta values)
          ((w.withRetainedShift rho).shiftedValue theta values)
          (fun i => theta ((w.withRetainedShift rho).parameter i))
          ((w.withRetainedShift rho).sourceValues theta values) k l)

end Semantics

end Circuit

end FastPoly.Cost
