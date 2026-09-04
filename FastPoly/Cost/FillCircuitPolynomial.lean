import FastPoly.Cost.FillCircuit
import FastPoly.Section4.FillRec

/-!
# Polynomial semantics of the generic fill compiler

This small adapter is the only place where the characteristic-independent circuit fill
is identified with the paper's `FillData`/`fillChain` definitions. Keeping the adapter
separate lets future construction families reuse `Cost.FillCircuit` without importing
the present Section-4 recursion.
-/

namespace FastPoly.Cost

open Polynomial

universe v

/-- Convert the paper's scalar fields `b,ah` to the constant-polynomial values used by
the generic circuit evaluator. -/
noncomputable def FillValues.ofPolynomialData {A : Type v} [CommRing A]
    (d : FastPoly.FillData A) : FillValues A[X] :=
  { q := d.q
    qh := d.qh
    b := C d.b
    ah := C d.ah }

@[simp] theorem fillStepValue_ofPolynomialData {A : Type v} [CommRing A]
    (H : A[X]) (d : FastPoly.FillData A) (source : A[X] × A[X]) :
    fillStepValue H (FillValues.ofPolynomialData d) source =
      FastPoly.fillStep H d source :=
  rfl

/-- The generic value-level chain specializes exactly to the paper's polynomial chain. -/
theorem fillChainValue_ofPolynomialData {A : Type v} [CommRing A]
    (H : ℕ → A[X]) (D : ℕ → FastPoly.FillData A) :
    ∀ l source,
      fillChainValue H (fun i => FillValues.ofPolynomialData (D i)) l source =
        FastPoly.fillChain H D l source := by
  intro l
  induction l with
  | zero => intro source; rfl
  | succ l ih =>
      intro source
      rcases l with _ | l
      · rfl
      · change fillChainValue H (fun i => FillValues.ofPolynomialData (D i)) (l + 1)
            (fillStepValue (H (l + 2)) (FillValues.ofPolynomialData (D (l + 2))) source) = _
        rw [fillStepValue_ofPolynomialData, ih]
        rfl

end FastPoly.Cost
