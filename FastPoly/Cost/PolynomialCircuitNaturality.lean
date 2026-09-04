import FastPoly.Cost.CircuitNaturality
import FastPoly.Cost.PolynomialCircuit
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Specialization of polynomial-input programs

The generic naturality theorem specializes neatly to `PolyInput`: mapping polynomial
coefficients along an `R`-algebra homomorphism sends the symbolic variable to itself and
each parameter wire to the mapped parameter.  Hence a joint program certified once in
a free parameter algebra works, unchanged, after every parameter specialization.
-/

namespace FastPoly.Cost

open Polynomial

universe u v w

/-- The polynomial-input environment commutes with coefficient maps. -/
theorem polyEnv_map {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) (theta : ℕ → A) :
    (fun input => Polynomial.mapAlgHom f (polyEnv theta input)) =
      polyEnv (fun i => f (theta i)) := by
  funext input
  cases input <;>
    simp only [polyEnv_variable, polyEnv_parameter, Polynomial.coe_mapAlgHom,
      Polynomial.map_X, Polynomial.map_C]
  rfl

namespace JointPairProgram

/-- Specialize the semantics of one fixed joint program along a coefficient map.  The
program and its exact gate count are unchanged. -/
theorem RealizesAt.map {R : Type u} {A : Type v} {B : Type w}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {m : ℕ} {program : JointPairProgram R m} {theta : ℕ → A}
    {T₁ T₂ H₂ H₄ : A[X]}
    (h : program.RealizesAt theta T₁ T₂ H₂ H₄) (f : A →ₐ[R] B) :
    program.RealizesAt (fun i => f (theta i))
      (Polynomial.mapAlgHom f T₁) (Polynomial.mapAlgHom f T₂)
      (Polynomial.mapAlgHom f H₂) (Polynomial.mapAlgHom f H₄) := by
  have hnat : ∀ i,
      program.circuit.eval (polyEnv (fun t => f (theta t))) i =
        Polynomial.mapAlgHom f (program.circuit.eval (polyEnv theta) i) := by
    intro i
    rw [← polyEnv_map f theta]
    exact (congrFun
      (Circuit.eval_algHom (Polynomial.mapAlgHom f) program.circuit (polyEnv theta)) i).symm
  exact ⟨(hnat 0).trans (congrArg (Polynomial.mapAlgHom f) h.1),
    (hnat 1).trans (congrArg (Polynomial.mapAlgHom f) h.2.1),
    (hnat 2).trans (congrArg (Polynomial.mapAlgHom f) h.2.2.1),
    (hnat 3).trans (congrArg (Polynomial.mapAlgHom f) h.2.2.2)⟩

end JointPairProgram

end FastPoly.Cost
