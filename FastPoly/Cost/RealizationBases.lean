import FastPoly.Cost.PolynomialCircuit
import FastPoly.Height.Depth

/-!
# Semantic circuit certificates for the realized-pair bases

Each theorem in this file identifies the outputs of one explicit shared circuit. The
degree-three certificate is the smallest test of the master invariant: its quadratic is
computed once and reused as the first component, inside the second component, and as the
recorded `H₂` byproduct.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace Three

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The shared quadratic used by the degree-three pair. -/
noncomputable def H₂ (θ : ℕ → A) : A[X] :=
  (X + C (θ 2)) * X + C (θ 1)

/-- First component of the degree-three pair. -/
noncomputable def T₁ (θ : ℕ → A) : A[X] := H₂ θ

/-- Second component of the degree-three pair. -/
noncomputable def T₂ (θ : ℕ → A) : A[X] := H₂ θ + C (θ 0)

/-- The one-product shared circuit. -/
def circuit : Circuit R PolyInput 4 :=
  let q : Circuit R PolyInput 1 :=
    .add (.mul (.add Circuit.polyX (Circuit.polyParameter 2)) Circuit.polyX)
      (Circuit.polyParameter 1)
  .bind q <|
    .fork
      (.fork (Circuit.rightInput (ι := PolyInput) (0 : Fin 1))
        (.add (Circuit.rightInput (ι := PolyInput) (0 : Fin 1))
          (Circuit.polyParameter 0).liftLeft))
      (.fork (Circuit.rightInput (ι := PolyInput) (0 : Fin 1)) (.const 0))

/-- The single product of the degree-three circuit. -/
theorem circuit_multiplications :
    (circuit (R := R)).gates.multiplications = 1 := rfl

/-- Every output of the degree-three circuit sits at height at most one. -/
theorem multDepth_circuit_le :
    ((circuit (R := R)).multDepth (fun _ => 0) 0 ≤ 1) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 1 ≤ 1) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 3 ≤ 0) := by
  have hm : ∀ j, (circuit (R := R)).multDepth (fun _ => 0) j ≤ 1 := by
    intro j
    have h := Circuit.multDepth_le_multiplications (circuit (R := R))
      (env := fun _ => 0) (d := 0) (fun _ => le_rfl) j
    rwa [circuit_multiplications, Nat.add_zero] at h
  refine ⟨hm 0, hm 1, hm 2, ?_⟩
  rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
  simp only [circuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
    Fin.addCases_right, Circuit.multDepth_const]
  omega

/-- The degree-three pair and its byproducts are jointly realized with exactly one
nonscalar multiplication. -/
def realized (θ : ℕ → A) :
    JointPairRealization (R := R) θ (T₁ θ) (T₂ θ) (H₂ θ) 0 1 where
  circuit := circuit
  eval₁ := by
    rfl
  eval₂ := by
    rfl
  evalH₂ := by
    rfl
  evalH₄ := by
    change algebraMap R A[X] 0 = 0
    exact map_zero (algebraMap R A[X])
  multiplication_count := circuit_multiplications

/-- Proposition-valued form used by the master construction theorem. -/
theorem realizable (θ : ℕ → A) :
    JointPairRealizable (R := R) θ (T₁ θ) (T₂ θ) (H₂ θ) 0 1 :=
  ⟨realized θ⟩

end Three

end FastPoly.Cost
