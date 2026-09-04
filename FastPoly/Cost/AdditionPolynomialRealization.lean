import FastPoly.Cost.AdditionJointPairEndpoint
import FastPoly.Cost.CubicProgram
import FastPoly.Cost.SepticProgram

/-!
# Same-program addition certificates for complete polynomials

This is the complete-polynomial analogue of `AdditionJointPairRealization`.  One
fixed `PolynomialProgram` carries its pointwise semantics, literal addition count,
and selected `PolynomialAddCost`.  Direct bases, pair completion, and the even lift
all preserve that same-witness invariant.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- A fixed complete-polynomial program with semantics and its exact selected
addition ledger attached to the same circuit. -/
structure AdditionPolynomialRealization (R : Type u) [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A]
    (theta : ℕ → A) (P : A[X]) (degree multiplications additions : ℕ) where
  program : PolynomialProgram R multiplications
  realizesAt : program.RealizesAt theta P
  addition_count : program.additions = additions
  ledger : PolynomialAddCost degree additions

namespace AdditionPolynomialRealization

/-- Direct affine base. -/
def linear {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (theta : ℕ → A) :
    AdditionPolynomialRealization R theta (X + C (theta 0)) 1 0 1 where
  program := PolynomialProgram.linear
  realizesAt := PolynomialProgram.linear_realizesAt theta
  addition_count := PolynomialProgram.additions_linear
  ledger := PolynomialAddCost.linear

/-- Direct quadratic base. -/
def quadratic {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    AdditionPolynomialRealization R theta
      (X * (X + C (theta 1)) + C (theta 0)) 2 1 2 where
  program := PolynomialProgram.quadratic
  realizesAt := PolynomialProgram.quadratic_realizesAt theta
  addition_count := PolynomialProgram.additions_quadratic
  ledger := PolynomialAddCost.quadratic

/-- Direct two-product, three-addition cubic base. -/
def cubic {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    AdditionPolynomialRealization R theta (CubicProgram.value theta) 3 2 3 where
  program := CubicProgram.program
  realizesAt := CubicProgram.realizesAt theta
  addition_count := CubicProgram.additions_program
  ledger := PolynomialAddCost.cubic

/-- Direct optimized four-product, ten-addition septic base. -/
def septic {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    AdditionPolynomialRealization R theta
      (FastPoly.optimizedSeptic
        (theta 0) (theta 1) (theta 2) (theta 3)
        (theta 4) (theta 5) (theta 6)) 7 4 10 where
  program := SepticProgram.program
  realizesAt := SepticProgram.realizesAt theta
  addition_count := SepticProgram.additions_program
  ledger := PolynomialAddCost.septic

/-- Complete an addition-certified realized pair using the exact same pair program.
The final combiner contributes one multiplication and one addition. -/
def ofJointPair {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {degree additions : ℕ}
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄
      degree additions) :
    AdditionPolynomialRealization R theta (X * T₁ + T₂) degree
      (((degree - 1) / 2) + 1) (additions + 1) where
  program := PolynomialProgram.ofJointPair source.certificate.program
  realizesAt := PolynomialProgram.ofJointPair_realizesAt source.realizesAt
  addition_count := by
    rw [PolynomialProgram.additions_ofJointPair]
    change source.certificate.program.circuit.gates.additions + 1 =
      additions + 1
    rw [source.certificate.addition_count]
  ledger := PolynomialAddCost.odd source.certificate.ledger

/-- Lift one complete odd-degree program to the next even degree on the same ambient
parameter environment. -/
def evenLift {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {P : A[X]} {degree multiplications additions : ℕ}
    (source : AdditionPolynomialRealization R theta P degree
      multiplications additions)
    (hodd : degree % 2 = 1) (freshIndex : ℕ) :
    AdditionPolynomialRealization R theta
      (X * P + C (theta freshIndex)) (degree + 1)
      (multiplications + 1) (additions + 1) where
  program := PolynomialProgram.evenLift source.program freshIndex
  realizesAt := PolynomialProgram.evenLift_realizesAt
    source.realizesAt freshIndex
  addition_count := by
    rw [PolynomialProgram.additions_evenLift, source.addition_count]
  ledger := PolynomialAddCost.evenLift source.ledger hodd

/-- Consumer-facing existence of one fixed complete-polynomial program carrying its
semantics, exact addition count, and selected ledger. -/
theorem exists_program {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {P : A[X]} {degree multiplications additions : ℕ}
    (source : AdditionPolynomialRealization R theta P degree
      multiplications additions) :
    ∃ program : PolynomialProgram R multiplications,
      program.RealizesAt theta P ∧ program.additions = additions ∧
        PolynomialAddCost degree additions :=
  ⟨source.program, source.realizesAt, source.addition_count, source.ledger⟩

/-- The sharp complete bound applies to the exact semantic program. -/
theorem program_additions_sharp {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {P : A[X]} {degree multiplications additions : ℕ}
    (source : AdditionPolynomialRealization R theta P degree
      multiplications additions) :
    4 * source.program.additions ≤
      5 * degree + 24 * ceilLog2 degree * ceilLog2 degree + 4 := by
  rw [source.addition_count]
  exact source.ledger.sharp

/-- The uniform complete bound applies to that same program. -/
theorem program_additions_uniform_two {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {P : A[X]} {degree multiplications additions : ℕ}
    (source : AdditionPolynomialRealization R theta P degree
      multiplications additions) :
    source.program.additions ≤ 2 * degree := by
  rw [source.addition_count]
  exact source.ledger.uniform_two

end AdditionPolynomialRealization

end FastPoly.Cost
