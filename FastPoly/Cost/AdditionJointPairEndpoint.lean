import FastPoly.Cost.AdditionPairBaseRealizations

/-!
# Same-program endpoint for pair addition bounds

This module exposes the consumer-facing invariant carried by
`AdditionJointPairRealization`: one fixed `JointPairProgram` simultaneously has the
advertised semantics, literal addition count, and recursive addition ledger.  The
numerical bounds are then applied to that program's own gates.
-/

namespace FastPoly.Cost.AdditionJointPairRealization

open Polynomial

universe u v

/-- Expose the single fixed program together with all three facts needed by a public
same-program addition theorem. -/
theorem exists_program {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {degree additions : ℕ}
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄
      degree additions) :
    ∃ program : JointPairProgram R ((degree - 1) / 2),
      program.RealizesAt theta T₁ T₂ H₂ H₄ ∧
        program.circuit.gates.additions = additions ∧
          PairAddCost degree additions :=
  ⟨source.certificate.program, source.realizesAt,
    source.certificate.addition_count, source.certificate.ledger⟩

/-- The sharp pair bound applies to the additions of the exact semantic program. -/
theorem program_additions_sharp {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {degree additions : ℕ}
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄
      degree additions) :
    4 * source.certificate.program.circuit.gates.additions ≤
      5 * degree + 24 * ceilLog2 degree * ceilLog2 degree := by
  rw [source.certificate.addition_count]
  exact source.certificate.ledger.sharp

/-- The uniform two-additions-per-degree bound applies to that same program. -/
theorem program_additions_uniform_two {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {degree additions : ℕ}
    (source : AdditionJointPairRealization R theta T₁ T₂ H₂ H₄
      degree additions) :
    source.certificate.program.circuit.gates.additions ≤ 2 * degree - 1 := by
  rw [source.certificate.addition_count]
  exact source.certificate.ledger.uniform_two

end FastPoly.Cost.AdditionJointPairRealization
