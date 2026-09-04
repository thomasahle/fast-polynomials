import FastPoly.Cost.Additions.Final
import FastPoly.Cost.RealizationBases
import FastPoly.Cost.RealizationCrownOptimized
import FastPoly.Cost.RealizationP15
import FastPoly.Cost.RealizationP27Optimized
import FastPoly.Cost.RealizationP31

/-!
# Same-program addition certificates for realized pair bases

The numerical `PairAddCost` relation is useful only after it is attached to the fixed
syntax which realizes the advertised pair.  `AdditionJointPairProgram` packages that
syntax, its literal addition count, and the matching ledger.  The constructors below
cover every nonrecursive pair base and provide semantic bridges for arbitrary
parameter environments.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- A fixed four-output pair program whose own literal additions satisfy the selected
degree ledger.  The multiplication index is the canonical half-degree budget. -/
structure AdditionJointPairProgram (R : Type u) [CommRing R]
    (degree additions : ℕ) where
  program : JointPairProgram R ((degree - 1) / 2)
  addition_count : program.circuit.gates.additions = additions
  ledger : PairAddCost degree additions

namespace AdditionJointPairProgram

/-- The certified additions remain attached after exposing the underlying fixed
`JointPairProgram`. -/
theorem program_additions {R : Type u} [CommRing R] {degree additions : ℕ}
    (certificate : AdditionJointPairProgram R degree additions) :
    certificate.program.circuit.gates.additions = additions :=
  certificate.addition_count

namespace Three

/-- Literal additions in the existing degree-three shared circuit. -/
@[simp] theorem circuit_additions {R : Type u} [CommRing R] :
    (FastPoly.Cost.Three.circuit (R := R)).gates.additions = 3 := by
  rfl

end Three

/-- Fixed addition-certified degree-three pair program. -/
def three (R : Type u) [CommRing R] : AdditionJointPairProgram R 3 3 where
  program :=
    { circuit := FastPoly.Cost.Three.circuit
      multiplication_count := by
        simpa only [show (3 - 1) / 2 = 1 by omega] using
          FastPoly.Cost.Three.circuit_multiplications (R := R) }
  addition_count := Three.circuit_additions
  ledger := PairAddCost.three

/-- The degree-three certificate's fixed syntax realizes the existing semantic base
at every parameter environment. -/
theorem three_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (three R).program.RealizesAt theta
      (FastPoly.Cost.Three.T₁ theta) (FastPoly.Cost.Three.T₂ theta)
      (FastPoly.Cost.Three.H₂ theta) 0 := by
  let source := FastPoly.Cost.Three.realized (R := R) theta
  exact ⟨source.eval₁, source.eval₂, source.evalH₂, source.evalH₄⟩

/-- Fixed addition-certified retained-shift crown program. -/
def crown (R : Type u) [CommRing R] (k : ℕ) (hk : 1 ≤ k) :
    AdditionJointPairProgram R (4 * k + 1) (tAdd (2 * k) 1 + 2) where
  program :=
    { circuit := CrownOptimized.circuit k
      multiplication_count := by
        simpa only [show (4 * k + 1 - 1) / 2 = 2 * k by omega] using
          CrownOptimized.circuit_multiplications (R := R) k hk }
  addition_count := CrownOptimized.circuit_additions k hk
  ledger := PairAddCost.fourKPlusOne k hk

/-- The crown certificate's fixed syntax realizes the retained-shift semantic crown
at every parameter environment. -/
theorem crown_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    (crown R k hk).program.RealizesAt theta
      (FastPoly.Tpair
        (FastPoly.crownHp (theta 0) (theta 1) (theta 2) (theta 3))
        (FastPoly.crownH4 (theta 0) (theta 1) (theta 2) (theta 3) + C (theta 4))
        k 2 (fun i => theta (5 + i))).1
      (FastPoly.Tpair
        (FastPoly.crownHp (theta 0) (theta 1) (theta 2) (theta 3))
        (FastPoly.crownH4 (theta 0) (theta 1) (theta 2) (theta 3) + C (theta 4))
        k 2 (fun i => theta (5 + i))).2
      (FastPoly.crownH2 (theta 0) (theta 1))
      (FastPoly.crownH4 (theta 0) (theta 1) (theta 2) (theta 3)) := by
  let source := CrownOptimized.realized (R := R) theta k hk
  exact ⟨source.eval₁, source.eval₂, source.evalH₂, source.evalH₄⟩

/-- Fixed addition-certified degree-fifteen pair program. -/
def fifteen (R : Type u) [CommRing R] : AdditionJointPairProgram R 15 23 where
  program :=
    { circuit := FastPoly.Cost.Fifteen.circuit
      multiplication_count := by
        simpa only [show (15 - 1) / 2 = 7 by omega] using
          FastPoly.Cost.Fifteen.circuit_multiplications (R := R) }
  addition_count := FastPoly.Cost.Fifteen.circuit_additions
  ledger := PairAddCost.fifteen

/-- The degree-fifteen certificate's fixed syntax realizes its committed semantic
base at every parameter environment. -/
theorem fifteen_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (fifteen R).program.RealizesAt theta
      (FastPoly.P15.T1 theta (FastPoly.P15.Q7 theta))
      (FastPoly.P15.T2 theta (FastPoly.P15.Q7 theta))
      (FastPoly.P15.H2 theta) (FastPoly.P15.H4 theta) := by
  let source := FastPoly.Cost.Fifteen.realized (R := R) theta
  exact ⟨source.eval₁, source.eval₂, source.evalH₂, source.evalH₄⟩

/-- Fixed addition-certified optimized degree-twenty-seven pair program. -/
def twentySeven (R : Type u) [CommRing R] :
    AdditionJointPairProgram R 27 43 where
  program :=
    { circuit := TwentySevenOptimized.circuit
      multiplication_count := by
        simpa only [show (27 - 1) / 2 = 13 by omega] using
          TwentySevenOptimized.circuit_multiplications (R := R) }
  addition_count := by
    change (TwentySevenOptimized.circuit (R := R)).gates.additions = 43
    exact TwentySevenOptimized.circuit_additions (R := R)
  ledger := PairAddCost.twentySeven

/-- The optimized degree-twenty-seven certificate's fixed syntax realizes its
committed semantic base at every parameter environment. -/
theorem twentySeven_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (twentySeven R).program.RealizesAt theta
      (FastPoly.P27Full.T1 theta) (FastPoly.P27Full.T2 theta)
      (FastPoly.P27Full.H2 theta) (FastPoly.P27Full.H4 theta) := by
  exact ⟨TwentySevenOptimized.eval_circuit_zero (R := R) theta,
    TwentySevenOptimized.eval_circuit_one (R := R) theta,
    TwentySevenOptimized.eval_circuit_two (R := R) theta,
    TwentySevenOptimized.eval_circuit_three (R := R) theta⟩

/-- Fixed addition-certified degree-thirty-one pair program. -/
def thirtyOne (R : Type u) [CommRing R] :
    AdditionJointPairProgram R 31 43 where
  program :=
    { circuit := FastPoly.Cost.ThirtyOne.circuit
      multiplication_count := by
        simpa only [show (31 - 1) / 2 = 15 by omega] using
          FastPoly.Cost.ThirtyOne.circuit_multiplications (R := R) }
  addition_count := FastPoly.Cost.ThirtyOne.circuit_additions
  ledger := PairAddCost.thirtyOne

/-- The degree-thirty-one certificate's fixed syntax realizes its committed semantic
base at every parameter environment. -/
theorem thirtyOne_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (thirtyOne R).program.RealizesAt theta
      (FastPoly.P31Full.T1 theta) (FastPoly.P31Full.T2 theta)
      (FastPoly.P31Full.H2 theta) (FastPoly.P31Full.H4 theta) := by
  let source := FastPoly.Cost.ThirtyOne.realized (R := R) theta
  exact ⟨source.eval₁, source.eval₂, source.evalH₂, source.evalH₄⟩

end AdditionJointPairProgram

end FastPoly.Cost
