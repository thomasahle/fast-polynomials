import FastPoly.Cost.AdditionPairEightSeven

/-!
# Same-program semantic wrappers for realized pair bases

Each nonrecursive addition certificate already carries one fixed program and a theorem
that this exact syntax realizes the intended outputs at an arbitrary environment.  The
definitions below place those two facts in `AdditionJointPairRealization`, the common
input type of the recursive addition constructors.
-/

namespace FastPoly.Cost.AdditionJointPairRealization

open Polynomial

universe u v

/-- Attach pointwise semantics to an existing fixed addition-certified program. -/
def ofProgram {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {theta : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {degree additions : ℕ}
    (certificate : AdditionJointPairProgram R degree additions)
    (realizesAt : certificate.program.RealizesAt theta T₁ T₂ H₂ H₄) :
    AdditionJointPairRealization R theta T₁ T₂ H₂ H₄ degree additions :=
  ⟨certificate, realizesAt⟩

/-- Degree-three base with its literal three-addition circuit. -/
def three {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (theta : ℕ → A) :
    AdditionJointPairRealization R theta
      (FastPoly.Cost.Three.T₁ theta) (FastPoly.Cost.Three.T₂ theta)
      (FastPoly.Cost.Three.H₂ theta) 0 3 3 :=
  ofProgram (AdditionJointPairProgram.three R)
    (AdditionJointPairProgram.three_realizesAt theta)

/-- Retained-shift crown base with its selected exact addition count. -/
def crown {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    AdditionJointPairRealization R theta
      (FastPoly.Tpair
        (FastPoly.crownHp (theta 0) (theta 1) (theta 2) (theta 3))
        (FastPoly.crownH4 (theta 0) (theta 1) (theta 2) (theta 3) + C (theta 4))
        k 2 (fun i => theta (5 + i))).1
      (FastPoly.Tpair
        (FastPoly.crownHp (theta 0) (theta 1) (theta 2) (theta 3))
        (FastPoly.crownH4 (theta 0) (theta 1) (theta 2) (theta 3) + C (theta 4))
        k 2 (fun i => theta (5 + i))).2
      (FastPoly.crownH2 (theta 0) (theta 1))
      (FastPoly.crownH4 (theta 0) (theta 1) (theta 2) (theta 3))
      (4 * k + 1) (tAdd (2 * k) 1 + 2) :=
  ofProgram (AdditionJointPairProgram.crown R k hk)
    (AdditionJointPairProgram.crown_realizesAt theta k hk)

/-- Degree-fifteen base with its literal twenty-three-addition circuit. -/
def fifteen {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    (theta : ℕ → A) :
    AdditionJointPairRealization R theta
      (FastPoly.P15.T1 theta (FastPoly.P15.Q7 theta))
      (FastPoly.P15.T2 theta (FastPoly.P15.Q7 theta))
      (FastPoly.P15.H2 theta) (FastPoly.P15.H4 theta) 15 23 :=
  ofProgram (AdditionJointPairProgram.fifteen R)
    (AdditionJointPairProgram.fifteen_realizesAt theta)

/-- Degree-twenty-seven base with the optimized forty-three-addition circuit. -/
def twentySeven {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    AdditionJointPairRealization R theta
      (FastPoly.P27Full.T1 theta) (FastPoly.P27Full.T2 theta)
      (FastPoly.P27Full.H2 theta) (FastPoly.P27Full.H4 theta) 27 43 :=
  ofProgram (AdditionJointPairProgram.twentySeven R)
    (AdditionJointPairProgram.twentySeven_realizesAt theta)

/-- Degree-thirty-one base with its literal forty-three-addition circuit. -/
def thirtyOne {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    AdditionJointPairRealization R theta
      (FastPoly.P31Full.T1 theta) (FastPoly.P31Full.T2 theta)
      (FastPoly.P31Full.H2 theta) (FastPoly.P31Full.H4 theta) 31 43 :=
  ofProgram (AdditionJointPairProgram.thirtyOne R)
    (AdditionJointPairProgram.thirtyOne_realizesAt theta)

end FastPoly.Cost.AdditionJointPairRealization
