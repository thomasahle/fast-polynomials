import FastPoly.Cost.PolynomialProgram
import FastPoly.Examples.SepticAdditions

/-!
# The optimized four-product septic as one fixed program

This is the ten-addition presentation from `sec:addition-count`.  The intermediate
polynomials `y`, `z`, and `w` are bound explicitly, so the circuit syntax records their
sharing rather than relying on an external numerical schedule.
-/

namespace FastPoly.Cost.SepticProgram

open Polynomial

universe u v

private def x {R : Type u} : Circuit R PolyInput 1 := Circuit.polyX
private def a {R : Type u} (i : ℕ) : Circuit R PolyInput 1 :=
  Circuit.polyParameter i

/-- First shared product, `y=x(x+b₆)`. -/
private def yCircuit {R : Type u} : Circuit R PolyInput 1 :=
  .mul x (.add x (a 6))

private abbrev YEnv := Sum PolyInput (Fin 1)

/-- Second shared product, `z=(b₅+x+y)(b₄+x)`. -/
private def zCircuit {R : Type u} : Circuit R YEnv 1 :=
  let old (p : Circuit R PolyInput 1) : Circuit R YEnv 1 := p.liftLeft
  let y := Circuit.rightInput (R := R) (i := (0 : Fin 1))
  .mul (.add (.add (old (a 5)) (old x)) y) (.add (old (a 4)) (old x))

private abbrev ZEnv := Sum YEnv (Fin 1)

/-- Third shared product, `w=(b₃+z)x`. -/
private def wCircuit {R : Type u} : Circuit R ZEnv 1 :=
  let old (p : Circuit R PolyInput 1) : Circuit R ZEnv 1 := p.liftLeft.liftLeft
  let z := Circuit.rightInput (R := R) (i := (0 : Fin 1))
  .mul (.add (old (a 3)) z) (old x)

private abbrev WEnv := Sum ZEnv (Fin 1)

/-- Last product and the affine output shell. -/
private def finishCircuit {R : Type u} : Circuit R WEnv 1 :=
  let old (p : Circuit R PolyInput 1) : Circuit R WEnv 1 :=
    p.liftLeft.liftLeft.liftLeft
  let y : Circuit R WEnv 1 := Circuit.input (.inl (.inl (.inr 0)))
  let z : Circuit R WEnv 1 := Circuit.input (.inl (.inr 0))
  let w := Circuit.rightInput (R := R) (i := (0 : Fin 1))
  let v := .mul (.add (.add (old (a 2)) (old x)) z) (.add (old (a 1)) w)
  .add (.add (old (a 0)) y) v

/-- Literal shared circuit for the optimized septic. -/
def circuit {R : Type u} : Circuit R PolyInput 1 :=
  .bind yCircuit (.bind zCircuit (.bind wCircuit finishCircuit))

section Semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private noncomputable def yValue (theta : ℕ → A) : A[X] :=
  X * (X + C (theta 6))

private noncomputable def zValue (theta : ℕ → A) : A[X] :=
  (C (theta 5) + X + yValue theta) * (C (theta 4) + X)

private noncomputable def wValue (theta : ℕ → A) : A[X] :=
  (C (theta 3) + zValue theta) * X

private noncomputable def value (theta : ℕ → A) : A[X] :=
  C (theta 0) + yValue theta +
    (C (theta 2) + X + zValue theta) * (C (theta 1) + wValue theta)

private theorem value_eq_optimizedSeptic (theta : ℕ → A) :
    value theta = FastPoly.optimizedSeptic
      (theta 0) (theta 1) (theta 2) (theta 3) (theta 4) (theta 5) (theta 6) := by
  rfl

@[simp] theorem eval_circuit (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 0 = value theta := by
  rfl

end Semantics

/-! ## Exact cost and fixed-program certificate -/

@[simp] theorem gates_circuit {R : Type u} :
    (circuit (R := R)).gates = GateCount.of 10 4 := by
  apply GateCount.ext <;> rfl

/-- The exact four-product, ten-addition program. -/
def program {R : Type u} [CommRing R] : PolynomialProgram R 4 where
  circuit := circuit
  multiplication_count := by
    rw [gates_circuit, GateCount.of_multiplications]

@[simp] theorem additions_program {R : Type u} [CommRing R] :
    (program (R := R)).additions = 10 := by
  rw [MultiplicationProgram.additions, program, gates_circuit,
    GateCount.of_additions]

/-- Pointwise semantics, stated against the same optimized family whose explicit decoder
is proved in `SepticAdditions.lean`. -/
theorem realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (program (R := R)).RealizesAt theta
      (FastPoly.optimizedSeptic
        (theta 0) (theta 1) (theta 2) (theta 3) (theta 4) (theta 5) (theta 6)) := by
  rw [PolynomialProgram.realizesAt_iff]
  change (circuit (R := R)).eval (polyEnv theta) 0 = _
  rw [eval_circuit, value_eq_optimizedSeptic]

/-- Structural endpoint for the very polynomial realized by `program`. -/
theorem good {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A] (theta : ℕ → A) :
    (FastPoly.optimizedSeptic
      (theta 0) (theta 1) (theta 2) (theta 3) (theta 4) (theta 5) (theta 6)).Monic ∧
    (FastPoly.optimizedSeptic
      (theta 0) (theta 1) (theta 2) (theta 3) (theta 4) (theta 5) (theta 6)).natDegree = 7 := by
  rw [FastPoly.optimizedSeptic_eq_septic]
  exact FastPoly.septic_good _ _ _ _ _ _ _

/-- Uniform public form: one literal program works for every vector of seven keys. -/
theorem realizesFiniteFamily {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] :
    (program (R := R)).RealizesFiniteFamily
      (fun key : Fin 7 → A => FastPoly.optimizedSeptic
        (key 0) (key 1) (key 2) (key 3) (key 4) (key 5) (key 6)) := by
  intro key
  have h := realizesAt (R := R) (zeroExtend key)
  change MultiplicationProgram.RealizesAt (program (R := R))
    (polyEnv (zeroExtend key))
    (oneOutput (FastPoly.optimizedSeptic
      (zeroExtend key 0) (zeroExtend key 1) (zeroExtend key 2)
      (zeroExtend key 3) (zeroExtend key 4) (zeroExtend key 5)
      (zeroExtend key 6))) at h
  simpa only [zeroExtend_apply_fin] using h

end FastPoly.Cost.SepticProgram
