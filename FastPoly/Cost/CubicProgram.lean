import FastPoly.Cost.PolynomialProgram

/-!
# The direct two-product, three-addition cubic program

The complete-polynomial addition ledger treats degree three as a direct Horner base.
Completing the degree-three pair would use one unnecessary addition, so this module
records the literal base circuit and its coefficient-by-coefficient decoder pivots.
-/

namespace FastPoly.Cost.CubicProgram

open Polynomial

universe u v

/-- Literal Horner circuit `x * (x * (x + a₂) + a₁) + a₀`. -/
def circuit {R : Type u} : Circuit R PolyInput 1 :=
  .add
    (.mul Circuit.polyX
      (.add
        (.mul Circuit.polyX
          (.add Circuit.polyX (Circuit.polyParameter 2)))
        (Circuit.polyParameter 1)))
    (Circuit.polyParameter 0)

/-- Polynomial computed by the direct cubic circuit. -/
noncomputable def value {A : Type v} [CommRing A] (theta : ℕ → A) : A[X] :=
  X * (X * (X + C (theta 2)) + C (theta 1)) + C (theta 0)

@[simp] theorem eval_circuit {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (circuit (R := R)).eval (polyEnv theta) 0 = value theta :=
  rfl

/-- The circuit uses exactly two nonscalar products and three additions. -/
@[simp] theorem gates_circuit {R : Type u} :
    (circuit (R := R)).gates = GateCount.of 3 2 := by
  apply GateCount.ext <;> rfl

/-- Fixed direct cubic program. -/
def program {R : Type u} [CommRing R] : PolynomialProgram R 2 where
  circuit := circuit
  multiplication_count := by
    rw [gates_circuit, GateCount.of_multiplications]

@[simp] theorem additions_program {R : Type u} [CommRing R] :
    (program (R := R)).additions = 3 := by
  rw [MultiplicationProgram.additions, program, gates_circuit,
    GateCount.of_additions]

/-- Pointwise semantics of the exact fixed program. -/
theorem realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (program (R := R)).RealizesAt theta (value theta) := by
  rw [PolynomialProgram.realizesAt_iff]
  change (circuit (R := R)).eval (polyEnv theta) 0 = value theta
  rw [eval_circuit]

/-! The decoder is the literal coefficient readout, in ascending order. -/

@[simp] theorem coeff_zero {A : Type v} [CommRing A] (theta : ℕ → A) :
    (value theta).coeff 0 = theta 0 := by
  simp [value]

@[simp] theorem coeff_one {A : Type v} [CommRing A] (theta : ℕ → A) :
    (value theta).coeff 1 = theta 1 := by
  simp [value]

@[simp] theorem coeff_two {A : Type v} [CommRing A] (theta : ℕ → A) :
    (value theta).coeff 2 = theta 2 := by
  simp [value]

end FastPoly.Cost.CubicProgram
