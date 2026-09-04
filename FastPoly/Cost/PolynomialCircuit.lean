import FastPoly.Cost.MultiplicationProgram
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomial-circuit inputs and joint pair realizations

The master construction is evaluated from one polynomial variable and a countable
parameter supply. A concrete circuit uses only finitely many labels, while `Nat` labels
make recursive block shifts literal renamings of wires.

`JointPairRealization` is the cost-sensitive invariant missing from algebraic
splittability alone: the *same* circuit outputs both components and the recorded
quadratic/quartic byproducts, and its multiplication count is computed from that circuit.
No characteristic assumption occurs in this interface.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- Inputs available to a preprocessed polynomial-evaluation circuit. -/
inductive PolyInput where
  | variable
  | parameter (index : ℕ)
deriving DecidableEq, Repr

/-- Interpret the distinguished input as `x` and parameter inputs as constant
polynomials. -/
noncomputable def polyEnv {A : Type v} [CommRing A] (θ : ℕ → A) : PolyInput → A[X]
  | .variable => X
  | .parameter i => C (θ i)

/-- The polynomial variable as a circuit wire. -/
def Circuit.polyX {R : Type u} : Circuit R PolyInput 1 :=
  Circuit.input .variable

/-- One preprocessing parameter as a circuit wire. -/
def Circuit.polyParameter {R : Type u} (i : ℕ) : Circuit R PolyInput 1 :=
  Circuit.input (.parameter i)

@[simp] theorem polyEnv_variable {A : Type v} [CommRing A] (θ : ℕ → A) :
    polyEnv θ .variable = (X : A[X]) := rfl

@[simp] theorem polyEnv_parameter {A : Type v} [CommRing A] (θ : ℕ → A) (i : ℕ) :
    polyEnv θ (.parameter i) = C (θ i) := rfl

@[simp] theorem Circuit.eval_polyX {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (θ : ℕ → A) :
    (Circuit.polyX (R := R)).eval (polyEnv θ) 0 = (X : A[X]) := rfl

@[simp] theorem Circuit.eval_polyParameter {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (θ : ℕ → A) (i : ℕ) :
    (Circuit.polyParameter (R := R) i).eval (polyEnv θ) 0 = C (θ i) := rfl

/-- Four scalar circuits packaged in the output order used by the master invariant:
pair components first, then the recorded quadratic and quartic. -/
def Circuit.pairWithPowers {R : Type u} {ι : Type v}
    (T₁ T₂ H₂ H₄ : Circuit R ι 1) : Circuit R ι 4 :=
  .fork (.fork T₁ T₂) (.fork H₂ H₄)

@[simp] theorem Circuit.eval_pairWithPowers_zero {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    (T₁ T₂ H₂ H₄ : Circuit R ι 1) (env : ι → A) :
    (Circuit.pairWithPowers T₁ T₂ H₂ H₄).eval env 0 = T₁.eval env 0 := by
  rfl

@[simp] theorem Circuit.eval_pairWithPowers_one {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    (T₁ T₂ H₂ H₄ : Circuit R ι 1) (env : ι → A) :
    (Circuit.pairWithPowers T₁ T₂ H₂ H₄).eval env 1 = T₂.eval env 0 := by
  rfl

@[simp] theorem Circuit.eval_pairWithPowers_two {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    (T₁ T₂ H₂ H₄ : Circuit R ι 1) (env : ι → A) :
    (Circuit.pairWithPowers T₁ T₂ H₂ H₄).eval env 2 = H₂.eval env 0 := by
  rfl

@[simp] theorem Circuit.eval_pairWithPowers_three {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*}
    (T₁ T₂ H₂ H₄ : Circuit R ι 1) (env : ι → A) :
    (Circuit.pairWithPowers T₁ T₂ H₂ H₄).eval env 3 = H₄.eval env 0 := by
  rfl

@[simp] theorem Circuit.gates_pairWithPowers {R : Type u} {ι : Type v}
    (T₁ T₂ H₂ H₄ : Circuit R ι 1) :
    (Circuit.pairWithPowers T₁ T₂ H₂ H₄).gates =
      T₁.gates + T₂.gates + H₂.gates + H₄.gates := by
  simp only [Circuit.pairWithPowers, Circuit.gates_fork]
  apply GateCount.ext <;>
    simp only [GateCount.add_additions, GateCount.add_multiplications, Nat.add_assoc]

/-- The current construction family's four-output specialization of the generic fixed
program object.  The payload order is pair components, quadratic, then quartic. -/
abbrev JointPairProgram (R : Type u) [CommRing R] (multiplications : ℕ) :=
  MultiplicationProgram R PolyInput 4 multiplications

namespace JointPairProgram

/-- A fixed program has the advertised four outputs at one parameter environment. -/
def RealizesAt {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {m : ℕ} (program : JointPairProgram R m) (θ : ℕ → A)
    (T₁ T₂ H₂ H₄ : A[X]) : Prop :=
  program.circuit.eval (polyEnv θ) 0 = T₁ ∧
    program.circuit.eval (polyEnv θ) 1 = T₂ ∧
    program.circuit.eval (polyEnv θ) 2 = H₂ ∧
    program.circuit.eval (polyEnv θ) 3 = H₄

/-- Uniform realization: one syntax tree works for every parameter environment.  The
quantifier order rules out smuggling parameter-dependent values into free constants. -/
def RealizesFamily {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {m : ℕ} (program : JointPairProgram R m)
    (T₁ T₂ H₂ H₄ : (ℕ → A) → A[X]) : Prop :=
  ∀ θ, program.RealizesAt θ (T₁ θ) (T₂ θ) (H₂ θ) (H₄ θ)

end JointPairProgram

/-- A pointwise semantic witness for a single shared circuit computing a pair and its
recorded byproducts at one parameter environment.

The multiplication equality is attached to the circuit itself; unlike `PairCost`, it
cannot be proved independently and paired with unrelated polynomial witnesses. The
exact addition count remains available as `realization.circuit.gates.additions`.

This structure deliberately does not claim that the circuit was chosen independently
of `θ`.  Use `JointPairProgram.RealizesFamily` (or a symbolic free-parameter
instantiation) for the public uniform cost theorem. -/
structure JointPairRealization {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (θ : ℕ → A) (T₁ T₂ H₂ H₄ : A[X]) (multiplications : ℕ) where
  circuit : Circuit R PolyInput 4
  eval₁ : circuit.eval (polyEnv θ) 0 = T₁
  eval₂ : circuit.eval (polyEnv θ) 1 = T₂
  evalH₂ : circuit.eval (polyEnv θ) 2 = H₂
  evalH₄ : circuit.eval (polyEnv θ) 3 = H₄
  multiplication_count : circuit.gates.multiplications = multiplications

/-- Proposition-valued *pointwise* wrapper used while composing one fixed construction
branch.  It is not, by itself, the final uniform circuit theorem: `∀ θ, ∃ circuit` has
the wrong quantifier order for that purpose. -/
def JointPairRealizable {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (θ : ℕ → A) (T₁ T₂ H₂ H₄ : A[X]) (multiplications : ℕ) : Prop :=
  Nonempty (JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ multiplications)

namespace JointPairRealization

/-- Forget the pointwise equations and retain the underlying parameter-independent
program syntax. -/
def program {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {m : ℕ}
    (h : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ m) :
    JointPairProgram R m where
  circuit := h.circuit
  multiplication_count := h.multiplication_count

/-- The pointwise witness supplies the corresponding semantics for its program. -/
theorem program_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {m : ℕ}
    (h : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ m) :
    h.program.RealizesAt θ T₁ T₂ H₂ H₄ :=
  ⟨h.eval₁, h.eval₂, h.evalH₂, h.evalH₄⟩

/-- The exact addition count of the very circuit certified by the realization. -/
def additions {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {m : ℕ}
    (h : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ m) : ℕ :=
  h.circuit.gates.additions

end JointPairRealization

end FastPoly.Cost
