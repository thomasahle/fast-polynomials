import FastPoly.Cost.Circuit

/-!
# Uniform finite-output circuit programs

`MultiplicationProgram` separates circuit syntax from any particular input values.  It
is the construction-neutral object for public exact-multiplication theorems: one syntax
tree and its literal gate count are chosen first, and semantic correctness may then be
proved uniformly over a family of environments.

Pointwise `MultiplicationRealization`s remain useful while composing a construction,
but quantifying those witnesses after an environment would permit the circuit itself to
depend on that environment.  `RealizesFamily` records the required quantifier order.
-/

namespace FastPoly.Cost

universe u v w z

/-- A finite-output circuit syntax with its exact nonscalar-multiplication count. -/
structure MultiplicationProgram (R : Type u) [CommRing R] (input : Type v)
    (outputs multiplications : ℕ) where
  circuit : Circuit R input outputs
  multiplication_count : circuit.gates.multiplications = multiplications

namespace MultiplicationProgram

/-- A fixed program has the advertised output at one environment. -/
def RealizesAt {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {q m : ℕ} (program : MultiplicationProgram R ι q m)
    (env : ι → A) (output : Fin q → A) : Prop :=
  program.circuit.eval env = output

/-- One fixed syntax realizes a whole indexed family of environments and outputs. -/
def RealizesFamily {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {κ : Type z} {q m : ℕ} (program : MultiplicationProgram R ι q m)
    (env : κ → ι → A) (output : κ → Fin q → A) : Prop :=
  ∀ key, program.RealizesAt (env key) (output key)

/-- The addition count of the same literal program. -/
def additions {R : Type u} [CommRing R] {ι : Type v} {q m : ℕ}
    (program : MultiplicationProgram R ι q m) : ℕ :=
  program.circuit.gates.additions

end MultiplicationProgram

end FastPoly.Cost
