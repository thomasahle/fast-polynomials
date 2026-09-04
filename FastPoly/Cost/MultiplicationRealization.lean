import FastPoly.Cost.MultiplicationProgram

/-!
# Circuit realizations with an exact multiplication count

This is the small, construction-neutral pointwise semantic object used when an
intermediate producer has more than one output.  Unlike `Cost.Realization`, it leaves
the addition count existential while retaining the same circuit, so clients may still
inspect that count later.  Unlike a numerical schedule, its cost cannot be detached
from its output.  Public uniform theorems use `MultiplicationProgram.RealizesFamily`;
the pointwise package here is the convenient composition layer.
-/

namespace FastPoly.Cost

universe u v w

/-- A named two-output vector, avoiding repeated `Fin.cases` terms at staged circuit
interfaces. -/
def twoOutputs {A : Type w} (first second : A) : Fin 2 → A
  | 0 => first
  | 1 => second

@[simp] theorem twoOutputs_zero {A : Type w} (first second : A) :
    twoOutputs first second 0 = first := rfl

@[simp] theorem twoOutputs_one {A : Type w} (first second : A) :
    twoOutputs first second 1 = second := rfl

/-- One finite-output circuit, its literal semantics, and its exact multiplication
count.  The input/output arities and evaluation algebra are completely generic. -/
structure MultiplicationRealization {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {ι : Type v} {q : ℕ}
    (env : ι → A) (output : Fin q → A) (multiplications : ℕ) where
  circuit : Circuit R ι q
  eval_eq : circuit.eval env = output
  multiplication_count : circuit.gates.multiplications = multiplications

namespace MultiplicationRealization

variable {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
  {ι : Type v} {q : ℕ} {env : ι → A} {output : Fin q → A} {m : ℕ}

@[simp] theorem eval_at (h : MultiplicationRealization (R := R) env output m)
    (i : Fin q) : h.circuit.eval env i = output i := by
  rw [h.eval_eq]

/-- Forget the pointwise equation and retain the underlying fixed syntax and count. -/
def program (h : MultiplicationRealization (R := R) env output m) :
    MultiplicationProgram R ι q m where
  circuit := h.circuit
  multiplication_count := h.multiplication_count

/-- The pointwise witness proves the corresponding semantics of its program. -/
theorem program_realizesAt (h : MultiplicationRealization (R := R) env output m) :
    h.program.RealizesAt env output :=
  h.eval_eq

end MultiplicationRealization

end FastPoly.Cost
