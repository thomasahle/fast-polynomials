import FastPoly.Cost.Circuit
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Local inputs for reusable construction circuits

The fill, known-powers, and `T` gadgets are compiled once over symbolic input labels.
At a call site these labels are relabeled to global parameters or to outputs of an
earlier shared binding. This keeps local cost theorems independent of the surrounding
construction and makes all reuse explicit.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- Inputs that can occur in a local construction gadget. -/
inductive ConstructionInput where
  | variable
  | power (level : ℕ)
  | shiftedPower
  | parameter (index : ℕ)
  | source (component : Fin 2)
deriving DecidableEq, Repr

/-- Semantic environment for a local gadget. -/
noncomputable def constructionEnv {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) : ConstructionInput → A[X]
  | .variable => X
  | .power i => powers i
  | .shiftedPower => shifted
  | .parameter i => C (parameters i)
  | .source i => source i

def Circuit.constructionX {R : Type u} : Circuit R ConstructionInput 1 :=
  Circuit.input .variable

def Circuit.constructionPower {R : Type u} (level : ℕ) :
    Circuit R ConstructionInput 1 :=
  Circuit.input (.power level)

def Circuit.constructionShiftedPower {R : Type u} :
    Circuit R ConstructionInput 1 :=
  Circuit.input .shiftedPower

def Circuit.constructionParameter {R : Type u} (index : ℕ) :
    Circuit R ConstructionInput 1 :=
  Circuit.input (.parameter index)

def Circuit.constructionSource {R : Type u} (component : Fin 2) :
    Circuit R ConstructionInput 1 :=
  Circuit.input (.source component)

@[simp] theorem Circuit.gates_constructionX {R : Type u} :
    (Circuit.constructionX (R := R)).gates = 0 := rfl

@[simp] theorem Circuit.gates_constructionPower {R : Type u} (level : ℕ) :
    (Circuit.constructionPower (R := R) level).gates = 0 := rfl

@[simp] theorem Circuit.gates_constructionShiftedPower {R : Type u} :
    (Circuit.constructionShiftedPower (R := R)).gates = 0 := rfl

@[simp] theorem Circuit.gates_constructionParameter {R : Type u} (index : ℕ) :
    (Circuit.constructionParameter (R := R) index).gates = 0 := rfl

@[simp] theorem Circuit.gates_constructionSource {R : Type u} (component : Fin 2) :
    (Circuit.constructionSource (R := R) component).gates = 0 := rfl

@[simp] theorem Circuit.eval_constructionX {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) :
    (Circuit.constructionX (R := R)).eval
        (constructionEnv powers shifted parameters source) 0 = X :=
  rfl

@[simp] theorem Circuit.eval_constructionPower {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) (level : ℕ) :
    (Circuit.constructionPower (R := R) level).eval
        (constructionEnv powers shifted parameters source) 0 = powers level :=
  rfl

@[simp] theorem Circuit.eval_constructionShiftedPower {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) :
    (Circuit.constructionShiftedPower (R := R)).eval
        (constructionEnv powers shifted parameters source) 0 = shifted :=
  rfl

@[simp] theorem Circuit.eval_constructionParameter {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) (index : ℕ) :
    (Circuit.constructionParameter (R := R) index).eval
        (constructionEnv powers shifted parameters source) 0 = C (parameters index) :=
  rfl

@[simp] theorem Circuit.eval_constructionSource {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) (component : Fin 2) :
    (Circuit.constructionSource (R := R) component).eval
        (constructionEnv powers shifted parameters source) 0 = source component :=
  rfl

/-- Reindex only the fresh parameter block of a local gadget. -/
def ConstructionInput.reindexParameters (f : ℕ → ℕ) :
    ConstructionInput → ConstructionInput
  | .variable => .variable
  | .power i => .power i
  | .shiftedPower => .shiftedPower
  | .parameter i => .parameter (f i)
  | .source i => .source i

def Circuit.reindexConstructionParameters {R : Type u} {m : ℕ} (f : ℕ → ℕ)
    (c : Circuit R ConstructionInput m) : Circuit R ConstructionInput m :=
  c.relabel (ConstructionInput.reindexParameters f)

@[simp] theorem constructionEnv_variable {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) :
    constructionEnv powers shifted parameters source .variable = X := rfl

@[simp] theorem constructionEnv_power {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) (i : ℕ) :
    constructionEnv powers shifted parameters source (.power i) = powers i := rfl

@[simp] theorem constructionEnv_shiftedPower {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) :
    constructionEnv powers shifted parameters source .shiftedPower = shifted := rfl

@[simp] theorem constructionEnv_parameter {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) (i : ℕ) :
    constructionEnv powers shifted parameters source (.parameter i) = C (parameters i) := rfl

@[simp] theorem constructionEnv_source {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) (i : Fin 2) :
    constructionEnv powers shifted parameters source (.source i) = source i := rfl

theorem constructionEnv_comp_reindex {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (source : Fin 2 → A[X]) (f : ℕ → ℕ) :
    constructionEnv powers shifted parameters source ∘
        ConstructionInput.reindexParameters f =
      constructionEnv powers shifted (parameters ∘ f) source := by
  funext input
  cases input <;> rfl

@[simp] theorem Circuit.eval_reindexConstructionParameters {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ} (f : ℕ → ℕ)
    (c : Circuit R ConstructionInput m) (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (c.reindexConstructionParameters f).eval
        (constructionEnv powers shifted parameters source) =
      c.eval (constructionEnv powers shifted (parameters ∘ f) source) := by
  rw [Circuit.reindexConstructionParameters, Circuit.eval_relabel,
    constructionEnv_comp_reindex]

@[simp] theorem Circuit.gates_reindexConstructionParameters {R : Type u} {m : ℕ}
    (f : ℕ → ℕ) (c : Circuit R ConstructionInput m) :
    (c.reindexConstructionParameters f).gates = c.gates :=
  c.gates_relabel _

end FastPoly.Cost
