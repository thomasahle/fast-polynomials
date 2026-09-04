import FastPoly.Cost.ConstructionInput
import FastPoly.Cost.PolynomialCircuit

/-!
# Instantiating local construction circuits

`peelCircuit` and `tCircuit` are deliberately compiled over the symbolic labels
`ConstructionInput`.  This file supplies the characteristic-independent adapter used
at a global call site: a finite producer is bound once, and its shared outputs are used
as the local power, shifted-power, or source wires.  The polynomial variable and fresh
parameters remain ordinary `PolyInput` labels.

The adapter is only a relabeling, so it introduces no arithmetic gates.  Its semantic
theorem is the precise substitution statement needed by realization constructors.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- A wiring prescription from the inputs of a reusable local gadget to the free
polynomial inputs and the outputs of one finite producer. -/
structure ConstructionWiring (m : ℕ) where
  power : ℕ → Sum PolyInput (Fin m)
  shiftedPower : Sum PolyInput (Fin m)
  parameter : ℕ → ℕ
  source : Fin 2 → Sum PolyInput (Fin m)

/-- The input relabeling induced by a construction wiring. -/
def ConstructionWiring.label {m : ℕ} (w : ConstructionWiring m) :
    ConstructionInput → Sum PolyInput (Fin m)
  | .variable => .inl .variable
  | .power i => w.power i
  | .shiftedPower => w.shiftedPower
  | .parameter i => .inl (.parameter (w.parameter i))
  | .source i => w.source i

/-- Interpret a local construction circuit after a finite producer has been bound. -/
def Circuit.instantiateConstruction {R : Type u} {m o : ℕ}
    (w : ConstructionWiring m) (c : Circuit R ConstructionInput o) :
    Circuit R (Sum PolyInput (Fin m)) o :=
  c.relabel w.label

/-- Value-level power environment selected by a wiring. -/
noncomputable def ConstructionWiring.powerValues {A : Type v} [CommRing A] {m : ℕ}
    (w : ConstructionWiring m) (θ : ℕ → A) (values : Fin m → A[X]) : ℕ → A[X] :=
  fun i => Sum.elim (polyEnv θ) values (w.power i)

/-- Value-level shifted power selected by a wiring. -/
noncomputable def ConstructionWiring.shiftedValue {A : Type v} [CommRing A] {m : ℕ}
    (w : ConstructionWiring m) (θ : ℕ → A) (values : Fin m → A[X]) : A[X] :=
  Sum.elim (polyEnv θ) values w.shiftedPower

/-- Value-level source pair selected by a wiring. -/
noncomputable def ConstructionWiring.sourceValues {A : Type v} [CommRing A] {m : ℕ}
    (w : ConstructionWiring m) (θ : ℕ → A) (values : Fin m → A[X]) :
    Fin 2 → A[X] :=
  fun i => Sum.elim (polyEnv θ) values (w.source i)

theorem ConstructionWiring.env_comp_label {A : Type v} [CommRing A] {m : ℕ}
    (w : ConstructionWiring m) (θ : ℕ → A) (values : Fin m → A[X]) :
    Sum.elim (polyEnv θ) values ∘ w.label =
      constructionEnv (w.powerValues θ values) (w.shiftedValue θ values)
        (fun i => θ (w.parameter i)) (w.sourceValues θ values) := by
  funext input
  cases input <;> rfl

@[simp] theorem Circuit.eval_instantiateConstruction {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m o : ℕ}
    (w : ConstructionWiring m) (c : Circuit R ConstructionInput o)
    (θ : ℕ → A) (values : Fin m → A[X]) :
    (c.instantiateConstruction w).eval (Sum.elim (polyEnv θ) values) =
      c.eval (constructionEnv (w.powerValues θ values) (w.shiftedValue θ values)
        (fun i => θ (w.parameter i)) (w.sourceValues θ values)) := by
  rw [Circuit.instantiateConstruction, Circuit.eval_relabel,
    w.env_comp_label θ values]

@[simp] theorem Circuit.gates_instantiateConstruction {R : Type u} {m o : ℕ}
    (w : ConstructionWiring m) (c : Circuit R ConstructionInput o) :
    (c.instantiateConstruction w).gates = c.gates :=
  c.gates_relabel _

/-- Bind a finite shared producer and run a local construction circuit with the stated
wiring. -/
def Circuit.bindConstruction {R : Type u} {m o : ℕ}
    (producer : Circuit R PolyInput m) (w : ConstructionWiring m)
    (gadget : Circuit R ConstructionInput o) : Circuit R PolyInput o :=
  .bind producer (gadget.instantiateConstruction w)

@[simp] theorem Circuit.eval_bindConstruction {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m o : ℕ}
    (producer : Circuit R PolyInput m) (w : ConstructionWiring m)
    (gadget : Circuit R ConstructionInput o) (θ : ℕ → A) :
    (Circuit.bindConstruction producer w gadget).eval (polyEnv θ) =
      gadget.eval
        (constructionEnv (w.powerValues θ (producer.eval (polyEnv θ)))
          (w.shiftedValue θ (producer.eval (polyEnv θ)))
          (fun i => θ (w.parameter i))
          (w.sourceValues θ (producer.eval (polyEnv θ)))) := by
  rw [Circuit.bindConstruction, Circuit.eval_bind,
    Circuit.eval_instantiateConstruction]

@[simp] theorem Circuit.gates_bindConstruction {R : Type u} {m o : ℕ}
    (producer : Circuit R PolyInput m) (w : ConstructionWiring m)
    (gadget : Circuit R ConstructionInput o) :
    (Circuit.bindConstruction producer w gadget).gates =
      producer.gates + gadget.gates := by
  rw [Circuit.bindConstruction, Circuit.gates_bind,
    Circuit.gates_instantiateConstruction]

end FastPoly.Cost
