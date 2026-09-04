import FastPoly.Cost.Gates
import Mathlib.Algebra.Algebra.Basic

/-!
# Characteristic-independent arithmetic circuits

This module is the semantic replacement for a trusted numerical cost annotation.
Circuits are finite DAGs with explicit sharing, their evaluator is defined for every
`R`-algebra, and their gate count is computed solely from syntax.
-/

namespace FastPoly.Cost

universe u v w z

/-- A finite-output cartesian arithmetic circuit. Input labels may have any
type, but every circuit mentions only finitely many of them. `wire` includes
copying and permutation. `bind` is a genuine shared let-binding: its body
receives both the original inputs and all producer outputs.

There is deliberately no constructor carrying an arbitrary value or an
arbitrary cost. Every charged gate is visible in the syntax. -/
inductive Circuit (R : Type u) : (ι : Type v) → ℕ → Type (max u (v + 1)) where
  | wire {ι : Type v} {m : ℕ} (f : Fin m → ι) : Circuit R ι m
  | const {ι : Type v} (r : R) : Circuit R ι 1
  | add {ι : Type v} (left right : Circuit R ι 1) : Circuit R ι 1
  | sub {ι : Type v} (left right : Circuit R ι 1) : Circuit R ι 1
  | mul {ι : Type v} (left right : Circuit R ι 1) : Circuit R ι 1
  | neg {ι : Type v} (p : Circuit R ι 1) : Circuit R ι 1
  | scale {ι : Type v} (r : R) (p : Circuit R ι 1) : Circuit R ι 1
  | fork {ι : Type v} {m o : ℕ} (left : Circuit R ι m)
      (right : Circuit R ι o) : Circuit R ι (m + o)
  | bind {ι : Type v} {m o : ℕ} (producer : Circuit R ι m)
      (body : Circuit R (Sum ι (Fin m)) o) : Circuit R ι o

namespace Circuit

/-- Evaluate a circuit in an `R`-algebra. -/
def eval {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A] :
    {ι : Type v} → {m : ℕ} → Circuit R ι m → (ι → A) → Fin m → A
  | _, _, .wire f, input => fun j => input (f j)
  | _, _, .const r, _ => fun _ => algebraMap R A r
  | _, _, .add left right, input => fun _ => eval left input 0 + eval right input 0
  | _, _, .sub left right, input => fun _ => eval left input 0 - eval right input 0
  | _, _, .mul left right, input => fun _ => eval left input 0 * eval right input 0
  | _, _, .neg p, input => fun _ => -eval p input 0
  | _, _, .scale r p, input => fun _ => algebraMap R A r * eval p input 0
  | _, _, .fork left right, input =>
      Fin.addCases (eval left input) (eval right input)
  | _, _, .bind producer body, input =>
      eval body (Sum.elim input (eval producer input))

/-- Exact primitive-gate count of a circuit. -/
def gates {R : Type u} : {ι : Type v} → {m : ℕ} → Circuit R ι m → GateCount
  | _, _, .wire _ => 0
  | _, _, .const _ => 0
  | _, _, .add left right => gates left + gates right + GateCount.adds 1
  | _, _, .sub left right => gates left + gates right + GateCount.adds 1
  | _, _, .mul left right => gates left + gates right + GateCount.muls 1
  | _, _, .neg p => gates p
  | _, _, .scale _ p => gates p
  | _, _, .fork left right => gates left + gates right
  | _, _, .bind producer body => gates producer + gates body

/-- Select one input. -/
def input {R : Type u} {ι : Type v} (i : ι) : Circuit R ι 1 :=
  .wire (fun _ => i)

@[simp] theorem gates_input {R : Type u} {ι : Type v} (i : ι) :
    (input (R := R) i).gates = 0 := rfl

/-- A circuit whose outputs are precisely two scalar computations. -/
def pair {R : Type u} {ι : Type v} (left right : Circuit R ι 1) : Circuit R ι 2 :=
  .fork left right

/-- Shared single-output let-binding. -/
def let1 {R : Type u} {ι : Type v} {o : ℕ} (producer : Circuit R ι 1)
    (body : Circuit R (Sum ι (Fin 1)) o) : Circuit R ι o :=
  .bind producer body

/-- Rename the free input labels of a circuit. This is substitution by wires,
not semantic substitution: it preserves every primitive gate exactly. -/
def relabel {R : Type u} {ι : Type v} {κ : Type z} {m : ℕ} (f : ι → κ) :
    Circuit R ι m → Circuit R κ m
  | .wire g => .wire (fun j => f (g j))
  | .const r => .const r
  | .add left right => .add (relabel f left) (relabel f right)
  | .sub left right => .sub (relabel f left) (relabel f right)
  | .mul left right => .mul (relabel f left) (relabel f right)
  | .neg p => .neg (relabel f p)
  | .scale r p => .scale r (relabel f p)
  | .fork left right => .fork (relabel f left) (relabel f right)
  | .bind producer body =>
      .bind (relabel f producer) (relabel (Sum.map f id) body)

@[simp] theorem eval_wire {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {m : ℕ} (f : Fin m → ι) (env : ι → A) :
    eval (.wire f : Circuit R ι m) env = fun j => env (f j) := rfl

@[simp] theorem eval_const {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (r : R) (env : ι → A) :
    eval (.const r : Circuit R ι 1) env = fun _ => algebraMap R A r := rfl

@[simp] theorem eval_add {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (left right : Circuit R ι 1) (env : ι → A) :
    eval (.add left right) env = fun _ => eval left env 0 + eval right env 0 := rfl

@[simp] theorem eval_sub {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (left right : Circuit R ι 1) (env : ι → A) :
    eval (.sub left right) env = fun _ => eval left env 0 - eval right env 0 := rfl

@[simp] theorem eval_mul {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (left right : Circuit R ι 1) (env : ι → A) :
    eval (.mul left right) env = fun _ => eval left env 0 * eval right env 0 := rfl

@[simp] theorem eval_neg {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (p : Circuit R ι 1) (env : ι → A) :
    eval (.neg p) env = fun _ => -eval p env 0 := rfl

@[simp] theorem eval_scale {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (r : R) (p : Circuit R ι 1) (env : ι → A) :
    eval (.scale r p) env = fun _ => algebraMap R A r * eval p env 0 := rfl

@[simp] theorem eval_fork {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {m o : ℕ} (left : Circuit R ι m) (right : Circuit R ι o)
    (env : ι → A) :
    eval (.fork left right) env =
      Fin.addCases (eval left env) (eval right env) := rfl

/-- Definitional selectors for a two-output fork.  Naming these facts once avoids
exposing the `Fin.addCases` encoding in every per-output stage equation. -/
theorem eval_fork_zero {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (left right : Circuit R ι 1) (env : ι → A) :
    eval (.fork left right) env 0 = eval left env 0 := rfl

theorem eval_fork_one {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (left right : Circuit R ι 1) (env : ι → A) :
    eval (.fork left right) env 1 = eval right env 0 := rfl

/-- Definitional selectors for a right-associated three-output fork. -/
theorem eval_triple_zero {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (first second third : Circuit R ι 1) (env : ι → A) :
    eval (.fork first (.fork second third)) env 0 = eval first env 0 := rfl

theorem eval_triple_one {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (first second third : Circuit R ι 1) (env : ι → A) :
    eval (.fork first (.fork second third)) env 1 = eval second env 0 := rfl

theorem eval_triple_two {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} (first second third : Circuit R ι 1) (env : ι → A) :
    eval (.fork first (.fork second third)) env 2 = eval third env 0 := rfl

@[simp] theorem eval_bind {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {m o : ℕ} (producer : Circuit R ι m)
    (body : Circuit R (Sum ι (Fin m)) o) (env : ι → A) :
    eval (.bind producer body) env =
      eval body (Sum.elim env (eval producer env)) := rfl

@[simp] theorem gates_neg {R : Type u} {ι : Type v} (p : Circuit R ι 1) :
    gates (.neg p) = gates p := rfl

@[simp] theorem gates_scale {R : Type u} {ι : Type v} (r : R) (p : Circuit R ι 1) :
    gates (.scale r p) = gates p := rfl

@[simp] theorem gates_fork {R : Type u} {ι : Type v} {m o : ℕ}
    (left : Circuit R ι m) (right : Circuit R ι o) :
    gates (.fork left right) = gates left + gates right := rfl

@[simp] theorem gates_bind {R : Type u} {ι : Type v} {m o : ℕ}
    (producer : Circuit R ι m) (body : Circuit R (Sum ι (Fin m)) o) :
    gates (.bind producer body) = gates producer + gates body := rfl

theorem eval_relabel {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {m : ℕ} (c : Circuit R ι m) :
    ∀ {κ : Type z} (f : ι → κ) (env : κ → A),
      eval (relabel f c) env = eval c (env ∘ f) := by
  induction c with
  | wire g => intro κ f env; rfl
  | const r => intro κ f env; rfl
  | add left right ihl ihr =>
      intro κ f env
      simp only [relabel, eval_add, ihl, ihr]
  | sub left right ihl ihr =>
      intro κ f env
      simp only [relabel, eval_sub, ihl, ihr]
  | mul left right ihl ihr =>
      intro κ f env
      simp only [relabel, eval_mul, ihl, ihr]
  | neg p ih => intro κ f env; simp only [relabel, eval_neg, ih]
  | scale r p ih => intro κ f env; simp only [relabel, eval_scale, ih]
  | fork left right ihl ihr =>
      intro κ f env
      simp only [relabel, eval_fork, ihl, ihr]
  | bind producer body ihp ihb =>
      intro κ f env
      simp only [relabel, eval_bind, ihb, ihp]
      congr 2
      funext z
      cases z <;> rfl

theorem gates_relabel {R : Type u} {ι : Type v} {m : ℕ} (c : Circuit R ι m) :
    ∀ {κ : Type z} (f : ι → κ), gates (relabel f c) = gates c := by
  induction c with
  | wire g => intro κ f; rfl
  | const r => intro κ f; rfl
  | add left right ihl ihr =>
      intro κ f
      simp only [relabel, gates, ihl, ihr]
  | sub left right ihl ihr =>
      intro κ f
      simp only [relabel, gates, ihl, ihr]
  | mul left right ihl ihr =>
      intro κ f
      simp only [relabel, gates, ihl, ihr]
  | neg p ih => intro κ f; simp only [relabel, gates_neg, ih]
  | scale r p ih => intro κ f; simp only [relabel, gates_scale, ih]
  | fork left right ihl ihr =>
      intro κ f
      simp only [relabel, gates_fork, ihl, ihr]
  | bind producer body ihp ihb =>
      intro κ f
      simp only [relabel, gates_bind, ihp, ihb]

/-- Make a circuit ignore a newly added family of right-hand input labels. -/
def liftLeft {R : Type u} {ι : Type v} {κ : Type z} {m : ℕ}
    (c : Circuit R ι m) : Circuit R (Sum ι κ) m :=
  c.relabel Sum.inl

/-- Select one input from the right-hand side of an extended environment. In a
`bind` body these are precisely the producer's shared outputs. -/
def rightInput {R : Type u} {ι : Type v} {κ : Type z} (i : κ) :
    Circuit R (Sum ι κ) 1 :=
  input (Sum.inr i)

@[simp] theorem eval_liftLeft {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {ι : Type v} {κ : Type z} {m : ℕ}
    (c : Circuit R ι m) (left : ι → A) (right : κ → A) :
    c.liftLeft.eval (Sum.elim left right) = c.eval left := by
  rw [liftLeft, eval_relabel]
  congr 2

@[simp] theorem gates_liftLeft {R : Type u} {ι : Type v} {κ : Type z} {m : ℕ}
    (c : Circuit R ι m) : (c.liftLeft (κ := κ)).gates = c.gates :=
  c.gates_relabel _

@[simp] theorem eval_rightInput {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {ι : Type v} {κ : Type z}
    (i : κ) (left : ι → A) (right : κ → A) :
    (rightInput (R := R) (ι := ι) i).eval (Sum.elim left right) 0 = right i := rfl

@[simp] theorem gates_rightInput {R : Type u} {ι : Type v} {κ : Type z} (i : κ) :
    (rightInput (R := R) (ι := ι) i).gates = 0 := rfl

/-- Sequential composition, derived from a shared binding. The second circuit
sees the first circuit's output wires and nothing else. -/
def comp {R : Type u} {ι : Type v} {m o : ℕ} (first : Circuit R ι m)
    (second : Circuit R (Fin m) o) : Circuit R ι o :=
  .bind first (relabel Sum.inr second)

@[simp] theorem eval_comp {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {m o : ℕ} (first : Circuit R ι m) (second : Circuit R (Fin m) o)
    (env : ι → A) :
    eval (comp first second) env = eval second (eval first env) := by
  rw [comp, eval_bind, eval_relabel]
  congr 2

@[simp] theorem gates_comp {R : Type u} {ι : Type v} {m o : ℕ}
    (first : Circuit R ι m) (second : Circuit R (Fin m) o) :
    gates (comp first second) = gates first + gates second := by
  rw [comp, gates_bind, gates_relabel]

end Circuit

/-- A circuit whose semantics and exact gate count are both fixed. -/
structure Realization {R : Type u} {A : Type w} [CommRing R] [Ring A] [Algebra R A]
    {ι : Type v} {m : ℕ} (env : ι → A) (output : Fin m → A) (cost : GateCount) where
  circuit : Circuit R ι m
  eval_eq : circuit.eval env = output
  gates_eq : circuit.gates = cost

end FastPoly.Cost
