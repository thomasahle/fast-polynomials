import FastPoly.Cost.Gates

/-!
# Gate-accounting schedule model

`Program α` is a writer-style accounting object: its output is an `α`, and its annotation
records the number of top-level additions and nonscalar multiplications.  Monadic bind
models DAG sharing: a charged producer is counted once and its result may then be reused by
the continuation.  Inputs, constants, negation, and integer scalar multiples are free;
`addGate`, `subGate`, and `mulGate` are the primitive charged operations.

This deliberately separates a circuit from the syntax tree of its output expression.  In
particular, writing the same let-bound value twice does not charge its construction twice.
It is also deliberately an accounting DSL rather than an intrinsically typed circuit
syntax: `charge` is a trusted annotation.  Consequently, a theorem about a `Program Unit`
proves the numerical recurrence for a displayed construction schedule, but not by itself
that an unrelated polynomial has that cost.  The final construction theorem must attach
the matching schedule constructor in the same branch in which it constructs and decodes
the polynomial pair.  This separation prevents the numerical shadow from being mistaken
for a realizability theorem.
-/

namespace FastPoly.Cost

universe u

/-- A value together with an explicit gate-accounting annotation. -/
structure Program (α : Type*) where
  value : α
  gates : GateCount

namespace Program

protected def pure {α : Type*} (x : α) : Program α := ⟨x, 0⟩

protected def bind {α β : Type u} (p : Program α) (f : α → Program β) : Program β :=
  let q := f p.value
  ⟨q.value, p.gates + q.gates⟩

instance : Monad Program where
  pure := Program.pure
  bind := Program.bind

/-- Record a block of gates whose semantic result is `x`. -/
def charge {α : Type*} (g : GateCount) (x : α) : Program α := ⟨x, g⟩

/-- A cost-free input or previously computed value. -/
def input {α : Type*} (x : α) : Program α := pure x

/-- One charged addition. -/
def addGate {α : Type*} [Add α] (x y : α) : Program α :=
  charge (GateCount.adds 1) (x + y)

/-- One charged subtraction. -/
def subGate {α : Type*} [Sub α] (x y : α) : Program α :=
  charge (GateCount.adds 1) (x - y)

/-- One charged nonscalar multiplication. -/
def mulGate {α : Type*} [Mul α] (x y : α) : Program α :=
  charge (GateCount.muls 1) (x * y)

/-- Negation is multiplication by the fixed scalar `-1`, hence free. -/
def negFree {α : Type*} [Neg α] (x : α) : Program α := pure (-x)

/-- Multiplication by a natural-number scalar is implemented by additions and is not a
nonscalar multiplication gate in the paper's model. -/
def nsmulFree {α : Type*} [SMul ℕ α] (n : ℕ) (x : α) : Program α := pure (n • x)

/-- A schedule fragment with no semantic payload. -/
def schedule (g : GateCount) : Program Unit := charge g ()

/-- Sequential composition of schedule fragments. -/
def thenSchedule (p q : Program Unit) : Program Unit := do
  let _ ← p
  q

@[simp] theorem pure_value {α : Type*} (x : α) : (pure x : Program α).value = x := rfl
@[simp] theorem pure_gates {α : Type*} (x : α) : (pure x : Program α).gates = 0 := rfl
@[simp] theorem bind_value {α β : Type u} (p : Program α) (f : α → Program β) :
    (p >>= f).value = (f p.value).value := rfl
@[simp] theorem bind_gates {α β : Type u} (p : Program α) (f : α → Program β) :
    (p >>= f).gates = p.gates + (f p.value).gates := rfl
@[simp] theorem charge_value {α : Type*} (g : GateCount) (x : α) :
    (charge g x).value = x := rfl
@[simp] theorem charge_gates {α : Type*} (g : GateCount) (x : α) :
    (charge g x).gates = g := rfl
@[simp] theorem schedule_gates (g : GateCount) : (schedule g).gates = g := rfl
@[simp] theorem thenSchedule_gates (p q : Program Unit) :
    (thenSchedule p q).gates = p.gates + q.gates := rfl

/-- The formal DAG-sharing property: binding a result and reusing the bound value in a
cost-free expression charges the producer exactly once. -/
theorem shared_once {α β : Type u} (p : Program α) (f : α → β) :
    (do
      let x ← p
      pure (f x)).gates = p.gates := by
  rfl

end Program

end FastPoly.Cost
