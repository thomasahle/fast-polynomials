import FastPoly.Cost.Circuit
import FastPoly.Cost.MultiplicationProgram

/-!
# Multiplicative depth ("height") of circuits

`Circuit.multDepth` evaluates a circuit in the (max, +1-per-multiplication)
algebra: wiring, constants, additions, subtractions, negations and fixed
scalar multiples are free, and every `mul` gate raises the maximum operand
depth by one.  This is the *height* of the paper's addition-accounting
section (`thm:construction-height`): the maximum number of nonscalar
multiplications on a directed input-to-output path of the DAG.

The lemma set mirrors the `eval` calculus, so the height ledger for the
concrete constructions can be proved by the same structural walks as their
semantic correctness.
-/

namespace FastPoly.Cost

universe u v w z

namespace Circuit

/-- Multiplicative depth of each output, given depths for the inputs. -/
def multDepth {R : Type u} :
    {ι : Type v} → {m : ℕ} → Circuit R ι m → (ι → ℕ) → Fin m → ℕ
  | _, _, .wire f, env => fun j => env (f j)
  | _, _, .const _, _ => fun _ => 0
  | _, _, .add left right, env => fun _ =>
      max (multDepth left env 0) (multDepth right env 0)
  | _, _, .sub left right, env => fun _ =>
      max (multDepth left env 0) (multDepth right env 0)
  | _, _, .mul left right, env => fun _ =>
      max (multDepth left env 0) (multDepth right env 0) + 1
  | _, _, .neg p, env => fun _ => multDepth p env 0
  | _, _, .scale _ p, env => fun _ => multDepth p env 0
  | _, _, .fork left right, env =>
      Fin.addCases (multDepth left env) (multDepth right env)
  | _, _, .bind producer body, env =>
      multDepth body (Sum.elim env (multDepth producer env))

@[simp] theorem multDepth_wire {R : Type u} {ι : Type v} {m : ℕ}
    (f : Fin m → ι) (env : ι → ℕ) :
    multDepth (.wire f : Circuit R ι m) env = fun j => env (f j) := rfl

@[simp] theorem multDepth_const {R : Type u} {ι : Type v} (r : R) (env : ι → ℕ) :
    multDepth (.const r : Circuit R ι 1) env = fun _ => 0 := rfl

@[simp] theorem multDepth_add {R : Type u} {ι : Type v}
    (left right : Circuit R ι 1) (env : ι → ℕ) :
    multDepth (.add left right) env =
      fun _ => max (multDepth left env 0) (multDepth right env 0) := rfl

@[simp] theorem multDepth_sub {R : Type u} {ι : Type v}
    (left right : Circuit R ι 1) (env : ι → ℕ) :
    multDepth (.sub left right) env =
      fun _ => max (multDepth left env 0) (multDepth right env 0) := rfl

@[simp] theorem multDepth_mul {R : Type u} {ι : Type v}
    (left right : Circuit R ι 1) (env : ι → ℕ) :
    multDepth (.mul left right) env =
      fun _ => max (multDepth left env 0) (multDepth right env 0) + 1 := rfl

@[simp] theorem multDepth_neg {R : Type u} {ι : Type v}
    (p : Circuit R ι 1) (env : ι → ℕ) :
    multDepth (.neg p) env = fun _ => multDepth p env 0 := rfl

@[simp] theorem multDepth_scale {R : Type u} {ι : Type v} (r : R)
    (p : Circuit R ι 1) (env : ι → ℕ) :
    multDepth (.scale r p) env = fun _ => multDepth p env 0 := rfl

@[simp] theorem multDepth_fork {R : Type u} {ι : Type v} {m o : ℕ}
    (left : Circuit R ι m) (right : Circuit R ι o) (env : ι → ℕ) :
    multDepth (.fork left right) env =
      Fin.addCases (multDepth left env) (multDepth right env) := rfl

@[simp] theorem multDepth_bind {R : Type u} {ι : Type v} {m o : ℕ}
    (producer : Circuit R ι m) (body : Circuit R (Sum ι (Fin m)) o) (env : ι → ℕ) :
    multDepth (.bind producer body) env =
      multDepth body (Sum.elim env (multDepth producer env)) := rfl

@[simp] theorem multDepth_input {R : Type u} {ι : Type v} (i : ι) (env : ι → ℕ) :
    multDepth (input (R := R) i) env = fun _ => env i := rfl

theorem multDepth_relabel {R : Type u} {ι : Type v} {m : ℕ} (c : Circuit R ι m) :
    ∀ {κ : Type z} (f : ι → κ) (env : κ → ℕ),
      multDepth (relabel f c) env = multDepth c (env ∘ f) := by
  induction c with
  | wire g => intro κ f env; rfl
  | const r => intro κ f env; rfl
  | add left right ihl ihr =>
      intro κ f env
      simp only [relabel, multDepth_add, ihl, ihr]
  | sub left right ihl ihr =>
      intro κ f env
      simp only [relabel, multDepth_sub, ihl, ihr]
  | mul left right ihl ihr =>
      intro κ f env
      simp only [relabel, multDepth_mul, ihl, ihr]
  | neg p ih => intro κ f env; simp only [relabel, multDepth_neg, ih]
  | scale r p ih => intro κ f env; simp only [relabel, multDepth_scale, ih]
  | fork left right ihl ihr =>
      intro κ f env
      simp only [relabel, multDepth_fork, ihl, ihr]
  | bind producer body ihp ihb =>
      intro κ f env
      simp only [relabel, multDepth_bind, ihb, ihp]
      congr 2
      funext z
      cases z <;> rfl

@[simp] theorem multDepth_liftLeft {R : Type u} {ι : Type v} {κ : Type z} {m : ℕ}
    (c : Circuit R ι m) (left : ι → ℕ) (right : κ → ℕ) :
    c.liftLeft.multDepth (Sum.elim left right) = c.multDepth left := by
  rw [liftLeft, multDepth_relabel]
  congr 2

@[simp] theorem multDepth_rightInput {R : Type u} {ι : Type v} {κ : Type z}
    (i : κ) (left : ι → ℕ) (right : κ → ℕ) :
    (rightInput (R := R) (ι := ι) i).multDepth (Sum.elim left right) 0 = right i := rfl

@[simp] theorem multDepth_comp {R : Type u} {ι : Type v} {m o : ℕ}
    (first : Circuit R ι m) (second : Circuit R (Fin m) o) (env : ι → ℕ) :
    multDepth (comp first second) env = multDepth second (multDepth first env) := by
  rw [comp, multDepth_bind, multDepth_relabel]
  congr 2

/-- Depth is monotone in the input depths. -/
theorem multDepth_mono {R : Type u} {ι : Type v} {m : ℕ} (c : Circuit R ι m) :
    ∀ {env₁ env₂ : ι → ℕ}, (∀ i, env₁ i ≤ env₂ i) →
      ∀ j, multDepth c env₁ j ≤ multDepth c env₂ j := by
  induction c with
  | wire g => intro env₁ env₂ h j; exact h (g j)
  | const r => intro env₁ env₂ h j; exact le_rfl
  | add left right ihl ihr =>
      intro env₁ env₂ h j
      exact max_le_max (ihl h 0) (ihr h 0)
  | sub left right ihl ihr =>
      intro env₁ env₂ h j
      exact max_le_max (ihl h 0) (ihr h 0)
  | mul left right ihl ihr =>
      intro env₁ env₂ h j
      exact Nat.succ_le_succ (max_le_max (ihl h 0) (ihr h 0))
  | neg p ih => intro env₁ env₂ h j; exact ih h 0
  | scale r p ih => intro env₁ env₂ h j; exact ih h 0
  | fork left right ihl ihr =>
      intro env₁ env₂ h j
      refine Fin.addCases (fun i => ?_) (fun i => ?_) j
      · simpa using ihl h i
      · simpa using ihr h i
  | bind producer body ihp ihb =>
      intro env₁ env₂ h j
      simp only [multDepth_bind]
      refine ihb (fun i => ?_) j
      cases i with
      | inl i => exact h i
      | inr i => exact ihp h i

/-- Multiplicative depth is at most the total multiplication count plus the depth
of the inputs: every path can pass each product gate at most once. -/
theorem multDepth_le_multiplications {R : Type u} {ι : Type v} {m : ℕ}
    (c : Circuit R ι m) :
    ∀ {env : ι → ℕ} {d : ℕ}, (∀ i, env i ≤ d) → ∀ j,
      multDepth c env j ≤ c.gates.multiplications + d := by
  induction c with
  | wire g =>
      intro env d h j
      exact (h (g j)).trans (by omega)
  | const r =>
      intro env d h j
      exact Nat.zero_le _
  | add left right ihl ihr =>
      intro env d h j
      obtain rfl : j = (0 : Fin 1) := Subsingleton.elim j 0
      have hl := ihl h 0
      have hr := ihr h 0
      have hg : (Circuit.add left right).gates.multiplications
          = left.gates.multiplications + right.gates.multiplications := by
        show (left.gates + right.gates + GateCount.adds 1).multiplications = _
        simp only [GateCount.add_multiplications, GateCount.adds_multiplications]
        omega
      simp only [multDepth_add, hg]
      omega
  | sub left right ihl ihr =>
      intro env d h j
      obtain rfl : j = (0 : Fin 1) := Subsingleton.elim j 0
      have hl := ihl h 0
      have hr := ihr h 0
      have hg : (Circuit.sub left right).gates.multiplications
          = left.gates.multiplications + right.gates.multiplications := by
        show (left.gates + right.gates + GateCount.adds 1).multiplications = _
        simp only [GateCount.add_multiplications, GateCount.adds_multiplications]
        omega
      simp only [multDepth_sub, hg]
      omega
  | mul left right ihl ihr =>
      intro env d h j
      obtain rfl : j = (0 : Fin 1) := Subsingleton.elim j 0
      have hl := ihl h 0
      have hr := ihr h 0
      have hg : (Circuit.mul left right).gates.multiplications
          = left.gates.multiplications + right.gates.multiplications + 1 := by
        show (left.gates + right.gates + GateCount.muls 1).multiplications = _
        simp only [GateCount.add_multiplications, GateCount.muls_multiplications]
      simp only [multDepth_mul, hg]
      omega
  | neg p ih =>
      intro env d h j
      obtain rfl : j = (0 : Fin 1) := Subsingleton.elim j 0
      have hp := ih h 0
      have hg : (Circuit.neg p).gates.multiplications
          = p.gates.multiplications := by
        show (p.gates + GateCount.adds 1).multiplications = _
        simp only [GateCount.add_multiplications, GateCount.adds_multiplications]
        omega
      simp only [multDepth_neg, hg]
      omega
  | scale r p ih =>
      intro env d h j
      obtain rfl : j = (0 : Fin 1) := Subsingleton.elim j 0
      have hp := ih h 0
      have hg : (Circuit.scale r p).gates.multiplications
          = p.gates.multiplications := rfl
      simp only [multDepth_scale, hg]
      omega
  | fork left right ihl ihr =>
      intro env d h j
      have hg : (Circuit.fork left right).gates.multiplications
          = left.gates.multiplications + right.gates.multiplications := by
        show (left.gates + right.gates).multiplications = _
        simp only [GateCount.add_multiplications]
      refine Fin.addCases (motive := fun j =>
        multDepth (.fork left right) env j
          ≤ (Circuit.fork left right).gates.multiplications + d) ?_ ?_ j
      · intro i
        have := ihl h i
        simp only [multDepth_fork, Fin.addCases_left, hg]
        omega
      · intro i
        have := ihr h i
        simp only [multDepth_fork, Fin.addCases_right, hg]
        omega
  | bind producer body ihp ihb =>
      intro env d h j
      have hb := ihb (env := Sum.elim env (multDepth producer env))
        (d := producer.gates.multiplications + d)
        (fun i => by
          cases i with
          | inl i => exact (h i).trans (by omega)
          | inr i => exact ihp h i) j
      have hg : (Circuit.bind producer body).gates.multiplications
          = producer.gates.multiplications + body.gates.multiplications := by
        show (producer.gates + body.gates).multiplications = _
        simp only [GateCount.add_multiplications]
      simp only [multDepth_bind, hg]
      omega

end Circuit

/-- The height of a program's `j`-th output when every input sits at depth
zero: the maximum number of nonscalar multiplications on a path to it.  This is
the paper's named height notion; the realization ledgers state their bounds
directly on `Circuit.multDepth`, so this anchor currently has no consumers. -/
def MultiplicationProgram.height {R : Type u} [CommRing R] {ι : Type v} {q m : ℕ}
    (program : MultiplicationProgram R ι q m) (j : Fin q) : ℕ :=
  program.circuit.multDepth (fun _ => 0) j

end FastPoly.Cost
