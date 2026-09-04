import FastPoly.Cost.Instantiate

/-!
# Composition of joint realizations

The master induction builds a new pair by binding the smaller realized pair and then
running a branch-local circuit.  This file packages that operation once.  Sharing is
semantic rather than inferred: the source circuit occurs exactly once under `bind`, so
both multiplication and addition counts belong to the circuit producing the returned
polynomials.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace JointPairRealization

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Extend a realized pair by one circuit whose body may use all four old outputs.
The four semantic equations describe the new pair and recorded powers; the local
multiplication equation counts only the body, because the producer is bound once. -/
def extend {θ : ℕ → A} {T₁ T₂ H₂ H₄ : A[X]} {m branchMuls : ℕ}
    (source : JointPairRealization (R := R) θ T₁ T₂ H₂ H₄ m)
    (body : Circuit R (Sum PolyInput (Fin 4)) 4)
    (U₁ U₂ K₂ K₄ : A[X])
    (eval₁ : body.eval (Sum.elim (polyEnv θ) (source.circuit.eval (polyEnv θ))) 0 = U₁)
    (eval₂ : body.eval (Sum.elim (polyEnv θ) (source.circuit.eval (polyEnv θ))) 1 = U₂)
    (evalK₂ : body.eval (Sum.elim (polyEnv θ) (source.circuit.eval (polyEnv θ))) 2 = K₂)
    (evalK₄ : body.eval (Sum.elim (polyEnv θ) (source.circuit.eval (polyEnv θ))) 3 = K₄)
    (local_count : body.gates.multiplications = branchMuls) :
    JointPairRealization (R := R) θ U₁ U₂ K₂ K₄ (m + branchMuls) where
  circuit := .bind source.circuit body
  eval₁ := by
    rw [Circuit.eval_bind, eval₁]
  eval₂ := by
    rw [Circuit.eval_bind, eval₂]
  evalH₂ := by
    rw [Circuit.eval_bind, evalK₂]
  evalH₄ := by
    rw [Circuit.eval_bind, evalK₄]
  multiplication_count := by
    rw [Circuit.gates_bind, GateCount.add_multiplications,
      source.multiplication_count, local_count]

end JointPairRealization

namespace Circuit

/-- Select an output of an earlier producer from inside one further nested binding. -/
def priorOutput {R : Type u} {ι : Type v} {m n : ℕ} (i : Fin m) :
    Circuit R (Sum (Sum ι (Fin m)) (Fin n)) 1 :=
  Circuit.input (.inl (.inr i))

@[simp] theorem eval_priorOutput {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} {m n : ℕ}
    (i : Fin m) (left : ι → A) (middle : Fin m → A) (right : Fin n → A) :
    (priorOutput (R := R) i).eval
        (Sum.elim (Sum.elim left middle) right) 0 = middle i :=
  rfl

@[simp] theorem gates_priorOutput {R : Type u} {ι : Type v} {m n : ℕ} (i : Fin m) :
    (priorOutput (R := R) (ι := ι) (n := n) i).gates = 0 :=
  rfl

/-- Select an output two bindings back.  This is useful when a branch first binds its
recorded power tower, then an auxiliary gadget, and finally an outer shell. -/
def grandOutput {R : Type u} {ι : Type v} {m n o : ℕ} (i : Fin m) :
    Circuit R (Sum (Sum (Sum ι (Fin m)) (Fin n)) (Fin o)) 1 :=
  Circuit.input (.inl (.inl (.inr i)))

@[simp] theorem eval_grandOutput {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} {m n o : ℕ}
    (i : Fin m) (first : ι → A) (second : Fin m → A) (third : Fin n → A)
    (fourth : Fin o → A) :
    (grandOutput (R := R) i).eval
        (Sum.elim (Sum.elim (Sum.elim first second) third) fourth) 0 = second i :=
  rfl

@[simp] theorem gates_grandOutput {R : Type u} {ι : Type v} {m n o : ℕ} (i : Fin m) :
    (grandOutput (R := R) (ι := ι) (n := n) (o := o) i).gates = 0 :=
  rfl

end Circuit

end FastPoly.Cost
