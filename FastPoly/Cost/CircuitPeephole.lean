import FastPoly.Cost.Circuit

/-!
# Typed replacement of shared circuit producers

These combinators replace the producer at one or two leading `bind` nodes while
retaining the original continuation.  They are useful for local schedule peepholes:
the optimized producer is explicit syntax, and the decoder-facing continuation is
reused unchanged.
-/

namespace FastPoly.Cost

universe u v w

namespace Circuit

private theorem funext_fin_two {B : Type*} (f g : Fin 2 → B)
    (h₀ : f 0 = g 0) (h₁ : f 1 = g 1) : f = g := by
  funext i
  by_cases hi : i = 0
  · subst i
    exact h₀
  have hi : i = 1 := Fin.ext (by omega)
  subst i
  exact h₁

/-- Replace the producer of a leading `bind` when its output arity matches `new`.
Circuits that are not a leading bind, or whose producer has another arity, are left
unchanged. -/
def replaceTopProducer {R : Type u} {iota : Type v} {m o : ℕ}
    (new : Circuit R iota m) : Circuit R iota o → Circuit R iota o
  | .bind (m := q) producer body =>
      if h : q = m then
        .bind new (h ▸ body)
      else
        .bind producer body
  | circuit => circuit

/-- Replace the producers of two consecutive leading binds. -/
def replaceFirstTwoProducers {R : Type u} {iota : Type v} {m n o : ℕ}
    (first : Circuit R iota m) (second : Circuit R (Sum iota (Fin m)) n) :
    Circuit R iota o → Circuit R iota o
  | .bind (m := q) producer body =>
      if h : q = m then
        let body' := h ▸ body
        .bind first (replaceTopProducer second body')
      else
        .bind producer body
  | circuit => circuit

@[simp] theorem gates_replaceTopProducer_bind {R : Type u} {iota : Type v}
    {m o : ℕ} (new producer : Circuit R iota m)
    (body : Circuit R (Sum iota (Fin m)) o) :
    (replaceTopProducer new (.bind producer body)).gates = new.gates + body.gates := by
  simp only [replaceTopProducer, ↓reduceDIte, Circuit.gates_bind]

@[simp] theorem eval_replaceTopProducer_bind {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {iota : Type v} {m o : ℕ}
    (new producer : Circuit R iota m) (body : Circuit R (Sum iota (Fin m)) o)
    (env : iota → A) :
    (replaceTopProducer new (.bind producer body)).eval env =
      body.eval (Sum.elim env (new.eval env)) := by
  simp only [replaceTopProducer, ↓reduceDIte, Circuit.eval_bind]

/-- Replacing a leading producer by a pointwise equivalent producer preserves the
complete continuation. -/
theorem eval_replaceTopProducer_eq_bind {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {iota : Type v} {m o : ℕ}
    (new producer : Circuit R iota m) (body : Circuit R (Sum iota (Fin m)) o)
    (env : iota → A) (hproducer : new.eval env = producer.eval env) :
    (replaceTopProducer new (.bind producer body)).eval env =
      (Circuit.bind producer body).eval env := by
  rw [eval_replaceTopProducer_bind, Circuit.eval_bind, hproducer]

@[simp] theorem gates_replaceFirstTwoProducers_bind_bind {R : Type u}
    {iota : Type v} {m n o : ℕ}
    (first producer₁ : Circuit R iota m)
    (second producer₂ : Circuit R (Sum iota (Fin m)) n)
    (body : Circuit R (Sum (Sum iota (Fin m)) (Fin n)) o) :
    (replaceFirstTwoProducers first second
      (.bind producer₁ (.bind producer₂ body))).gates =
        first.gates + second.gates + body.gates := by
  simp only [replaceFirstTwoProducers, ↓reduceDIte,
    gates_replaceTopProducer_bind, Circuit.gates_bind]
  apply GateCount.ext <;>
    simp only [GateCount.add_additions, GateCount.add_multiplications] <;> omega

@[simp] theorem eval_replaceFirstTwoProducers_bind_bind {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {iota : Type v} {m n o : ℕ}
    (first producer₁ : Circuit R iota m)
    (second producer₂ : Circuit R (Sum iota (Fin m)) n)
    (body : Circuit R (Sum (Sum iota (Fin m)) (Fin n)) o)
    (env : iota → A) :
    (replaceFirstTwoProducers first second
      (.bind producer₁ (.bind producer₂ body))).eval env =
        body.eval
          (Sum.elim (Sum.elim env (first.eval env))
            (second.eval (Sum.elim env (first.eval env)))) := by
  simp only [replaceFirstTwoProducers, ↓reduceDIte,
    eval_replaceTopProducer_bind, Circuit.eval_bind]

/-- Two consecutive producer replacements preserve the complete circuit when both
new producers agree with the corresponding old producer in the environment generated
by the preceding replacement. -/
theorem eval_replaceFirstTwoProducers_eq_bind_bind {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {iota : Type v} {m n o : ℕ}
    (first producer₁ : Circuit R iota m)
    (second producer₂ : Circuit R (Sum iota (Fin m)) n)
    (body : Circuit R (Sum (Sum iota (Fin m)) (Fin n)) o)
    (env : iota → A) (hfirst : first.eval env = producer₁.eval env)
    (hsecond : second.eval (Sum.elim env (first.eval env)) =
      producer₂.eval (Sum.elim env (producer₁.eval env))) :
    (replaceFirstTwoProducers first second
      (Circuit.bind producer₁ (Circuit.bind producer₂ body))).eval env =
        (Circuit.bind producer₁ (Circuit.bind producer₂ body)).eval env := by
  have hsecond' : second.eval (Sum.elim env (producer₁.eval env)) =
      producer₂.eval (Sum.elim env (producer₁.eval env)) := by
    calc
      second.eval (Sum.elim env (producer₁.eval env)) =
          second.eval (Sum.elim env (first.eval env)) := by rw [hfirst]
      _ = producer₂.eval (Sum.elim env (producer₁.eval env)) := hsecond
  rw [eval_replaceFirstTwoProducers_bind_bind, Circuit.eval_bind,
    Circuit.eval_bind, hfirst, hsecond']

/-- Binary-output version of the preceding theorem.  Pair equality is often the
natural semantic interface for a jointly produced pair and avoids exposing its two
coordinates to a large dependent continuation. -/
theorem eval_replaceFirstTwoProducers_eq_bind_bind_two {R : Type u} {A : Type w}
    [CommRing R] [Ring A] [Algebra R A] {iota : Type v} {m o : ℕ}
    (first producer₁ : Circuit R iota m)
    (second producer₂ : Circuit R (Sum iota (Fin m)) 2)
    (body : Circuit R (Sum (Sum iota (Fin m)) (Fin 2)) o)
    (env : iota → A) (hfirst : first.eval env = producer₁.eval env)
    (hsecond :
      (second.eval (Sum.elim env (first.eval env)) 0,
        second.eval (Sum.elim env (first.eval env)) 1) =
      (producer₂.eval (Sum.elim env (producer₁.eval env)) 0,
        producer₂.eval (Sum.elim env (producer₁.eval env)) 1)) :
    (replaceFirstTwoProducers first second
      (Circuit.bind producer₁ (Circuit.bind producer₂ body))).eval env =
        (Circuit.bind producer₁ (Circuit.bind producer₂ body)).eval env := by
  apply eval_replaceFirstTwoProducers_eq_bind_bind first producer₁ second producer₂
    body env hfirst
  apply funext_fin_two
  · exact congrArg Prod.fst hsecond
  exact congrArg Prod.snd hsecond

end Circuit

end FastPoly.Cost
