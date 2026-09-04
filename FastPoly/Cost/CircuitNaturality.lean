import FastPoly.Cost.MultiplicationProgram
import Mathlib.Algebra.Algebra.Hom

/-!
# Naturality of circuit evaluation

An arithmetic circuit over `R` commutes with every morphism of `R`-algebras.  This is
the specialization principle for uniform circuit theorems: prove a fixed program over
a free parameter algebra once, then evaluate those parameters in any target algebra
without changing the syntax or its gate count.
-/

namespace FastPoly.Cost

universe u v w z

namespace Circuit

/-- Applying an `R`-algebra homomorphism after evaluating a circuit is the same as
applying it to every input first. -/
theorem eval_algHom {R : Type u} {A : Type w} {B : Type z}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : ∀ {ι : Type v} {q : ℕ} (c : Circuit R ι q) (env : ι → A),
      (fun i => f (c.eval env i)) = c.eval (fun input => f (env input)) := by
  intro ι q c
  induction c with
  | wire g => intro env; rfl
  | const r =>
      intro env
      funext i
      exact f.commutes r
  | add left right ihLeft ihRight =>
      intro env
      funext i
      simp only [eval_add, map_add]
      rw [congrFun (ihLeft env) 0, congrFun (ihRight env) 0]
  | sub left right ihLeft ihRight =>
      intro env
      funext i
      simp only [eval_sub, map_sub]
      rw [congrFun (ihLeft env) 0, congrFun (ihRight env) 0]
  | mul left right ihLeft ihRight =>
      intro env
      funext i
      simp only [eval_mul, map_mul]
      rw [congrFun (ihLeft env) 0, congrFun (ihRight env) 0]
  | neg p ih =>
      intro env
      funext i
      simp only [eval_neg, map_neg]
      rw [congrFun (ih env) 0]
  | scale r p ih =>
      intro env
      funext i
      simp only [eval_scale, map_mul, f.commutes]
      rw [congrFun (ih env) 0]
  | fork left right ihLeft ihRight =>
      intro env
      simp only [eval_fork]
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [Fin.addCases_left] using congrFun (ihLeft env) j
      · intro j
        simpa only [Fin.addCases_right] using congrFun (ihRight env) j
  | bind producer body ihProducer ihBody =>
      intro env
      rw [eval_bind, eval_bind, ihBody]
      congr 1
      funext input
      cases input with
      | inl i => rfl
      | inr i => exact congrFun (ihProducer env) i

end Circuit

namespace MultiplicationProgram

/-- A pointwise semantic equation specializes along any `R`-algebra homomorphism,
while retaining exactly the same program. -/
theorem RealizesAt.map {R : Type u} {A : Type w} {B : Type z}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    {ι : Type v} {q m : ℕ} {program : MultiplicationProgram R ι q m}
    {env : ι → A} {output : Fin q → A}
    (h : program.RealizesAt env output) (f : A →ₐ[R] B) :
    program.RealizesAt (fun input => f (env input)) (fun i => f (output i)) := by
  rw [RealizesAt] at h ⊢
  rw [← h]
  exact (Circuit.eval_algHom f program.circuit env).symm

end MultiplicationProgram

end FastPoly.Cost
