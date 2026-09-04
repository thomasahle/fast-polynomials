import FastPoly.Cost.PolynomialCircuitNaturality
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Uniform specialization from finitely many free parameters

Construction circuits use `Nat` labels because recursive parameter blocks are easiest to
shift arithmetically.  A degree-`n` public family, however, has exactly `n` preprocessing
keys.  This file connects the two interfaces by extending a vector indexed by `Fin n`
with zeros.

The specialization theorem has the important quantifier order: a program is first proved
correct at the canonical free environment in `MvPolynomial (Fin n) R`; that *same syntax*
is then correct for every key vector in every `R`-algebra.  No property of the current
large-characteristic construction is used here.
-/

namespace FastPoly.Cost

open Polynomial

universe u v w

/-- Extend exactly `n` values to the countable parameter-label space, using zero outside
the public key range. -/
def zeroExtend {A : Type v} [Zero A] {n : ℕ} (key : Fin n → A) : ℕ → A :=
  fun i => if hi : i < n then key ⟨i, hi⟩ else 0

@[simp] theorem zeroExtend_apply_lt {A : Type v} [Zero A] {n i : ℕ}
    (key : Fin n → A) (hi : i < n) :
    zeroExtend key i = key ⟨i, hi⟩ := by
  simp only [zeroExtend, dif_pos hi]

@[simp] theorem zeroExtend_apply_not_lt {A : Type v} [Zero A] {n i : ℕ}
    (key : Fin n → A) (hi : ¬ i < n) :
    zeroExtend key i = 0 := by
  simp only [zeroExtend, dif_neg hi]

@[simp] theorem zeroExtend_apply_fin {A : Type v} [Zero A] {n : ℕ}
    (key : Fin n → A) (i : Fin n) :
    zeroExtend key i = key i := by
  rw [zeroExtend_apply_lt key i.isLt]

/-- The canonical countable circuit environment containing exactly `n` free coordinate
variables and zeros after them. -/
noncomputable def freeParameterEnv (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → MvPolynomial (Fin n) R :=
  zeroExtend MvPolynomial.X

/-- Evaluation of the free environment is precisely zero-extension of the chosen key
vector. -/
theorem aeval_freeParameterEnv {R : Type u} {B : Type w}
    [CommRing R] [CommRing B] [Algebra R B] {n : ℕ} (key : Fin n → B) :
    (fun i => MvPolynomial.aeval key (freeParameterEnv R n i)) = zeroExtend key := by
  funext i
  by_cases hi : i < n
  · simp only [freeParameterEnv, zeroExtend_apply_lt _ hi, MvPolynomial.aeval_X]
  · simp only [freeParameterEnv, zeroExtend_apply_not_lt _ hi, map_zero]

/-- A fixed polynomial-input program proved correct over free coordinates realizes,
without any change of syntax or cost, the corresponding family over every finite key
vector in an arbitrary target algebra. -/
theorem MultiplicationProgram.realizesFamily_of_free
    {R : Type u} {B : Type w} [CommRing R] [CommRing B] [Algebra R B]
    {n q m : ℕ} (program : MultiplicationProgram R PolyInput q m)
    (output : Fin q → (MvPolynomial (Fin n) R)[X])
    (h : program.RealizesAt (polyEnv (freeParameterEnv R n)) output) :
    program.RealizesFamily
      (fun key : Fin n → B => polyEnv (zeroExtend key))
      (fun key i =>
        Polynomial.mapAlgHom (MvPolynomial.aeval key) (output i)) := by
  intro key
  have hmap := MultiplicationProgram.RealizesAt.map h
    (Polynomial.mapAlgHom (MvPolynomial.aeval key))
  rw [polyEnv_map] at hmap
  rw [aeval_freeParameterEnv] at hmap
  exact hmap

/-! ## Four-output convenience wrapper for the present construction family -/

/-- The output order of a joint pair program: the two pair components followed by its
recorded quadratic and quartic. -/
def jointPairOutputs {A : Type v} (T₁ T₂ H₂ H₄ : A) : Fin 4 → A :=
  Fin.cases T₁ (Fin.cases T₂ (Fin.cases H₂ (fun _ => H₄)))

@[simp] theorem jointPairOutputs_zero {A : Type v} (T₁ T₂ H₂ H₄ : A) :
    jointPairOutputs T₁ T₂ H₂ H₄ 0 = T₁ := rfl

@[simp] theorem jointPairOutputs_one {A : Type v} (T₁ T₂ H₂ H₄ : A) :
    jointPairOutputs T₁ T₂ H₂ H₄ 1 = T₂ := rfl

@[simp] theorem jointPairOutputs_two {A : Type v} (T₁ T₂ H₂ H₄ : A) :
    jointPairOutputs T₁ T₂ H₂ H₄ 2 = H₂ := rfl

@[simp] theorem jointPairOutputs_three {A : Type v} (T₁ T₂ H₂ H₄ : A) :
    jointPairOutputs T₁ T₂ H₂ H₄ 3 = H₄ := rfl

namespace JointPairProgram

/-- Finite-key uniform semantics for the current four-output payload.  This is a thin
specialization of the construction-neutral `MultiplicationProgram.RealizesFamily`.
Unlike the older `Nat`-family convenience predicate, it states that there are exactly
`n` preprocessing keys. -/
def RealizesFiniteFamily {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (program : JointPairProgram R m)
    (T₁ T₂ H₂ H₄ : (Fin n → A) → A[X]) : Prop :=
  MultiplicationProgram.RealizesFamily program
    (fun key => polyEnv (zeroExtend key))
    (fun key => jointPairOutputs (T₁ key) (T₂ key) (H₂ key) (H₄ key))

/-- The conjunction-style pointwise predicate is exactly the generic four-output
equation. -/
theorem realizesAt_iff {R : Type u} {A : Type w}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    (program : JointPairProgram R m) (theta : ℕ → A)
    (T₁ T₂ H₂ H₄ : A[X]) :
    program.RealizesAt theta T₁ T₂ H₂ H₄ ↔
      MultiplicationProgram.RealizesAt program (polyEnv theta)
        (jointPairOutputs T₁ T₂ H₂ H₄) := by
  constructor
  · intro h
    funext i
    exact Fin.cases h.1
      (Fin.cases h.2.1 (Fin.cases h.2.2.1 (fun j => by
        have hj : j = 0 := Fin.eq_zero j
        subst j
        exact h.2.2.2))) i
  · intro h
    exact ⟨congrFun h 0, congrFun h 1, congrFun h 2, congrFun h 3⟩

private theorem map_jointPairOutputs {A : Type v} {B : Type w} (f : A → B)
    (T₁ T₂ H₂ H₄ : A) :
    (fun i => f (jointPairOutputs T₁ T₂ H₂ H₄ i)) =
      jointPairOutputs (f T₁) (f T₂) (f H₂) (f H₄) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun j => by
    have hj : j = 0 := Fin.eq_zero j
    subst j
    rfl))) i

/-- A joint pair program certified once at the free `n`-parameter environment has
uniform finite-key semantics after every specialization. -/
theorem realizesFiniteFamily_of_free
    {R : Type u} {B : Type w} [CommRing R] [CommRing B] [Algebra R B]
    {n m : ℕ} (program : JointPairProgram R m)
    (T₁ T₂ H₂ H₄ : (MvPolynomial (Fin n) R)[X])
    (h : program.RealizesAt (freeParameterEnv R n) T₁ T₂ H₂ H₄) :
    program.RealizesFiniteFamily
      (fun key : Fin n → B =>
        Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) T₁)
      (fun key : Fin n → B =>
        Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) T₂)
      (fun key : Fin n → B =>
        Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) H₂)
      (fun key : Fin n → B =>
        Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) H₄) := by
  rw [realizesAt_iff] at h
  have hfamily := MultiplicationProgram.realizesFamily_of_free (B := B) program
    (jointPairOutputs T₁ T₂ H₂ H₄) h
  intro key
  have hk := hfamily key
  change MultiplicationProgram.RealizesAt program (polyEnv (zeroExtend key))
    (fun i => Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key)
      (jointPairOutputs T₁ T₂ H₂ H₄ i)) at hk
  change MultiplicationProgram.RealizesAt program (polyEnv (zeroExtend key))
    (jointPairOutputs
      (Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) T₁)
      (Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) T₂)
      (Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) H₂)
      (Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) H₄))
  rw [map_jointPairOutputs] at hk
  exact hk

end JointPairProgram

end FastPoly.Cost
