import FastPoly.Cost.FreeSpecialization

/-!
# Fixed programs for complete polynomial constructions

The recursive invariant produces a shared pair in the first two outputs of a
`JointPairProgram`.  One final product forms `x T¹ + T²`.  Even degrees are then obtained
by the equally literal lift `x Q + c`.  This file implements both operations on the fixed
program syntax, so their costs and semantics cannot become detached.

Everything here is characteristic-independent and only assumes the generic circuit
interface.  In particular, a later binary-field construction may use the same final
combine and even-lift programs.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

/-- A fixed one-output polynomial circuit with an exact nonscalar-multiplication count. -/
abbrev PolynomialProgram (R : Type u) [CommRing R] (multiplications : ℕ) :=
  MultiplicationProgram R PolyInput 1 multiplications

/-- Package one value as a one-output vector. -/
def oneOutput {A : Type v} (P : A) : Fin 1 → A := fun _ => P

namespace PolynomialProgram

/-- Pointwise symbolic semantics of a complete polynomial program. -/
def RealizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    (program : PolynomialProgram R m) (theta : ℕ → A) (P : A[X]) : Prop :=
  MultiplicationProgram.RealizesAt program (polyEnv theta) (oneOutput P)

/-- Uniform semantics over exactly `n` preprocessing keys. -/
def RealizesFiniteFamily {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (program : PolynomialProgram R m) (P : (Fin n → A) → A[X]) : Prop :=
  MultiplicationProgram.RealizesFamily program
    (fun key => polyEnv (zeroExtend key)) (fun key => oneOutput (P key))

theorem realizesAt_iff {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    (program : PolynomialProgram R m) (theta : ℕ → A) (P : A[X]) :
    program.RealizesAt theta P ↔ program.circuit.eval (polyEnv theta) 0 = P := by
  constructor
  · intro h
    exact congrFun h 0
  · intro h
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    exact h

private theorem map_oneOutput {A B : Type*} (f : A → B) (P : A) :
    (fun i => f (oneOutput P i)) = oneOutput (f P) := by
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-- A complete polynomial program certified at the canonical free environment works,
unchanged, for every vector of exactly `n` keys. -/
theorem realizesFiniteFamily_of_free
    {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]
    {n m : ℕ} (program : PolynomialProgram R m)
    (P : (MvPolynomial (Fin n) R)[X])
    (h : program.RealizesAt (freeParameterEnv R n) P) :
    program.RealizesFiniteFamily
      (fun key : Fin n → B =>
        Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) P) := by
  have hfamily := MultiplicationProgram.realizesFamily_of_free (B := B) program
    (oneOutput P) h
  intro key
  have hk := hfamily key
  change MultiplicationProgram.RealizesAt program (polyEnv (zeroExtend key))
    (fun i => Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key)
      (oneOutput P i)) at hk
  change MultiplicationProgram.RealizesAt program (polyEnv (zeroExtend key))
    (oneOutput (Polynomial.mapAlgHom (MvPolynomial.aeval (R := R) key) P))
  rw [map_oneOutput] at hk
  exact hk

/-! ## Combining two outputs -/

/-- The one-product body `x T¹ + T²`, with both source-output positions explicit.
The source may carry any finite payload; no quadratic/quartic layout is assumed. -/
def combineOutputsBody {R : Type u} {q : ℕ} (first second : Fin q) :
    Circuit R (Sum PolyInput (Fin q)) 1 :=
  .add
    (.mul Circuit.polyX.liftLeft
      (Circuit.rightInput (R := R) (i := first)))
    (Circuit.rightInput (R := R) (i := second))

@[simp] theorem gates_combineOutputsBody {R : Type u} {q : ℕ}
    (first second : Fin q) :
    (combineOutputsBody (R := R) first second).gates = GateCount.of 1 1 := by
  apply GateCount.ext <;> rfl

/-- Bind an arbitrary finite-output program once and combine two of its outputs with one
further product. -/
def ofOutputs {R : Type u} [CommRing R] {q m : ℕ}
    (source : MultiplicationProgram R PolyInput q m) (first second : Fin q) :
    PolynomialProgram R (m + 1) where
  circuit := .bind source.circuit (combineOutputsBody first second)
  multiplication_count := by
    rw [Circuit.gates_bind, GateCount.add_multiplications,
      source.multiplication_count, gates_combineOutputsBody,
      GateCount.of_multiplications]

@[simp] theorem eval_ofOutputs {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {q m : ℕ}
    (source : MultiplicationProgram R PolyInput q m) (first second : Fin q)
    (theta : ℕ → A) :
    (ofOutputs source first second).circuit.eval (polyEnv theta) 0 =
      X * source.circuit.eval (polyEnv theta) first +
        source.circuit.eval (polyEnv theta) second := by
  rfl

/-- Combining two retained outputs contributes exactly one addition as well as one
multiplication. -/
theorem additions_ofOutputs {R : Type u} [CommRing R] {q m : ℕ}
    (source : MultiplicationProgram R PolyInput q m) (first second : Fin q) :
    (ofOutputs source first second).additions = source.additions + 1 := by
  simp only [MultiplicationProgram.additions, ofOutputs, Circuit.gates_bind,
    GateCount.add_additions, gates_combineOutputsBody, GateCount.of_additions]

/-- Combining two positions preserves finite-key uniformity for an arbitrary payload. -/
theorem ofOutputs_realizesFiniteFamily {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {n q m : ℕ}
    (source : MultiplicationProgram R PolyInput q m)
    (output : (Fin n → A) → Fin q → A[X])
    (h : source.RealizesFamily
      (fun key => polyEnv (zeroExtend key)) output)
    (first second : Fin q) :
    (ofOutputs source first second).RealizesFiniteFamily
      (fun key => X * output key first + output key second) := by
  intro key
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rw [eval_ofOutputs, congrFun (h key) first, congrFun (h key) second]
  rfl

/-! ### Current-family wrapper -/

/-- The current pair payload stores its two components in positions zero and one. -/
def combinedPairBody {R : Type u} : Circuit R (Sum PolyInput (Fin 4)) 1 :=
  combineOutputsBody 0 1

@[simp] theorem gates_combinedPairBody {R : Type u} :
    (combinedPairBody (R := R)).gates = GateCount.of 1 1 :=
  gates_combineOutputsBody 0 1

/-- Bind a current-family joint pair once and complete its polynomial. -/
def ofJointPair {R : Type u} [CommRing R] {m : ℕ}
    (source : JointPairProgram R m) : PolynomialProgram R (m + 1) :=
  ofOutputs source 0 1

@[simp] theorem eval_ofJointPair {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    (source : JointPairProgram R m) (theta : ℕ → A) :
    (ofJointPair source).circuit.eval (polyEnv theta) 0 =
      X * source.circuit.eval (polyEnv theta) 0 +
        source.circuit.eval (polyEnv theta) 1 :=
  eval_ofOutputs source 0 1 theta

/-- Completing a pointwise realized pair realizes exactly its combined polynomial. -/
theorem ofJointPair_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    {source : JointPairProgram R m} {theta : ℕ → A}
    {T₁ T₂ H₂ H₄ : A[X]}
    (h : source.RealizesAt theta T₁ T₂ H₂ H₄) :
    (ofJointPair source).RealizesAt theta (X * T₁ + T₂) := by
  rw [realizesAt_iff, eval_ofJointPair, h.1, h.2.1]

/-- The final pair combination contributes exactly one addition as well as one
multiplication. -/
theorem additions_ofJointPair {R : Type u} [CommRing R] {m : ℕ}
    (source : JointPairProgram R m) :
    (ofJointPair source).additions = source.additions + 1 :=
  additions_ofOutputs source 0 1

/-- Uniform current-family pair semantics pass directly through the generic output
combiner. -/
theorem ofJointPair_realizesFiniteFamily {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (source : JointPairProgram R m)
    (T₁ T₂ H₂ H₄ : (Fin n → A) → A[X])
    (h : source.RealizesFiniteFamily T₁ T₂ H₂ H₄) :
    (ofJointPair source).RealizesFiniteFamily
      (fun key => X * T₁ key + T₂ key) := by
  have hgeneric := ofOutputs_realizesFiniteFamily source
    (fun key => jointPairOutputs (T₁ key) (T₂ key) (H₂ key) (H₄ key)) h 0 1
  simpa only [ofJointPair, jointPairOutputs_zero, jointPairOutputs_one] using hgeneric

/-! ## The even-degree lift -/

/-- The one-product body `x Q + c`, where `c` is read from `freshIndex`. -/
def evenLiftBody {R : Type u} (freshIndex : ℕ) :
    Circuit R (Sum PolyInput (Fin 1)) 1 :=
  .add
    (.mul Circuit.polyX.liftLeft
      (Circuit.rightInput (R := R) (i := (0 : Fin 1))))
    (Circuit.polyParameter freshIndex).liftLeft

@[simp] theorem gates_evenLiftBody {R : Type u} (freshIndex : ℕ) :
    (evenLiftBody (R := R) freshIndex).gates = GateCount.of 1 1 := by
  apply GateCount.ext <;> rfl

/-- Lift a complete degree-`n` program to `x Q + c` with one new multiplication. -/
def evenLift {R : Type u} [CommRing R] {m : ℕ}
    (source : PolynomialProgram R m) (freshIndex : ℕ) :
    PolynomialProgram R (m + 1) where
  circuit := .bind source.circuit (evenLiftBody freshIndex)
  multiplication_count := by
    rw [Circuit.gates_bind, GateCount.add_multiplications,
      source.multiplication_count, gates_evenLiftBody,
      GateCount.of_multiplications]

@[simp] theorem eval_evenLift {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    (source : PolynomialProgram R m) (freshIndex : ℕ) (theta : ℕ → A) :
    (evenLift source freshIndex).circuit.eval (polyEnv theta) 0 =
      X * source.circuit.eval (polyEnv theta) 0 + C (theta freshIndex) := by
  rfl

theorem evenLift_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {m : ℕ}
    {source : PolynomialProgram R m} {theta : ℕ → A} {Q : A[X]}
    (h : source.RealizesAt theta Q) (freshIndex : ℕ) :
    (evenLift source freshIndex).RealizesAt theta
      (X * Q + C (theta freshIndex)) := by
  rw [realizesAt_iff, eval_evenLift, (realizesAt_iff source theta Q).mp h]

/-- The even lift also contributes exactly one addition. -/
theorem additions_evenLift {R : Type u} [CommRing R] {m : ℕ}
    (source : PolynomialProgram R m) (freshIndex : ℕ) :
    (evenLift source freshIndex).additions = source.additions + 1 := by
  simp only [MultiplicationProgram.additions, evenLift, Circuit.gates_bind,
    GateCount.add_additions, gates_evenLiftBody, GateCount.of_additions]

/-- The even lift preserves finite-key uniformity when the source is already certified
in the same full key environment.  Taking `fresh : Fin n` makes that ambient-ring
requirement explicit. -/
theorem evenLift_realizesFiniteFamily {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] {n m : ℕ}
    (source : PolynomialProgram R m) (P : (Fin n → A) → A[X])
    (h : source.RealizesFiniteFamily P) (fresh : Fin n) :
    (evenLift source fresh).RealizesFiniteFamily
      (fun key => X * P key + C (key fresh)) := by
  intro key
  have hpoint : source.RealizesAt (zeroExtend key) (P key) := h key
  have hlift := evenLift_realizesAt hpoint fresh
  simpa only [zeroExtend_apply_fin] using hlift

/-! ## Affine and quadratic endpoints -/

/-- The monic affine family `x + a₀`. -/
def linear {R : Type u} [CommRing R] : PolynomialProgram R 0 where
  circuit := .add Circuit.polyX (Circuit.polyParameter 0)
  multiplication_count := rfl

@[simp] theorem eval_linear {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (linear (R := R)).circuit.eval (polyEnv theta) 0 = X + C (theta 0) := rfl

@[simp] theorem additions_linear {R : Type u} [CommRing R] :
    (linear (R := R)).additions = 1 := rfl

theorem linear_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (linear (R := R)).RealizesAt theta (X + C (theta 0)) := by
  rw [realizesAt_iff, eval_linear]

/-- One fixed affine program for every one-key vector. -/
theorem linear_realizesFiniteFamily {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] :
    (linear (R := R)).RealizesFiniteFamily
      (fun key : Fin 1 → A => X + C (key 0)) := by
  intro key
  have h := linear_realizesAt (R := R) (zeroExtend key)
  simpa only [zeroExtend_apply_fin] using h

/-- The monic quadratic family `x(x+a₁)+a₀`. -/
def quadratic {R : Type u} [CommRing R] : PolynomialProgram R 1 where
  circuit := .add
    (.mul Circuit.polyX (.add Circuit.polyX (Circuit.polyParameter 1)))
    (Circuit.polyParameter 0)
  multiplication_count := rfl

@[simp] theorem eval_quadratic {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (quadratic (R := R)).circuit.eval (polyEnv theta) 0 =
      X * (X + C (theta 1)) + C (theta 0) := rfl

@[simp] theorem additions_quadratic {R : Type u} [CommRing R] :
    (quadratic (R := R)).additions = 2 := rfl

theorem quadratic_realizesAt {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] (theta : ℕ → A) :
    (quadratic (R := R)).RealizesAt theta
      (X * (X + C (theta 1)) + C (theta 0)) := by
  rw [realizesAt_iff, eval_quadratic]

/-- One fixed quadratic program for every two-key vector. -/
theorem quadratic_realizesFiniteFamily {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] [Algebra R A] :
    (quadratic (R := R)).RealizesFiniteFamily
      (fun key : Fin 2 → A => X * (X + C (key 1)) + C (key 0)) := by
  intro key
  have h := quadratic_realizesAt (R := R) (zeroExtend key)
  simpa only [zeroExtend_apply_fin] using h

end PolynomialProgram

end FastPoly.Cost
