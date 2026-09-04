import FastPoly.Cost.RelativeRealization
import FastPoly.Cost.PowerTowerCircuit
import FastPoly.Height.RealizationDepth

/-!
# Parallel semantic realization of the `8k+7` outer step

The `8k+7` branch binds the smaller realized pair once, computes two independent odd
gadgets from the same recorded powers, and adds two difference-of-squares shells.  Its
last two fresh coordinates are `s = a+b` and `d = b-a`: sharing the forms `S₃+S₂` and
`S₃-S₂` makes the outer body cost six additions instead of eight.  The
`8k+3` branch is genuinely sequential because its second gadget consumes the crown
quartic produced by its first; that circuit lives in `RealizationOuterSequential`.

All identities below hold over an arbitrary commutative ring.  In particular this layer
can be reused by a future characteristic-two construction with different gadgets.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace Outer

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private abbrev SourceInput := Sum PolyInput (Fin 4)
private abbrev AuxInput := Sum SourceInput (Fin 2)
private abbrev FormInput := Sum AuxInput (Fin 2)

/-- Compute two conditionally realized gadgets in parallel after the source has been
bound.  Their only sharing is through the four source wires, so their local costs add. -/
def auxPair (left right : Circuit R SourceInput 1) : Circuit R SourceInput 2 :=
  .fork left right

private def oldParameter (i : ℕ) : Circuit R AuxInput 1 :=
  (Circuit.polyParameter (R := R) i).liftLeft.liftLeft

/-- The two common linear forms, produced once and reused by both outputs. -/
def eightSevenForms : Circuit R AuxInput 2 :=
  let S₂ := Circuit.rightInput (R := R) (ι := SourceInput) (0 : Fin 2)
  let S₃ := Circuit.rightInput (R := R) (ι := SourceInput) (1 : Fin 2)
  Circuit.pair (.add S₃ S₂) (.sub S₃ S₂)

/-- Local body of the `8k+7` step.  The fresh inputs are the already-reparameterized
coordinates `s = a+b` and `d = b-a`; no shifted auxiliary polynomial is materialized. -/
def eightSevenBody (sIndex dIndex : ℕ) : Circuit R AuxInput 4 :=
  .bind eightSevenForms <|
    let u := Circuit.rightInput (R := R) (ι := AuxInput) (0 : Fin 2)
    let v := Circuit.rightInput (R := R) (ι := AuxInput) (1 : Fin 2)
    let T₁' := Circuit.grandOutput (R := R) (ι := PolyInput)
      (n := 2) (o := 2) (0 : Fin 4)
    let T₂' := Circuit.grandOutput (R := R) (ι := PolyInput)
      (n := 2) (o := 2) (1 : Fin 4)
    let H₂ := Circuit.grandOutput (R := R) (ι := PolyInput)
      (n := 2) (o := 2) (2 : Fin 4)
    let H₄ := Circuit.grandOutput (R := R) (ι := PolyInput)
      (n := 2) (o := 2) (3 : Fin 4)
    let old (p : Circuit R AuxInput 1) := p.liftLeft
    let T₁ := .add (.mul u v) T₁'
    let T₂ := .add (.mul (.add u (old (oldParameter sIndex)))
      (.add v (old (oldParameter dIndex)))) T₂'
    Circuit.pairWithPowers T₁ T₂ H₂ H₄

/-- The analogous full circuit for the `8k+7` body. -/
def eightSevenCircuit {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]}
    {sourceMuls secondMuls thirdMuls : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ sourceMuls)
    (second : RelativeRealization (R := R) θ source.circuit S₂ secondMuls)
    (third : RelativeRealization (R := R) θ source.circuit S₃ thirdMuls)
    (sIndex dIndex : ℕ) : Circuit R PolyInput 4 :=
  .bind source.circuit <|
    .bind (auxPair second.circuit third.circuit) (eightSevenBody sIndex dIndex)

private noncomputable def sourceEnv {θ : ℕ → A} {S₁ S₂ H₂ H₄ : A[X]} {m : ℕ}
    (source : JointPairRealization (R := R) θ S₁ S₂ H₂ H₄ m) :
    SourceInput → A[X] :=
  Sum.elim (polyEnv θ) (source.circuit.eval (polyEnv θ))

private noncomputable def auxEnv {θ : ℕ → A} {S₁ S₂ H₂ H₄ Q₂ Q₃ : A[X]}
    {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ S₂ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit Q₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit Q₃ m₃) :
    AuxInput → A[X] :=
  Sum.elim (sourceEnv source)
    ((auxPair second.circuit third.circuit).eval (sourceEnv source))

@[simp] theorem eval_auxPair_zero {θ : ℕ → A} {S₁ S₂ H₂ H₄ Q₂ Q₃ : A[X]}
    {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ S₂ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit Q₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit Q₃ m₃) :
    (auxPair second.circuit third.circuit).eval (sourceEnv source) 0 = Q₂ := by
  rw [auxPair]
  change second.circuit.eval (sourceEnv source) 0 = Q₂
  simpa only [sourceEnv] using second.eval_eq

@[simp] theorem eval_auxPair_one {θ : ℕ → A} {S₁ S₂ H₂ H₄ Q₂ Q₃ : A[X]}
    {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ S₂ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit Q₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit Q₃ m₃) :
    (auxPair second.circuit third.circuit).eval (sourceEnv source) 1 = Q₃ := by
  rw [auxPair]
  change third.circuit.eval (sourceEnv source) 0 = Q₃
  simpa only [sourceEnv] using third.eval_eq

@[simp] private theorem eval_auxEnv_second
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃) :
    (Circuit.rightInput (R := R) (ι := SourceInput) (0 : Fin 2)).eval
        (auxEnv source second third) 0 = S₂ := by
  rw [auxEnv, Circuit.eval_rightInput, eval_auxPair_zero]

@[simp] private theorem eval_auxEnv_third
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃) :
    (Circuit.rightInput (R := R) (ι := SourceInput) (1 : Fin 2)).eval
        (auxEnv source second third) 0 = S₃ := by
  rw [auxEnv, Circuit.eval_rightInput, eval_auxPair_one]

@[simp] private theorem eval_auxEnv_source_zero
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃) :
    (Circuit.priorOutput (R := R) (ι := PolyInput) (n := 2) (0 : Fin 4)).eval
        (auxEnv source second third) 0 = S₁ := by
  rw [auxEnv, sourceEnv, Circuit.eval_priorOutput, source.eval₁]

@[simp] private theorem eval_auxEnv_source_one
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃) :
    (Circuit.priorOutput (R := R) (ι := PolyInput) (n := 2) (1 : Fin 4)).eval
        (auxEnv source second third) 0 = St₁ := by
  rw [auxEnv, sourceEnv, Circuit.eval_priorOutput, source.eval₂]

@[simp] private theorem eval_auxEnv_parameter
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃) (i : ℕ) :
    (oldParameter (R := R) i).eval (auxEnv source second third) 0 = C (θ i) := by
  rw [oldParameter, auxEnv, Circuit.eval_liftLeft, sourceEnv,
    Circuit.eval_liftLeft, Circuit.eval_polyParameter]

@[simp] private theorem eval_eightSevenForms_zero
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃) :
    (eightSevenForms (R := R)).eval (auxEnv source second third) 0 = S₃ + S₂ := by
  rw [eightSevenForms]
  change
    (Circuit.rightInput (R := R) (ι := SourceInput) (1 : Fin 2)).eval
        (auxEnv source second third) 0 +
      (Circuit.rightInput (R := R) (ι := SourceInput) (0 : Fin 2)).eval
        (auxEnv source second third) 0 = S₃ + S₂
  rw [eval_auxEnv_third, eval_auxEnv_second]

@[simp] private theorem eval_eightSevenForms_one
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃) :
    (eightSevenForms (R := R)).eval (auxEnv source second third) 1 = S₃ - S₂ := by
  rw [eightSevenForms]
  change
    (Circuit.rightInput (R := R) (ι := SourceInput) (1 : Fin 2)).eval
        (auxEnv source second third) 0 -
      (Circuit.rightInput (R := R) (ι := SourceInput) (0 : Fin 2)).eval
        (auxEnv source second third) 0 = S₃ - S₂
  rw [eval_auxEnv_third, eval_auxEnv_second]

@[simp] private theorem eval_formEnv_source
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (i : Fin 4) (forms : Fin 2 → A[X]) :
    (Circuit.grandOutput (R := R) (ι := PolyInput) (n := 2) (o := 2) i).eval
        (Sum.elim (auxEnv source second third) forms) 0 =
      source.circuit.eval (polyEnv θ) i := by
  rfl

@[simp] private theorem eval_formEnv_parameter
    {θ : ℕ → A} {S₁ St₁ H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (i : ℕ) (forms : Fin 2 → A[X]) :
    ((oldParameter (R := R) i).liftLeft : Circuit R FormInput 1).eval
        (Sum.elim (auxEnv source second third) forms) 0 = C (θ i) := by
  rw [Circuit.eval_liftLeft, eval_auxEnv_parameter]

private theorem eval_eightSevenBody_zero
    {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (sIndex dIndex : ℕ) :
  (eightSevenBody (R := R) sIndex dIndex).eval (auxEnv source second third) 0 =
      S₃ * S₃ - S₂ * S₂ + T₁' := by
  simp only [eightSevenBody, Circuit.eval_bind, Circuit.eval_pairWithPowers_zero,
    Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput,
    eval_eightSevenForms_zero, eval_eightSevenForms_one,
    eval_formEnv_source, source.eval₁]
  ring

private theorem eval_eightSevenBody_one
    {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (sIndex dIndex : ℕ) :
  (eightSevenBody (R := R) sIndex dIndex).eval (auxEnv source second third) 1 =
      (S₃ + S₂ + C (θ sIndex)) * (S₃ - S₂ + C (θ dIndex)) + T₂' := by
  simp only [eightSevenBody, Circuit.eval_bind, Circuit.eval_pairWithPowers_one,
    Circuit.eval_add, Circuit.eval_mul, Circuit.eval_rightInput,
    eval_eightSevenForms_zero, eval_eightSevenForms_one,
    eval_formEnv_parameter, eval_formEnv_source, source.eval₂]

private theorem eval_eightSevenBody_two
    {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (sIndex dIndex : ℕ) :
  (eightSevenBody (R := R) sIndex dIndex).eval (auxEnv source second third) 2 = H₂ := by
  simp only [eightSevenBody, Circuit.eval_bind, Circuit.eval_pairWithPowers_two,
    eval_formEnv_source, source.evalH₂]

private theorem eval_eightSevenBody_three
    {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (sIndex dIndex : ℕ) :
  (eightSevenBody (R := R) sIndex dIndex).eval (auxEnv source second third) 3 = H₄ := by
  simp only [eightSevenBody, Circuit.eval_bind, Circuit.eval_pairWithPowers_three,
    eval_formEnv_source, source.evalH₄]

omit [CommRing R] in
@[simp] theorem auxPair_multiplications
    (left right : Circuit R SourceInput 1) :
    (auxPair left right).gates.multiplications =
      left.gates.multiplications + right.gates.multiplications := by
  rfl

omit [CommRing R] in
@[simp] theorem auxPair_additions
    (left right : Circuit R SourceInput 1) :
    (auxPair left right).gates.additions =
      left.gates.additions + right.gates.additions := by
  rfl

omit [CommRing R] in
@[simp] theorem eightSevenBody_multiplications (sIndex dIndex : ℕ) :
    (eightSevenBody (R := R) sIndex dIndex).gates.multiplications = 2 := by
  rfl

omit [CommRing R] in
@[simp] theorem eightSevenBody_additions (sIndex dIndex : ℕ) :
    (eightSevenBody (R := R) sIndex dIndex).gates.additions = 6 := by
  rfl

/-- Exact addition count of the literal shared outer circuit. -/
theorem eightSevenCircuit_additions
    {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (sIndex dIndex : ℕ) :
    (eightSevenCircuit source second third sIndex dIndex).gates.additions =
      source.circuit.gates.additions + second.circuit.gates.additions +
        third.circuit.gates.additions + 6 := by
  simp only [eightSevenCircuit, Circuit.gates_bind, GateCount.add_additions,
    auxPair_additions, eightSevenBody_additions]
  omega

/-- Height ledger of the `8k+7` outer body: the two shells add one level above the
gadgets, and the recorded powers are forwarded unchanged. -/
theorem multDepth_eightSevenCircuit_le
    {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]}
    {sourceMuls secondMuls thirdMuls : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ sourceMuls)
    (second : RelativeRealization (R := R) θ source.circuit S₂ secondMuls)
    (third : RelativeRealization (R := R) θ source.circuit S₃ thirdMuls)
    (sIndex dIndex : ℕ) (D d₂ d₃ : ℕ)
    (hs0 : source.circuit.multDepth (fun _ => 0) 0 ≤ D)
    (hs1 : source.circuit.multDepth (fun _ => 0) 1 ≤ D)
    (hs2 : source.circuit.multDepth (fun _ => 0) 2 ≤ 1)
    (hs3 : source.circuit.multDepth (fun _ => 0) 3 ≤ 2)
    (h2c : second.circuit.multDepth (Sum.elim (fun _ : PolyInput => 0)
      (source.circuit.multDepth (fun _ => 0))) 0 ≤ d₂)
    (h3c : third.circuit.multDepth (Sum.elim (fun _ : PolyInput => 0)
      (source.circuit.multDepth (fun _ => 0))) 0 ≤ d₃) :
    ((eightSevenCircuit source second third sIndex dIndex).multDepth
        (fun _ => 0) 0 ≤ max (max d₂ d₃ + 1) D) ∧
      ((eightSevenCircuit source second third sIndex dIndex).multDepth
        (fun _ => 0) 1 ≤ max (max d₂ d₃ + 1) D) ∧
      ((eightSevenCircuit source second third sIndex dIndex).multDepth
        (fun _ => 0) 2 ≤ 1) ∧
      ((eightSevenCircuit source second third sIndex dIndex).multDepth
        (fun _ => 0) 3 ≤ 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightSevenCircuit, Circuit.multDepth_bind, eightSevenBody,
      eightSevenForms, auxPair, oldParameter, Circuit.pair,
      Circuit.pairWithPowers, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_sub, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.grandOutput,
      Circuit.polyParameter, Circuit.input, Circuit.multDepth_wire,
      Sum.elim_inl, Sum.elim_inr,
      show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
      show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    omega
  · rw [show (1 : Fin 4) = Fin.castAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightSevenCircuit, Circuit.multDepth_bind, eightSevenBody,
      eightSevenForms, auxPair, oldParameter, Circuit.pair,
      Circuit.pairWithPowers, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_sub, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.grandOutput,
      Circuit.polyParameter, Circuit.input, Circuit.multDepth_wire,
      Sum.elim_inl, Sum.elim_inr,
      show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
      show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    omega
  · rw [show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightSevenCircuit, Circuit.multDepth_bind, eightSevenBody,
      Circuit.pairWithPowers, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Circuit.grandOutput, Circuit.multDepth_input,
      Sum.elim_inl, Sum.elim_inr]
    exact hs2
  · rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [eightSevenCircuit, Circuit.multDepth_bind, eightSevenBody,
      Circuit.pairWithPowers, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.grandOutput, Circuit.multDepth_input,
      Sum.elim_inl, Sum.elim_inr]
    exact hs3

/-- Actual shared-circuit realization of one `8k+7` algebraic step. -/
def eightSevenRealized
    {θ : ℕ → A} {T₁' T₂' H₂ H₄ S₂ S₃ : A[X]} {m m₂ m₃ : ℕ}
    (source : JointPairRealization (R := R) θ T₁' T₂' H₂ H₄ m)
    (second : RelativeRealization (R := R) θ source.circuit S₂ m₂)
    (third : RelativeRealization (R := R) θ source.circuit S₃ m₃)
    (sIndex dIndex : ℕ) :
    JointPairRealization (R := R) θ
      (S₃ * S₃ - S₂ * S₂ + T₁')
      ((S₃ + S₂ + C (θ sIndex)) * (S₃ - S₂ + C (θ dIndex)) + T₂')
      H₂ H₄ (m + m₂ + m₃ + 2) where
  circuit := eightSevenCircuit source second third sIndex dIndex
  eval₁ := by
    rw [eightSevenCircuit, Circuit.eval_bind, Circuit.eval_bind]
    simpa only [sourceEnv, auxEnv] using
      eval_eightSevenBody_zero source second third sIndex dIndex
  eval₂ := by
    rw [eightSevenCircuit, Circuit.eval_bind, Circuit.eval_bind]
    simpa only [sourceEnv, auxEnv] using
      eval_eightSevenBody_one source second third sIndex dIndex
  evalH₂ := by
    rw [eightSevenCircuit, Circuit.eval_bind, Circuit.eval_bind]
    simpa only [sourceEnv, auxEnv] using
      eval_eightSevenBody_two source second third sIndex dIndex
  evalH₄ := by
    rw [eightSevenCircuit, Circuit.eval_bind, Circuit.eval_bind]
    simpa only [sourceEnv, auxEnv] using
      eval_eightSevenBody_three source second third sIndex dIndex
  multiplication_count := by
    simp only [eightSevenCircuit, Circuit.gates_bind,
      GateCount.add_multiplications, source.multiplication_count,
      auxPair_multiplications, second.multiplication_count,
      third.multiplication_count, eightSevenBody_multiplications]
    omega

end Outer

end FastPoly.Cost
