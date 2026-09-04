import FastPoly.Cost.OddGadgetCrownBundleOptimized

/-!
# Retained-shift `8k+3` known-powers gadget

The ordinary known-powers gadget already binds the perturbed quartic, its scalar
shift, and the shift scalar itself.  This sibling feeds that scalar to the retained
`T` compiler.  Its output polynomial, multiplication count, and height certificate
are unchanged; its literal additions are the selected `8k+3` gadget ledger.
-/

namespace FastPoly.Cost.OddGadget

open Polynomial

universe u v

namespace KnownOptimized

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Bind the perturbed quartic once before exposing it and its scalar shift.  The
ordinary producer writes the same addition twice syntactically; this is the local
one-addition peephole needed by the manuscript ledger. -/
def powerPair : Circuit R ConstructionInput 2 :=
  .bind ((peelCircuit 1).reindexConstructionParameters (fun i => 5 + i)) <|
    let q := Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 1)
    let old (p : Circuit R ConstructionInput 1) := p.liftLeft
    .bind (.add (old (Circuit.constructionPower 2)) q) <|
      let h₄' := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 1)) (0 : Fin 1)
      let oldest (p : Circuit R ConstructionInput 1) := p.liftLeft.liftLeft
      .fork h₄' (.add h₄' (oldest (Circuit.constructionParameter 6)))

private theorem eval_peelOne (H₂ H₄ : A[X]) (theta : ℕ → A) :
    ((peelCircuit (R := R) 1).reindexConstructionParameters
        (fun i => 5 + i)).eval (env H₂ H₄ theta) 0 =
      FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i)) := by
  rw [env, Circuit.eval_reindexConstructionParameters]
  exact eval_peelCircuit (R := R) (suppliedPowers H₂ H₄) H₄
    (fun i => theta (5 + i)) (fun _ => 0) 1

@[simp] theorem eval_powerPair_zero (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (powerPair (R := R)).eval (env H₂ H₄ theta) 0 =
      H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
        (fun i => theta (5 + i)) := by
  rw [powerPair, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_fork_zero,
    Circuit.eval_rightInput]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput]
  rw [eval_peelOne]
  simp only [env, Circuit.eval_constructionPower, suppliedPowers_two]

@[simp] theorem eval_powerPair_one (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (powerPair (R := R)).eval (env H₂ H₄ theta) 1 =
      H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
          (fun i => theta (5 + i)) + C (theta 6) := by
  rw [powerPair, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_fork_one]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput]
  rw [eval_peelOne]
  simp only [env, Circuit.eval_constructionPower, Circuit.eval_constructionParameter,
    suppliedPowers_two]

/-- Feed the newly bound level-two power pair to the local compiler and retain
`theta 6` as source zero. -/
def retainedLabel : ConstructionInput → Sum ConstructionInput (Fin 2)
  | .variable => .inl .variable
  | .power i => if i = 2 then .inr 0 else .inl (.power i)
  | .shiftedPower => .inr 1
  | .parameter i => .inl (.parameter (7 + i))
  | .source i => if i = 0 then .inl (.parameter 6) else .inl (.source i)

/-- The retained local `T_{2k,4}` call. -/
def localCircuit (k : ℕ) : Circuit R (Sum ConstructionInput (Fin 2)) 2 :=
  (RetainedShiftT.compiler (2 * k) 2).relabel retainedLabel

/-- The complete optimized known-powers gadget. -/
def circuit (k : ℕ) : Circuit R ConstructionInput 1 :=
  .bind powerPair <|
    .bind (localCircuit k) <|
      let old (p : Circuit R ConstructionInput 1) := p.liftLeft.liftLeft
      let source : Circuit R (Sum (Sum ConstructionInput (Fin 2)) (Fin 2)) 2 :=
        .fork
          (Circuit.rightInput (R := R) (ι := Sum ConstructionInput (Fin 2))
            (0 : Fin 2))
          (Circuit.rightInput (R := R) (ι := Sum ConstructionInput (Fin 2))
            (1 : Fin 2))
      Circuit.finishFill (old Circuit.constructionX)
        (old (Circuit.constructionPower 1))
        (old (Circuit.constructionParameter 0))
        (old (Circuit.constructionParameter 1))
        (old (Circuit.constructionParameter 2))
        (old (Circuit.constructionParameter 3))
        (old (Circuit.constructionParameter 4)) source

/-- The retained local compiler evaluates to the mathematical `Tpair` used by
`knownValue`. -/
theorem eval_local (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) :
    ((localCircuit (R := R) k).eval
        (Sum.elim (env H₂ H₄ theta)
          ((powerPair (R := R)).eval (env H₂ H₄ theta))) 0,
      (localCircuit (R := R) k).eval
        (Sum.elim (env H₂ H₄ theta)
          ((powerPair (R := R)).eval (env H₂ H₄ theta))) 1) =
      FastPoly.Tpair
        (Function.update (suppliedPowers H₂ H₄) 2
          (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
            (fun i => theta (5 + i))))
        (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
          (fun i => theta (5 + i)) + C (theta 6))
        (2 * k) 2 (fun i => theta (7 + i)) := by
  let values := (powerPair (R := R)).eval (env H₂ H₄ theta)
  let localEnv := Sum.elim (env H₂ H₄ theta) values ∘ retainedLabel
  have hshift : localEnv .shiftedPower =
      localEnv (.power 2) + localEnv (.source 0) := by
    simp only [localEnv, Function.comp_apply, retainedLabel, Sum.elim_inr]
    change (powerPair (R := R)).eval (env H₂ H₄ theta) 1 =
      (powerPair (R := R)).eval (env H₂ H₄ theta) 0 + C (theta 6)
    rw [eval_powerPair_one, eval_powerPair_zero]
  let source : Fin 2 → A[X] := fun i => localEnv (.source i)
  have henv : localEnv =
      constructionEnv
        (Function.update (suppliedPowers H₂ H₄) 2 (values 0))
        (values 1) (fun i => theta (7 + i)) source := by
    funext input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi : i = 2
        · subst i
          simp only [localEnv, retainedLabel, if_pos, Function.comp_apply,
            Sum.elim_inr, constructionEnv_power, Function.update_self]
        · simp only [localEnv, retainedLabel, hi, if_false, Function.comp_apply,
            Sum.elim_inl, env, constructionEnv_power]
          rw [Function.update_of_ne hi]
    | shiftedPower => rfl
    | parameter i => rfl
    | source i => rfl
  simp only [localCircuit, Circuit.eval_relabel]
  change ((RetainedShiftT.compiler (R := R) (2 * k) 2).eval localEnv 0,
    (RetainedShiftT.compiler (R := R) (2 * k) 2).eval localEnv 1) = _
  have hv0 : values 0 =
      H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
        (fun i => theta (5 + i)) := eval_powerPair_zero (R := R) H₂ H₄ theta
  have hv1 : values 1 =
      H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
          (fun i => theta (5 + i)) + C (theta 6) :=
    eval_powerPair_one (R := R) H₂ H₄ theta
  rw [RetainedShiftT.eval_compiler_eq (2 * k) 2 localEnv
    (show ValidTCall (2 * k) 2 from ⟨by omega, by omega⟩) hshift, henv,
    hv0, hv1]
  exact eval_tCircuit_with_source (R := R)
    (Function.update (suppliedPowers H₂ H₄) 2
      (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i))))
    (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i)) +
      C (theta 6)) (fun i => theta (7 + i)) source (2 * k) 2

/-- The optimized circuit computes the existing decoder-facing normal form. -/
theorem eval_circuit (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) :
    (circuit (R := R) k).eval (env H₂ H₄ theta) 0 =
      knownValue H₂ H₄ k theta := by
  rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
  have hpair := eval_local (R := R) H₂ H₄ theta k
  have h₁ := congrArg Prod.fst hpair
  have h₂' := congrArg Prod.snd hpair
  dsimp only at h₁ h₂'
  simp only [env] at h₁ h₂'
  simp only [Circuit.eval_finishFill, Circuit.eval_fork_zero, Circuit.eval_fork_one,
    Circuit.eval_rightInput, Circuit.eval_liftLeft, knownValue,
    Circuit.eval_constructionPower, Circuit.eval_constructionX,
    Circuit.eval_constructionParameter, env, suppliedPowers_one]
  rw [h₁, h₂']

omit [CommRing R] in
@[simp] theorem powerPair_additions :
    (powerPair (R := R)).gates.additions = 3 := by
  rfl

omit [CommRing R] in
@[simp] theorem powerPair_multiplications :
    (powerPair (R := R)).gates.multiplications = 0 := by
  rfl

/-- Literal additions in the optimized known-powers circuit. -/
theorem circuit_additions (k : ℕ) :
    (circuit (R := R) k).gates.additions = tAdd (2 * k) 2 + 9 := by
  simp only [circuit, localCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.finishFill, Circuit.gates, Circuit.gates_rightInput,
    Circuit.gates_liftLeft, GateCount.add_additions,
    GateCount.zero_additions, GateCount.adds_additions,
    GateCount.muls_additions, powerPair_additions,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]
  rw [RetainedShiftT.compiler_additions_eq_tAdd (2 * k) 2
    (show ValidTCall (2 * k) 2 from ⟨by omega, by omega⟩)]
  omega

/-- Exact multiplication count of the optimized known-powers circuit. -/
theorem circuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.multiplications = 4 * k + 1 := by
  simp only [circuit, localCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.finishFill, Circuit.gates, Circuit.gates_rightInput,
    Circuit.gates_liftLeft, GateCount.add_multiplications,
    GateCount.zero_multiplications, GateCount.adds_multiplications,
    GateCount.muls_multiplications, powerPair_multiplications,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]
  rw [RetainedShiftT.compiler_multiplications,
    gates_tCircuit_multiplications (2 * k) 2
      (show ValidTCall (2 * k) 2 from ⟨by omega, by omega⟩),
    show 2 - 1 = 1 by omega, pow_one]
  omega

omit [CommRing R] in
theorem multDepth_powerPair_le :
    ((powerPair (R := R)).multDepth Height.gadgetDepthEnv 0 ≤ 2) ∧
      ((powerPair (R := R)).multDepth Height.gadgetDepthEnv 1 ≤ 2) := by
  have hq : ((peelCircuit (R := R) 1).reindexConstructionParameters
      (fun i => 5 + i)).multDepth Height.gadgetDepthEnv 0 = 0 := by
    rw [Height.multDepth_reindexConstructionParameters]
    rfl
  constructor
  · rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
    simp only [powerPair, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Circuit.multDepth_add, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.constructionPower,
      Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
      hq, Height.denv_power, Height.denv_parameter, Height.gadgetDp_two]
    omega
  · rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    simp only [powerPair, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.multDepth_add, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.constructionPower,
      Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
      hq, Height.denv_power, Height.denv_parameter, Height.gadgetDp_two]
    omega

/-- The retained local call has the ordinary known-gadget local height bound. -/
theorem multDepth_localCircuit_le (k : ℕ) (j : Fin 2) :
    (localCircuit (R := R) k).multDepth
      (Sum.elim Height.gadgetDepthEnv
        ((powerPair (R := R)).multDepth Height.gadgetDepthEnv)) j
      ≤ 2 * Nat.clog 2 (2 * k) + 3 := by
  obtain ⟨hp0, hp1⟩ := multDepth_powerPair_le (R := R)
  let dP := (powerPair (R := R)).multDepth Height.gadgetDepthEnv
  let dp' := Function.update Height.gadgetDp 2 (dP 0)
  have hlabel : Sum.elim Height.gadgetDepthEnv dP ∘ retainedLabel =
      Height.denv dp' (dP 1) := by
    funext input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi : i = 2
        · subst i
          simp [retainedLabel, dp', Function.update_self]
        · simp [retainedLabel, hi, dp', Function.update_of_ne,
            Height.gadgetDepthEnv]
    | shiftedPower => rfl
    | parameter i => rfl
    | source i =>
        by_cases hi : i = 0
        · subst i
          rfl
        · simp [retainedLabel, hi, Height.gadgetDepthEnv]
  have hmono : ∀ input, Height.denv dp' (dP 1) input ≤
      Height.gadgetDepthEnv input := by
    intro input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi : i = 2
        · subst i
          simpa [dp', dP, Function.update_self] using hp0
        · simp [dp', hi, Function.update_of_ne, Height.gadgetDepthEnv]
    | shiftedPower => simpa [dP] using hp1
    | parameter i => rfl
    | source i => rfl
  rw [localCircuit, Circuit.multDepth_relabel, hlabel]
  calc
    (RetainedShiftT.compiler (R := R) (2 * k) 2).multDepth
        (Height.denv dp' (dP 1)) j
        ≤ (RetainedShiftT.compiler (R := R) (2 * k) 2).multDepth
          Height.gadgetDepthEnv j := Circuit.multDepth_mono _ hmono j
    _ ≤ Height.tDB (2 * k) (2 * k) 2 := by
      simpa only [RetainedShiftT.compiler] using
        (CrownOptimized.multDepth_compilerF_two_le (R := R) (2 * k) (2 * k) j)
    _ ≤ 2 * Nat.clog 2 (2 * k) + 3 := by
      have h := Height.tDB_le (2 * k) (2 * k) 2 (by omega)
      omega

/-- The complete optimized gadget preserves the ordinary height certificate. -/
theorem multDepth_circuit_le (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).multDepth Height.gadgetDepthEnv 0 ≤
      2 * Nat.clog 2 (2 * (4 * k + 1) + 1) + 1 := by
  have hT0 := multDepth_localCircuit_le (R := R) k 0
  have hT1 := multDepth_localCircuit_le (R := R) k 1
  have hc1 : Nat.clog 2 (2 * k) = Nat.clog 2 k + 1 :=
    Height.clog_two_double k hk
  have hc2 : Nat.clog 2 (2 * (2 * k)) = Nat.clog 2 (2 * k) + 1 :=
    Height.clog_two_double (2 * k) (by omega)
  have hc3 : Nat.clog 2 (2 * (2 * (2 * k))) = Nat.clog 2 (2 * (2 * k)) + 1 :=
    Height.clog_two_double (2 * (2 * k)) (by omega)
  have hc4 : Nat.clog 2 (2 * (2 * (2 * k))) ≤ Nat.clog 2 (2 * (4 * k + 1) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  simp only [circuit, Circuit.multDepth_bind, Circuit.finishFill,
    Circuit.multDepth_fork, Circuit.multDepth_add, Circuit.multDepth_mul,
    Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
    Circuit.constructionX, Circuit.constructionPower,
    Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
    Height.denv_variable, Height.denv_power,
    Height.denv_parameter, Height.gadgetDp_one]
  simp only [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left, Fin.addCases_right, Circuit.multDepth_rightInput]
    at hT0 hT1 ⊢
  omega

/-- Drop-in optimized realization of the existing known-powers polynomial. -/
def realized (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta (knownValue H₂ H₄ k theta) (4 * k + 1) where
  circuit := circuit k
  eval_eq := eval_circuit H₂ H₄ theta k
  multiplication_count := circuit_multiplications k hk
  depth_le := multDepth_circuit_le k hk

end KnownOptimized

end FastPoly.Cost.OddGadget
