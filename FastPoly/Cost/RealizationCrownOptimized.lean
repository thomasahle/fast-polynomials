import FastPoly.Cost.RealizationCrown
import FastPoly.Cost.RetainedShiftTBridge
import FastPoly.Cost.RetainedShiftTCount

/-!
# Retained-shift realization of the `4k+1` crown

The ordinary crown realization already produces `H₄`, `H₄ + ρ`, and the scalar
`ρ = θ₄`.  This sibling feeds that existing scalar wire to the retained-shift
`T` compiler.  It therefore has the same four outputs and multiplication count,
while its literal addition count is the manuscript ledger.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace CrownOptimized

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The already-present scalar shift `θ₄`, selected without an arithmetic gate. -/
def rhoLabel : Sum PolyInput (Fin 4) := .inl (.parameter 4)

/-- The retained local `T_{k,4}` call. -/
def localCircuit (k : ℕ) : Circuit R (Sum PolyInput (Fin 4)) 2 :=
  Circuit.instantiateRetainedT Crown.wiring rhoLabel k 2

/-- The full optimized crown circuit, ordered `(T¹,T²,H₂,H₄)`. -/
def circuit (k : ℕ) : Circuit R PolyInput 4 :=
  .bind Crown.powersCircuit <|
    .bind (localCircuit k) <|
      let t₁ := Circuit.rightInput (R := R)
        (ι := Sum PolyInput (Fin 4)) (0 : Fin 2)
      let t₂ := Circuit.rightInput (R := R)
        (ι := Sum PolyInput (Fin 4)) (1 : Fin 2)
      let h₂ := Circuit.priorOutput (R := R) (n := 2) (0 : Fin 4)
      let h₄ := Circuit.priorOutput (R := R) (n := 2) (1 : Fin 4)
      .fork (.fork t₁ t₂) (.fork h₂ h₄)

/-- The producer's shifted quartic differs from its quartic by exactly the retained
scalar selected in `rhoLabel`. -/
theorem retainedEquation (θ : ℕ → A) :
    Crown.wiring.shiftedValue θ
        ((Crown.powersCircuit (R := R)).eval (polyEnv θ)) =
      Crown.wiring.powerValues θ
          ((Crown.powersCircuit (R := R)).eval (polyEnv θ)) 2 +
        Sum.elim (polyEnv θ)
          ((Crown.powersCircuit (R := R)).eval (polyEnv θ)) rhoLabel := by
  rw [Crown.eval_wiring_shifted, Crown.eval_wiring_power]
  rfl

/-- The retained local compiler evaluates to the same mathematical `Tpair`. -/
theorem eval_local (θ : ℕ → A) (k : ℕ) :
    ((localCircuit (R := R) k).eval
        (Sum.elim (polyEnv θ)
          ((Crown.powersCircuit (R := R)).eval (polyEnv θ))) 0,
      (localCircuit (R := R) k).eval
        (Sum.elim (polyEnv θ)
          ((Crown.powersCircuit (R := R)).eval (polyEnv θ))) 1) =
      FastPoly.Tpair (FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4))
        k 2 (fun i => θ (5 + i)) := by
  have h := Circuit.eval_instantiateRetainedT_eq_Tpair (R := R)
    Crown.wiring rhoLabel θ
    ((Crown.powersCircuit (R := R)).eval (polyEnv θ)) k 2
    (show ValidTCall k 2 from ⟨by omega, by omega⟩) (retainedEquation (R := R) θ)
  rw [Crown.eval_wiring_power, Crown.eval_wiring_shifted] at h
  simpa only [localCircuit, Crown.wiring] using h

@[simp] theorem powersCircuit_additions :
    (Crown.powersCircuit (R := R)).gates.additions = 7 := by
  rfl

/-- Literal addition count of the same optimized crown circuit. -/
theorem circuit_additions (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.additions = tAdd (2 * k) 1 + 2 := by
  rw [circuit]
  simp only [Circuit.gates_bind, Circuit.gates_fork,
    GateCount.add_additions, Circuit.gates_rightInput,
    Circuit.gates_priorOutput, GateCount.zero_additions,
    powersCircuit_additions, localCircuit,
    Circuit.gates_instantiateRetainedT]
  rw [RetainedShiftT.compiler_additions_eq_tAdd k 2
    (show ValidTCall k 2 from ⟨by omega, by omega⟩),
    tAdd_even_base k hk]
  omega

/-- Exact multiplication count of the optimized crown circuit. -/
theorem circuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.multiplications = 2 * k := by
  rw [circuit]
  simp only [Circuit.gates_bind, Circuit.gates_fork,
    GateCount.add_multiplications, Circuit.gates_rightInput,
    Circuit.gates_priorOutput, GateCount.zero_multiplications,
    Crown.powersCircuit_multiplications, localCircuit]
  rw [Circuit.instantiateRetainedT_multiplications,
    gates_tCircuit_multiplications k 2
      (show ValidTCall k 2 from ⟨by omega, by omega⟩)]
  omega

private theorem multDepth_oddBaseAux_le (k : ℕ) :
    (RetainedShiftT.oddBaseAux (R := R) k
      (Circuit.constructionSource (R := R) 0)).multDepth
        Height.gadgetDepthEnv 0 ≤ 3 ∧
    (RetainedShiftT.oddBaseAux (R := R) k
      (Circuit.constructionSource (R := R) 0)).multDepth
        Height.gadgetDepthEnv 1 ≤ 3 ∧
    (RetainedShiftT.oddBaseAux (R := R) k
      (Circuit.constructionSource (R := R) 0)).multDepth
        Height.gadgetDepthEnv 2 ≤ 2 ∧
    (RetainedShiftT.oddBaseAux (R := R) k
      (Circuit.constructionSource (R := R) 0)).multDepth
        Height.gadgetDepthEnv 3 ≤ 2 ∧
    (RetainedShiftT.oddBaseAux (R := R) k
      (Circuit.constructionSource (R := R) 0)).multDepth
        Height.gadgetDepthEnv 4 ≤ 2 ∧
    (RetainedShiftT.oddBaseAux (R := R) k
      (Circuit.constructionSource (R := R) 0)).multDepth
        Height.gadgetDepthEnv 5 ≤ 2 := by
  exact ⟨by rfl, by rfl, by rfl, by rfl, by rfl, by
    change 0 ≤ 2
    omega⟩

/-- At level two, the retained compiler differs from `tCircuitF` only in the odd
shared base.  That base obeys the same spine-depth ledger. -/
theorem multDepth_compilerF_two_le (fuel k : ℕ) (j : Fin 2) :
    (RetainedShiftT.compilerF (R := R) fuel k 2).multDepth
        Height.gadgetDepthEnv j ≤ Height.tDB fuel k 2 := by
  cases fuel with
  | zero =>
      rw [RetainedShiftT.compilerF_zero]
      exact Height.multDepth_tCircuitF_le (R := R) 0 k 2
        Height.gadgetDp 2 (by omega) Height.gadgetDp_le (by omega) j
  | succ fuel =>
      by_cases hk : k ≤ 1
      · rw [RetainedShiftT.compilerF_succ_le_one fuel k 2 hk]
        exact Height.multDepth_tCircuitF_le (R := R) (fuel + 1) k 2
          Height.gadgetDp 2 (by omega) Height.gadgetDp_le (by omega) j
      · by_cases heven : k % 2 = 0
        · rw [RetainedShiftT.compilerF_succ_even_main fuel k 2 hk heven (by omega)]
          exact Height.multDepth_tCircuitF_le (R := R) (fuel + 1) k 2
            Height.gadgetDp 2 (by omega) Height.gadgetDp_le (by omega) j
        · rw [RetainedShiftT.compilerF_succ_odd_base fuel k 2 hk heven (by omega)]
          change (RetainedShiftT.oddBaseCircuit (R := R) k
            (Circuit.constructionSource (R := R) 0)
            (tCircuitF (R := R) fuel ((k - 1) / 2) 3)).multDepth
              Height.gadgetDepthEnv j ≤ Height.tDB (fuel + 1) k 2
          rw [RetainedShiftT.oddBaseCircuit]
          let aux := RetainedShiftT.oddBaseAux (R := R) k
            (Circuit.constructionSource (R := R) 0)
          let dp' := Function.update Height.gadgetDp 3
            (aux.multDepth (Height.denv Height.gadgetDp 2) 0)
          let dps' := aux.multDepth (Height.denv Height.gadgetDp 2) 1
          obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩ :=
            multDepth_oddBaseAux_le (R := R) k
          change aux.multDepth (Height.denv Height.gadgetDp 2) 0 ≤ 3 at ha0
          change aux.multDepth (Height.denv Height.gadgetDp 2) 1 ≤ 3 at ha1
          change aux.multDepth (Height.denv Height.gadgetDp 2) 2 ≤ 2 at ha2
          change aux.multDepth (Height.denv Height.gadgetDp 2) 3 ≤ 2 at ha3
          change aux.multDepth (Height.denv Height.gadgetDp 2) 4 ≤ 2 at ha4
          change aux.multDepth (Height.denv Height.gadgetDp 2) 5 ≤ 2 at ha5
          have hdp' : ∀ i, 1 ≤ i → dp' i ≤ i := by
            intro i hi
            by_cases hi3 : i = 3
            · subst i
              simp only [dp', Function.update_self]
              exact ha0
            · simp only [dp', Function.update_of_ne hi3]
              exact Height.gadgetDp_le i hi
          have hinner := Height.multDepth_tCircuitF_le (R := R) fuel
            ((k - 1) / 2) 3 dp' dps' (by omega) hdp' ha1
          have hbound : Height.tDB (fuel + 1) k 2 =
              max (max 2 (Height.tDB fuel ((k - 1) / 2) 3) + 1) 2 := by
            simp [Height.tDB, if_neg hk, heven]
          rw [hbound]
          match j with
          | 0 =>
              rw [Height.multDepth_finishOdd_zero]
              have h0 := hinner 0
              dsimp only [aux, dp', dps'] at ha2 ha4 h0 ⊢
              omega
          | 1 =>
              rw [Height.multDepth_finishOdd_one]
              have h1 := hinner 1
              dsimp only [aux, dp', dps'] at ha3 ha5 h1 ⊢
              omega

/-- The optimized crown preserves the ordinary crown's four-output depth bound. -/
theorem multDepth_circuit_le (k : ℕ) (hk : 1 ≤ k) :
    ((circuit (R := R) k).multDepth (fun _ => 0) 0
        ≤ 2 * Nat.clog 2 (4 * k + 1) + 3) ∧
      ((circuit (R := R) k).multDepth (fun _ => 0) 1
        ≤ 2 * Nat.clog 2 (4 * k + 1) + 3) ∧
      ((circuit (R := R) k).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((circuit (R := R) k).multDepth (fun _ => 0) 3 ≤ 2) := by
  obtain ⟨hq0, hq1, hq2, hq3⟩ := Height.multDepth_quadraticQuartic_le
    (Circuit.polyX (R := R)) (Circuit.polyParameter 0) (Circuit.polyParameter 1)
    (Circuit.polyParameter 2) (Circuit.polyParameter 3) (Circuit.polyParameter 4)
    (fun _ => 0) rfl rfl rfl rfl rfl rfl
  rw [show Circuit.quadraticQuartic (Circuit.polyX (R := R))
      (Circuit.polyParameter 0) (Circuit.polyParameter 1)
      (Circuit.polyParameter 2) (Circuit.polyParameter 3)
      (Circuit.polyParameter 4) = Crown.powersCircuit from rfl]
    at hq0 hq1 hq2 hq3
  let dvals := (Crown.powersCircuit (R := R)).multDepth (fun _ => 0)
  have hwle := Height.wiringDepth_le
    (Crown.wiring.withRetainedShift rhoLabel) dvals
    (by
      intro i
      by_cases hi1 : i = 1
      · subst i
        simpa [Crown.wiring] using hq0
      · by_cases hi2 : i = 2
        · subst i
          simpa [Crown.wiring] using hq1
        · simp [Crown.wiring, hi1, hi2])
    (by simpa [Crown.wiring] using hq2)
    (by
      intro i
      by_cases hi0 : i = 0
      · subst i
        simp [rhoLabel]
      · have hi1 : i = 1 := by omega
        subst i
        simpa [Crown.wiring] using hq3)
  have hlocal : ∀ j : Fin 2,
      (localCircuit (R := R) k).multDepth
          (Sum.elim (fun _ => (0 : ℕ)) dvals) j ≤ Height.tDB k k 2 := by
    intro j
    calc
      (localCircuit (R := R) k).multDepth
          (Sum.elim (fun _ => (0 : ℕ)) dvals) j =
          (RetainedShiftT.compiler (R := R) k 2).multDepth
            (Sum.elim (fun _ => (0 : ℕ)) dvals ∘
              (Crown.wiring.withRetainedShift rhoLabel).label) j := by
            rw [localCircuit, Circuit.instantiateRetainedT,
              Circuit.instantiateConstruction, Circuit.multDepth_relabel]
      _ ≤ (RetainedShiftT.compiler (R := R) k 2).multDepth
          Height.gadgetDepthEnv j :=
        Circuit.multDepth_mono _ hwle j
      _ ≤ Height.tDB k k 2 := by
        simpa only [RetainedShiftT.compiler] using
          (multDepth_compilerF_two_le (R := R) k k j)
  have hT0 := hlocal 0
  have hT1 := hlocal 1
  have hDB := Height.tDB_le k k 2 (by omega)
  have hmono : Nat.clog 2 k ≤ Nat.clog 2 (4 * k + 1) :=
    Nat.clog_mono_right 2 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Circuit.multDepth_rightInput, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    change (localCircuit (R := R) k).multDepth
      (Sum.elim (fun _ => (0 : ℕ)) dvals) 0 ≤ _
    omega
  · rw [show (1 : Fin 4) = Fin.castAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Fin.addCases_right, Circuit.multDepth_rightInput,
      Circuit.priorOutput, Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    change (localCircuit (R := R) k).multDepth
      (Sum.elim (fun _ => (0 : ℕ)) dvals) 1 ≤ _
    omega
  · rw [show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Fin.addCases_right, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    exact hq0
  · rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    exact hq1

/-- The `4k+1` pair witness realized by the literal optimized circuit. -/
def realized (θ : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    JointPairRealization (R := R) θ
      (FastPoly.Tpair (FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4))
        k 2 (fun i => θ (5 + i))).1
      (FastPoly.Tpair (FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4))
        k 2 (fun i => θ (5 + i))).2
      (FastPoly.crownH2 (θ 0) (θ 1))
      (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3)) (2 * k) where
  circuit := circuit k
  eval₁ := by
    rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
    have h := congrArg Prod.fst (eval_local (R := R) θ k)
    simpa only [Circuit.eval_fork, Circuit.eval_rightInput, Fin.addCases_left] using h
  eval₂ := by
    rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
    have h := congrArg Prod.snd (eval_local (R := R) θ k)
    simpa only [Circuit.eval_fork, Circuit.eval_rightInput, Fin.addCases_left,
      Fin.addCases_right] using h
  evalH₂ := by
    rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
    rw [Circuit.eval_fork]
    rw [show (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) from rfl]
    dsimp only
    rw [Fin.addCases_right]
    rw [Circuit.eval_fork]
    dsimp only
    rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
      Fin.addCases_left]
    rw [Circuit.eval_priorOutput, Crown.eval_powersCircuit_zero]
  evalH₄ := by
    rw [circuit, Circuit.eval_bind, Circuit.eval_bind]
    rw [Circuit.eval_fork]
    rw [show (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) from rfl]
    dsimp only
    rw [Fin.addCases_right]
    rw [Circuit.eval_fork]
    dsimp only
    rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
      Fin.addCases_right]
    rw [Circuit.eval_priorOutput, Crown.eval_powersCircuit_one]
  multiplication_count := circuit_multiplications k hk

end CrownOptimized

end FastPoly.Cost
