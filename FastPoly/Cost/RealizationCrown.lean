import FastPoly.Cost.RealizationComposition
import FastPoly.Cost.PowerTowerCircuit
import FastPoly.Cost.TCircuitCount
import FastPoly.Section5.FourKPlusOne
import FastPoly.Height.RealizationDepth

/-!
# Semantic realization of the `4k+1` crown

The quadratic, quartic, and shifted quartic are produced once.  The compiled `T_{k,4}`
circuit then consumes those three shared wires.  This is the circuit-level counterpart
of `lem:4k+1-splittable`; unlike a numerical `PairCost` witness, it identifies the
actual returned polynomials and the actual circuit with `2k` multiplications.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace Crown

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private def x : Circuit R PolyInput 1 := Circuit.polyX
private def a (i : ℕ) : Circuit R PolyInput 1 := Circuit.polyParameter i

/-- Shared producer in output order `(H₂,H₄,H̃₄,0)`.  The final zero wire supplies
the formally present (but unused) source-pair labels of the local compiler. -/
def powersCircuit : Circuit R PolyInput 4 :=
  Circuit.quadraticQuartic x (a 0) (a 1) (a 2) (a 3) (a 4)

/-- Wire the crown producer into a local `T` circuit. -/
def wiring : ConstructionWiring 4 where
  power i := if i = 1 then .inr 0 else if i = 2 then .inr 1 else .inl .variable
  shiftedPower := .inr 2
  parameter i := 5 + i
  source _ := .inr 3

/-- The full shared output circuit, ordered `(T¹,T²,H₂,H₄)`. -/
def circuit (k : ℕ) : Circuit R PolyInput 4 :=
  .bind powersCircuit <|
    .bind ((tCircuit (R := R) k 2).instantiateConstruction wiring) <|
      let t₁ := Circuit.rightInput (R := R)
        (ι := Sum PolyInput (Fin 4)) (0 : Fin 2)
      let t₂ := Circuit.rightInput (R := R)
        (ι := Sum PolyInput (Fin 4)) (1 : Fin 2)
      let h₂ := Circuit.priorOutput (R := R) (n := 2) (0 : Fin 4)
      let h₄ := Circuit.priorOutput (R := R) (n := 2) (1 : Fin 4)
      .fork (.fork t₁ t₂) (.fork h₂ h₄)

@[simp] theorem eval_powersCircuit_zero (θ : ℕ → A) :
    (powersCircuit (R := R)).eval (polyEnv θ) 0 =
      FastPoly.crownH2 (θ 0) (θ 1) := by
  rfl

@[simp] theorem eval_powersCircuit_one (θ : ℕ → A) :
    (powersCircuit (R := R)).eval (polyEnv θ) 1 =
      FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) := by
  rw [powersCircuit, Circuit.eval_quadraticQuartic_one]
  simp only [FastPoly.crownH4, FastPoly.crownH2]
  rfl

@[simp] theorem eval_powersCircuit_two (θ : ℕ → A) :
    (powersCircuit (R := R)).eval (polyEnv θ) 2 =
      FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4) := by
  rw [powersCircuit, Circuit.eval_quadraticQuartic_two]
  simp only [FastPoly.crownH4, FastPoly.crownH2]
  rfl

@[simp] theorem eval_powersCircuit_three (θ : ℕ → A) :
    (powersCircuit (R := R)).eval (polyEnv θ) 3 = 0 := by
  rw [powersCircuit, Circuit.eval_quadraticQuartic_three]

theorem eval_wiring_power (θ : ℕ → A) :
    wiring.powerValues θ ((powersCircuit (R := R)).eval (polyEnv θ)) =
      FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3) := by
  funext i
  by_cases h1 : i = 1
  · subst i
    simp only [ConstructionWiring.powerValues, wiring, if_pos, Sum.elim_inr,
      eval_powersCircuit_zero, FastPoly.crownHp]
  · by_cases h2 : i = 2
    · subst i
      simp only [ConstructionWiring.powerValues, wiring, h1, if_false, if_pos,
        Sum.elim_inr, eval_powersCircuit_one, FastPoly.crownHp]
    · simp only [ConstructionWiring.powerValues, wiring, h1, h2, if_false,
        Sum.elim_inl, polyEnv_variable, FastPoly.crownHp]

theorem eval_wiring_shifted (θ : ℕ → A) :
    wiring.shiftedValue θ ((powersCircuit (R := R)).eval (polyEnv θ)) =
      FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4) := by
  simp only [ConstructionWiring.shiftedValue, wiring, Sum.elim_inr,
    eval_powersCircuit_two]

theorem eval_wiring_source (θ : ℕ → A) :
    wiring.sourceValues θ ((powersCircuit (R := R)).eval (polyEnv θ)) =
      (fun _ => 0) := by
  funext i
  simp only [ConstructionWiring.sourceValues, wiring, Sum.elim_inr,
    eval_powersCircuit_three]

theorem eval_local (θ : ℕ → A) (k : ℕ) :
    let gadget := (tCircuit (R := R) k 2).instantiateConstruction wiring
    (gadget.eval
      (Sum.elim (polyEnv θ) ((powersCircuit (R := R)).eval (polyEnv θ))) 0,
      gadget.eval
      (Sum.elim (polyEnv θ) ((powersCircuit (R := R)).eval (polyEnv θ))) 1) =
        FastPoly.Tpair (FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3))
          (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4))
          k 2 (fun i => θ (5 + i)) := by
  dsimp only
  rw [Circuit.eval_instantiateConstruction, eval_wiring_power,
    eval_wiring_shifted, eval_wiring_source]
  exact eval_tCircuit (R := R)
    (FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3))
    (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4))
    (fun i => θ (5 + i)) k 2

@[simp] theorem powersCircuit_multiplications :
    (powersCircuit (R := R)).gates.multiplications = 2 := by
  rw [powersCircuit, Circuit.gates_quadraticQuartic_multiplications]
  rfl

/-- Exact multiplication count of the actual crown circuit. -/
theorem circuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.multiplications = 2 * k := by
  rw [circuit]
  simp only [Circuit.gates_bind, Circuit.gates_fork,
    GateCount.add_multiplications, Circuit.gates_rightInput,
    Circuit.gates_priorOutput, GateCount.zero_multiplications,
    powersCircuit_multiplications, Circuit.gates_instantiateConstruction]
  rw [gates_tCircuit_multiplications k 2
    (show ValidTCall k 2 from ⟨by omega, by omega⟩)]
  omega

/-- Height ledger of the crown circuit: the tower depths `(1,2,2,0)` satisfy the
canonical gadget invariant, so the `T` spine obeys its `tDB` bound and the pair
outputs sit at height at most `2⌈log₂(4k+1)⌉+3`. -/
theorem multDepth_circuit_le (k : ℕ) (hk : 1 ≤ k) :
    ((circuit (R := R) k).multDepth (fun _ => 0) 0
        ≤ 2 * Nat.clog 2 (4 * k + 1) + 3) ∧
      ((circuit (R := R) k).multDepth (fun _ => 0) 1
        ≤ 2 * Nat.clog 2 (4 * k + 1) + 3) ∧
      ((circuit (R := R) k).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((circuit (R := R) k).multDepth (fun _ => 0) 3 ≤ 2) := by
  obtain ⟨hq0, hq1, hq2, hq3⟩ := Height.multDepth_quadraticQuartic_le
    (x (R := R)) (a 0) (a 1) (a 2) (a 3) (a 4) (fun _ => 0)
    rfl rfl rfl rfl rfl rfl
  rw [show Circuit.quadraticQuartic (x (R := R)) (a 0) (a 1) (a 2) (a 3) (a 4)
      = powersCircuit from rfl] at hq0 hq1 hq2 hq3
  have hwle := Height.wiringDepth_le wiring
    ((powersCircuit (R := R)).multDepth (fun _ => 0))
    (by
      intro i
      by_cases hi1 : i = 1
      · subst hi1; simpa [wiring] using hq0
      · by_cases hi2 : i = 2
        · subst hi2; simpa [wiring] using hq1
        · simp [wiring, hi1, hi2])
    (by simpa [wiring] using hq2)
    (by intro i; simpa [wiring] using hq3)
  have hT : ∀ j : Fin 2, (tCircuit (R := R) k 2).multDepth
      ((Sum.elim (fun _ => (0 : ℕ))
        ((powersCircuit (R := R)).multDepth (fun _ => 0)))
          ∘ ConstructionWiring.label wiring) j ≤ 2 * Nat.clog 2 k + 3 := by
    intro j
    refine ((Circuit.multDepth_mono _ hwle j).trans
      (Height.multDepth_tCircuit_le k 2 Height.gadgetDp 2 (by omega)
        Height.gadgetDp_le le_rfl j)).trans ?_
    have := Height.tDB_le k k 2 (by omega)
    omega
  have hT0 := hT 0
  have hT1 := hT 1
  have hmono : Nat.clog 2 k ≤ Nat.clog 2 (4 * k + 1) :=
    Nat.clog_mono_right 2 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.instantiateConstruction,
      Circuit.multDepth_relabel, Circuit.multDepth_fork, Fin.addCases_left,
      Circuit.multDepth_rightInput, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    omega
  · rw [show (1 : Fin 4) = Fin.castAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.instantiateConstruction,
      Circuit.multDepth_relabel, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Circuit.multDepth_rightInput, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    omega
  · rw [show (2 : Fin 4) = Fin.natAdd 2 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.instantiateConstruction,
      Circuit.multDepth_relabel, Circuit.multDepth_fork, Fin.addCases_left,
      Fin.addCases_right, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    omega
  · rw [show (3 : Fin 4) = Fin.natAdd 2 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [circuit, Circuit.multDepth_bind, Circuit.instantiateConstruction,
      Circuit.multDepth_relabel, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.priorOutput,
      Circuit.multDepth_input, Sum.elim_inl, Sum.elim_inr]
    omega

/-- The `4k+1` witness returned by the master proof is jointly realized by the same
`2k`-multiplication circuit that produces its recorded powers. -/
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
    rw [Circuit.eval_priorOutput, eval_powersCircuit_zero]
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
    rw [Circuit.eval_priorOutput, eval_powersCircuit_one]
  multiplication_count := circuit_multiplications k hk

theorem realizable (θ : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    JointPairRealizable (R := R) θ
      (FastPoly.Tpair (FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4))
        k 2 (fun i => θ (5 + i))).1
      (FastPoly.Tpair (FastPoly.crownHp (θ 0) (θ 1) (θ 2) (θ 3))
        (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3) + C (θ 4))
        k 2 (fun i => θ (5 + i))).2
      (FastPoly.crownH2 (θ 0) (θ 1))
      (FastPoly.crownH4 (θ 0) (θ 1) (θ 2) (θ 3)) (2 * k) :=
  ⟨realized θ k hk⟩

end Crown

end FastPoly.Cost
