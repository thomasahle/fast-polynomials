import FastPoly.Cost.OddGadgetBundle

/-!
# The crown gadget with its quartic byproduct

The `8k+3` master step consumes more than the polynomial `Q_{4k+1}`: its next odd
gadget uses the newly constructed crown quartic.  This file exposes both values from
one shared local circuit, without recomputing the quartic.
-/

namespace FastPoly.Cost.OddGadget

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Output zero is `Q_{4k+1}`; output one is the crown quartic it constructs. -/
noncomputable def q4BundleOutput (H₂ : A[X]) (θ : ℕ → A) (k : ℕ) :
    Fin 2 → A[X] :=
  twoOutputs
    (FastPoly.q4k1 H₂ (θ 1) (θ 4) (θ 2) (θ 3) (θ 0)
      k (fun i => θ (5 + i)))
    (FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + θ 1) (θ 2) (θ 3))

/-- The ordinary q4 circuit with the already-computed crown quartic retained as a
second output. -/
def q4BundleCircuit (k : ℕ) : Circuit R ConstructionInput 2 :=
  .bind q4Tower <|
    .bind (q4TCircuit k) <|
      let old (p : Circuit R ConstructionInput 1) := p.liftLeft.liftLeft
      let T₁ := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 3)) (0 : Fin 2)
      let T₂ := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 3)) (1 : Fin 2)
      let Q := .add (.mul (.add (old Circuit.constructionX)
        (old (Circuit.constructionParameter 0))) T₁) T₂
      let H₄ := Circuit.priorOutput (R := R) (ι := ConstructionInput)
        (n := 2) (1 : Fin 3)
      .fork Q H₄

@[simp] theorem eval_q4BundleCircuit_zero [Nontrivial A]
    {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (θ : ℕ → A) (k : ℕ) :
    (q4BundleCircuit (R := R) k).eval (env H₂ H₄ θ) 0 =
      q4BundleOutput H₂ θ k 0 := by
  rw [q4BundleCircuit, Circuit.eval_bind, Circuit.eval_bind]
  have hpair := eval_q4TCircuit (R := R) (H₄ := H₄) hH₂m hH₂d θ k
  have h₁ := congrArg Prod.fst hpair
  have h₂' := congrArg Prod.snd hpair
  dsimp only at h₁ h₂'
  rw [env] at h₁ h₂'
  rw [Circuit.eval_fork]
  dsimp only
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left]
  simp only [Circuit.eval_add, Circuit.eval_mul,
    Circuit.eval_liftLeft, Circuit.eval_rightInput,
    Circuit.eval_constructionX, Circuit.eval_constructionParameter,
    env, q4BundleOutput, FastPoly.q4k1]
  rw [show (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 from rfl]
  rw [twoOutputs_zero]
  rw [h₁, h₂']

@[simp] theorem eval_q4BundleCircuit_one [Nontrivial A]
    {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (θ : ℕ → A) (k : ℕ) :
    (q4BundleCircuit (R := R) k).eval (env H₂ H₄ θ) 1 =
      q4BundleOutput H₂ θ k 1 := by
  rw [q4BundleCircuit, Circuit.eval_bind, Circuit.eval_bind]
  rw [Circuit.eval_fork]
  dsimp only
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_right, Circuit.eval_priorOutput]
  change (q4Tower (R := R)).eval (env H₂ H₄ θ) 1 =
    FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + θ 1) (θ 2) (θ 3)
  rw [eval_q4Tower_one, FastPoly.crownH4,
    ← FastPoly.crownH2_shift hH₂m hH₂d]

theorem q4BundleCircuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (q4BundleCircuit (R := R) k).gates.multiplications = 2 * k := by
  simp only [q4BundleCircuit, q4TCircuit, Circuit.gates_bind,
    Circuit.gates_relabel, Circuit.gates,
    Circuit.gates_liftLeft, Circuit.gates_rightInput, Circuit.gates_priorOutput,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    q4Tower_multiplications, Circuit.gates_constructionX,
    Circuit.gates_constructionParameter]
  rw [gates_tCircuit_multiplications k 2
    (show ValidTCall k 2 from ⟨by omega, by omega⟩)]
  omega

/-- Height ledger of the crown bundle: the `Q_{4k+1}` output obeys the canonical
gadget bound and the retained quartic stays at depth two. -/
theorem multDepth_q4BundleCircuit_le (k : ℕ) (hk : 1 ≤ k) :
    ((q4BundleCircuit (R := R) k).multDepth Height.gadgetDepthEnv 0
        ≤ 2 * Nat.clog 2 (2 * (2 * k) + 1) + 1) ∧
      ((q4BundleCircuit (R := R) k).multDepth Height.gadgetDepthEnv 1 ≤ 2) := by
  have hT0 := multDepth_q4TCircuit_le (R := R) k 0
  have hT1 := multDepth_q4TCircuit_le (R := R) k 1
  have hc1 : Nat.clog 2 (2 * k) = Nat.clog 2 k + 1 := Height.clog_two_double k hk
  have hc2 : Nat.clog 2 (2 * (2 * k)) = Nat.clog 2 (2 * k) + 1 :=
    Height.clog_two_double (2 * k) (by omega)
  have hc3 : Nat.clog 2 (2 * (2 * k)) ≤ Nat.clog 2 (2 * (2 * k) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  constructor
  · rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
    simp only [q4BundleCircuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Circuit.constructionX, Circuit.constructionParameter, Circuit.input,
      Circuit.multDepth_wire, Height.denv_variable,
      Height.denv_parameter]
    omega
  · rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    simp only [q4BundleCircuit, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.priorOutput, Circuit.multDepth_input]
    exact (multDepth_q4Tower_le (R := R)).2.1

/-- The local crown bundle has the same `2k` multiplication count as `Q_{4k+1}`
alone, because its second output is an already-bound intermediate. -/
def q4BundleRealized [Nontrivial A] {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (θ : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    BundleRealization (R := R) H₂ H₄ θ (q4BundleOutput H₂ θ k) (2 * k) where
  circuit := q4BundleCircuit k
  eval_eq := by
    funext i
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · exact eval_q4BundleCircuit_zero hH₂m hH₂d θ k
    · exact eval_q4BundleCircuit_one hH₂m hH₂d θ k
  multiplication_count := q4BundleCircuit_multiplications k hk

end FastPoly.Cost.OddGadget
