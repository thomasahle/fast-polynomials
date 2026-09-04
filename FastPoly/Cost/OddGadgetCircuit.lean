import FastPoly.Cost.FillCircuit
import FastPoly.Cost.MersenneCircuitCount
import FastPoly.Cost.RealizationComposition
import FastPoly.Cost.TCircuitCount
import FastPoly.Section5.QFourKOne
import FastPoly.Examples.BarQGeneral
import FastPoly.Height.TCircuitDepth

/-!
# Semantic circuits for the odd auxiliary gadgets

This file compiles the three families used by `odd_gadget_dispatch`.  The quadratic
and quartic supplied by the caller are input wires, hence cost no gates here.  Every
intermediate which is used more than once is introduced by `Circuit.bind`.

The layer is characteristic-neutral: it proves polynomial identities and counts the
actual circuit syntax, but makes no invertibility or admissibility assumption.  Those
hypotheses belong to the decoding layer, not to evaluation.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace OddGadget

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private abbrev x : Circuit R ConstructionInput 1 := Circuit.constructionX
private abbrev h₂ : Circuit R ConstructionInput 1 := Circuit.constructionPower 1
private abbrev h₄ : Circuit R ConstructionInput 1 := Circuit.constructionPower 2
private abbrev a (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionParameter i

/-- The convention used by `Section6.Dispatch`: level one is the supplied quadratic,
and every other pre-existing level is represented by the supplied quartic.  Individual
branch compilers explicitly replace any levels that they use differently. -/
noncomputable def suppliedPowers (H₂ H₄ : A[X]) : ℕ → A[X] :=
  fun i => if i = 1 then H₂ else H₄

@[simp] theorem suppliedPowers_one (H₂ H₄ : A[X]) :
    suppliedPowers H₂ H₄ 1 = H₂ := by
  simp only [suppliedPowers, if_pos]

@[simp] theorem suppliedPowers_two (H₂ H₄ : A[X]) :
  suppliedPowers H₂ H₄ 2 = H₄ := by
  simp only [suppliedPowers, if_neg (show (2 : ℕ) ≠ 1 by norm_num)]

/-- Evaluation environment for a local odd gadget. -/
noncomputable def env (H₂ H₄ : A[X]) (theta : ℕ → A) :
    ConstructionInput → A[X] :=
  constructionEnv (suppliedPowers H₂ H₄) H₄ theta (fun _ => 0)

@[simp] private theorem eval_x (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (x (R := R)).eval (env H₂ H₄ theta) 0 = X := by
  rfl

@[simp] private theorem eval_h₂ (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (h₂ (R := R)).eval (env H₂ H₄ theta) 0 = H₂ := by
  simp only [h₂, env, Circuit.eval_constructionPower, suppliedPowers_one]

@[simp] private theorem eval_h₄ (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (h₄ (R := R)).eval (env H₂ H₄ theta) 0 = H₄ := by
  simp only [h₄, env, Circuit.eval_constructionPower, suppliedPowers_two]

@[simp] private theorem eval_a (H₂ H₄ : A[X]) (theta : ℕ → A) (i : ℕ) :
    (a (R := R) i).eval (env H₂ H₄ theta) 0 = C (theta i) := by
  rfl

/-- A cost-sensitive auxiliary-gadget witness.  Unlike a numerical schedule, this
structure contains the circuit which evaluates to the advertised polynomial. -/
structure Realization (H₂ H₄ : A[X]) (theta : ℕ → A) (Q : A[X])
    (multiplications : ℕ) where
  circuit : Circuit R ConstructionInput 1
  eval_eq : circuit.eval (env H₂ H₄ theta) 0 = Q
  multiplication_count : circuit.gates.multiplications = multiplications
  depth_le : circuit.multDepth Height.gadgetDepthEnv 0 ≤
    2 * Nat.clog 2 (2 * multiplications + 1) + 1

/-- Transport a realization along an equality of its advertised polynomial. -/
def Realization.copy {H₂ H₄ : A[X]} {theta : ℕ → A} {Q Q' : A[X]}
    {multiplications : ℕ}
    (h : Realization (R := R) H₂ H₄ theta Q multiplications) (hQ : Q = Q') :
    Realization (R := R) H₂ H₄ theta Q' multiplications :=
  { h with eval_eq := h.eval_eq.trans hQ }

/-! ## The affine and Mersenne bases -/

def oneCircuit : Circuit R ConstructionInput 1 := .add x (a 0)

def threeCircuit : Circuit R ConstructionInput 1 := peelCircuit 2

def sevenCircuit : Circuit R ConstructionInput 1 := peelCircuit 3

@[simp] theorem eval_oneCircuit (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (oneCircuit (R := R)).eval (env H₂ H₄ theta) 0 = X + C (theta 0) := by
  rfl

@[simp] theorem eval_threeCircuit (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (threeCircuit (R := R)).eval (env H₂ H₄ theta) 0 =
      FastPoly.peel (suppliedPowers H₂ H₄) 2 theta := by
  exact eval_peelCircuit (R := R) (suppliedPowers H₂ H₄) H₄ theta (fun _ => 0) 2

@[simp] theorem eval_sevenCircuit (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (sevenCircuit (R := R)).eval (env H₂ H₄ theta) 0 =
      FastPoly.peel (suppliedPowers H₂ H₄) 3 theta := by
  exact eval_peelCircuit (R := R) (suppliedPowers H₂ H₄) H₄ theta (fun _ => 0) 3

omit [CommRing R] in
@[simp] theorem oneCircuit_multiplications :
    (oneCircuit (R := R)).gates.multiplications = 0 := by
  rfl

omit [CommRing R] in
@[simp] theorem threeCircuit_multiplications :
    (threeCircuit (R := R)).gates.multiplications = 1 := by
  rw [threeCircuit, gates_peelCircuit_multiplications (R := R) 2 (by omega)]
  omega

omit [CommRing R] in
@[simp] theorem sevenCircuit_multiplications :
    (sevenCircuit (R := R)).gates.multiplications = 3 := by
  rw [sevenCircuit, gates_peelCircuit_multiplications (R := R) 3 (by omega)]
  omega

def oneRealized (H₂ H₄ : A[X]) (theta : ℕ → A) :
    Realization (R := R) H₂ H₄ theta (X + C (theta 0)) 0 where
  circuit := oneCircuit
  eval_eq := eval_oneCircuit H₂ H₄ theta
  multiplication_count := oneCircuit_multiplications
  depth_le := by
    show max (Height.gadgetDepthEnv .variable)
        (Height.gadgetDepthEnv (.parameter 0)) ≤ _
    simp

def threeRealized (H₂ H₄ : A[X]) (theta : ℕ → A) :
    Realization (R := R) H₂ H₄ theta
      (FastPoly.peel (suppliedPowers H₂ H₄) 2 theta) 1 where
  circuit := threeCircuit
  eval_eq := eval_threeCircuit H₂ H₄ theta
  multiplication_count := threeCircuit_multiplications
  depth_le := by
    have h := Height.multDepth_peelCircuit (R := R) Height.gadgetDp 2 2
      (by omega) (fun i hi _ => Height.gadgetDp_le i hi)
    have hc : 0 < Nat.clog 2 (2 * 1 + 1) := Nat.clog_pos (by omega) (by omega)
    exact h.trans (by omega)

def sevenRealized (H₂ H₄ : A[X]) (theta : ℕ → A) :
    Realization (R := R) H₂ H₄ theta
      (FastPoly.peel (suppliedPowers H₂ H₄) 3 theta) 3 where
  circuit := sevenCircuit
  eval_eq := eval_sevenCircuit H₂ H₄ theta
  multiplication_count := sevenCircuit_multiplications
  depth_le := by
    have h := Height.multDepth_peelCircuit (R := R) Height.gadgetDp 2 3
      (by omega) (fun i hi _ => Height.gadgetDp_le i hi)
    have hc : 0 < Nat.clog 2 (2 * 3 + 1) := Nat.clog_pos (by omega) (by omega)
    exact h.trans (by omega)

/-! ## The `4k+1` gadget -/

/-- Produce, in order, the shifted quadratic, its constructed quartic, and the
scalar-shifted quartic.  The quartic is computed by one difference-of-squares gate. -/
def q4Tower : Circuit R ConstructionInput 3 :=
  let H₂' := .add h₂ (a 1)
  .bind H₂' <|
    let h₂' := Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 1)
    let old (p : Circuit R ConstructionInput 1) := p.liftLeft
    let H₄' := Circuit.diffSquareAdd h₂' (.add (old x) (old (a 2))) (old (a 3))
    .bind H₄' <|
      let h₂'' := Circuit.priorOutput (R := R) (n := 1) (0 : Fin 1)
      let h₄' := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 1)) (0 : Fin 1)
      .fork h₂'' (.fork h₄' (.add h₄' (a 4).liftLeft.liftLeft))

/-- Relabel a local `T_{k,4}` call to the three outputs of `q4Tower`.  Values outside
levels one and two are `x`, exactly as in `crownHp`. -/
def q4TLabel : ConstructionInput → Sum ConstructionInput (Fin 3)
  | .variable => .inl .variable
  | .power i => if i = 1 then .inr 0 else if i = 2 then .inr 1 else .inl .variable
  | .shiftedPower => .inr 2
  | .parameter i => .inl (.parameter (5 + i))
  | .source i => .inl (.source i)

def q4TCircuit (k : ℕ) : Circuit R (Sum ConstructionInput (Fin 3)) 2 :=
  (tCircuit k 2).relabel q4TLabel

/-- Actual circuit for `q4k1`: one constructed quartic, the shared `T_{k,4}` call,
and the final product `(x+β)T¹`. -/
def q4Circuit (k : ℕ) : Circuit R ConstructionInput 1 :=
  .bind q4Tower <|
    .bind (q4TCircuit k) <|
      let old (p : Circuit R ConstructionInput 1) := p.liftLeft.liftLeft
      let T₁ := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 3)) (0 : Fin 2)
      let T₂ := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 3)) (1 : Fin 2)
      .add (.mul (.add (old x) (old (a 0))) T₁) T₂

@[simp] theorem eval_q4Tower_zero (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (q4Tower (R := R)).eval (env H₂ H₄ theta) 0 = H₂ + C (theta 1) := by
  rw [q4Tower, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_triple_zero,
    Circuit.eval_priorOutput]
  simp only [h₂, a, env, Circuit.eval_add, Circuit.eval_constructionPower,
    Circuit.eval_constructionParameter, suppliedPowers_one]

@[simp] theorem eval_q4Tower_one (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (q4Tower (R := R)).eval (env H₂ H₄ theta) 1 =
      (H₂ + C (theta 1)) ^ 2 - (X + C (theta 2)) ^ 2 + C (theta 3) := by
  rw [q4Tower, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_triple_one,
    Circuit.eval_rightInput, Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput,
    h₂, x, a, env, Circuit.eval_constructionPower, Circuit.eval_constructionX,
    Circuit.eval_constructionParameter, suppliedPowers_one]
  ring

@[simp] theorem eval_q4Tower_two (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (q4Tower (R := R)).eval (env H₂ H₄ theta) 2 =
      (H₂ + C (theta 1)) ^ 2 - (X + C (theta 2)) ^ 2 +
        C (theta 3) + C (theta 4) := by
  rw [q4Tower, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_triple_two,
    Circuit.eval_add, Circuit.eval_rightInput, Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput,
    h₂, x, a, env, Circuit.eval_constructionPower, Circuit.eval_constructionX,
    Circuit.eval_constructionParameter, suppliedPowers_one]
  ring

theorem eval_q4TCircuit [Nontrivial A] {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (theta : ℕ → A) (k : ℕ) :
    let values := (q4Tower (R := R)).eval (env H₂ H₄ theta)
    ((q4TCircuit (R := R) k).eval (Sum.elim (env H₂ H₄ theta) values) 0,
      (q4TCircuit (R := R) k).eval (Sum.elim (env H₂ H₄ theta) values) 1) =
      FastPoly.Tpair
        (FastPoly.crownHp (H₂.coeff 1) (H₂.coeff 0 + theta 1)
          (theta 2) (theta 3))
        (FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + theta 1)
          (theta 2) (theta 3) + C (theta 4))
        k 2 (fun i => theta (5 + i)) := by
  dsimp only
  rw [q4TCircuit, Circuit.eval_relabel]
  have hshift := FastPoly.crownH2_shift hH₂m hH₂d (theta 1)
  have henv :
      Sum.elim (env H₂ H₄ theta) ((q4Tower (R := R)).eval (env H₂ H₄ theta)) ∘
          q4TLabel =
        constructionEnv
          (FastPoly.crownHp (H₂.coeff 1) (H₂.coeff 0 + theta 1)
            (theta 2) (theta 3))
          (FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + theta 1)
            (theta 2) (theta 3) + C (theta 4))
          (fun i => theta (5 + i)) (fun _ => 0) := by
    funext input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi1 : i = 1
        · subst i
          simp only [q4TLabel, if_pos, Function.comp_apply, Sum.elim_inr,
            constructionEnv_power, FastPoly.crownHp_one, eval_q4Tower_zero]
          exact hshift
        · by_cases hi2 : i = 2
          · subst i
            simp only [q4TLabel, hi1, if_false, if_pos, Function.comp_apply,
              Sum.elim_inr, constructionEnv_power, FastPoly.crownHp_two,
              eval_q4Tower_one, FastPoly.crownH4]
            rw [hshift]
          · simp only [q4TLabel, hi1, hi2, if_false, Function.comp_apply,
              Sum.elim_inl, env, constructionEnv_variable, constructionEnv_power,
              FastPoly.crownHp]
    | shiftedPower =>
        simp only [q4TLabel, Function.comp_apply, Sum.elim_inr,
          constructionEnv_shiftedPower, eval_q4Tower_two, FastPoly.crownH4]
        rw [hshift]
    | parameter i => rfl
    | source i => rfl
  rw [henv]
  exact eval_tCircuit (R := R)
    (FastPoly.crownHp (H₂.coeff 1) (H₂.coeff 0 + theta 1) (theta 2) (theta 3))
    (FastPoly.crownH4 (H₂.coeff 1) (H₂.coeff 0 + theta 1)
      (theta 2) (theta 3) + C (theta 4))
    (fun i => theta (5 + i)) k 2

theorem eval_q4Circuit [Nontrivial A] {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (theta : ℕ → A) (k : ℕ) :
    (q4Circuit (R := R) k).eval (env H₂ H₄ theta) 0 =
      FastPoly.q4k1 H₂ (theta 1) (theta 4) (theta 2) (theta 3) (theta 0)
        k (fun i => theta (5 + i)) := by
  rw [q4Circuit, Circuit.eval_bind, Circuit.eval_bind]
  have hpair := eval_q4TCircuit (R := R) (H₄ := H₄) hH₂m hH₂d theta k
  have h₁ := congrArg Prod.fst hpair
  have h₂' := congrArg Prod.snd hpair
  dsimp only at h₁ h₂'
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput, eval_x, eval_a, q4k1]
  rw [h₁, h₂']

omit [CommRing R] in
@[simp] theorem q4Tower_multiplications :
    (q4Tower (R := R)).gates.multiplications = 1 := by
  simp only [q4Tower, Circuit.gates_bind,
    GateCount.add_multiplications, Circuit.gates_diffSquareAdd_multiplications,
    Circuit.gates_rightInput, Circuit.gates_priorOutput, Circuit.gates_liftLeft,
    Circuit.gates, GateCount.zero_multiplications, GateCount.adds_multiplications,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]

theorem q4Circuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (q4Circuit (R := R) k).gates.multiplications = 2 * k := by
  simp only [q4Circuit, q4TCircuit, Circuit.gates_bind, Circuit.gates_relabel,
    Circuit.gates, Circuit.gates_liftLeft, Circuit.gates_rightInput,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    q4Tower_multiplications, Circuit.gates_constructionX,
    Circuit.gates_constructionParameter]
  rw [gates_tCircuit_multiplications k 2
    (show ValidTCall k 2 from ⟨by omega, by omega⟩)]
  omega

omit [CommRing R] in
theorem multDepth_q4Tower_le :
    ((q4Tower (R := R)).multDepth Height.gadgetDepthEnv 0 ≤ 1) ∧
      ((q4Tower (R := R)).multDepth Height.gadgetDepthEnv 1 ≤ 2) ∧
      ((q4Tower (R := R)).multDepth Height.gadgetDepthEnv 2 ≤ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show (0 : Fin 3) = Fin.castAdd 2 (0 : Fin 1) from rfl]
    simp only [q4Tower, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Circuit.priorOutput,
      Circuit.multDepth_add,
      Circuit.constructionPower, Circuit.constructionParameter, Circuit.input,
      Circuit.multDepth_wire, Sum.elim_inl, Sum.elim_inr,
      Height.denv_power, Height.denv_parameter, Height.gadgetDp_one]
    omega
  · rw [show (1 : Fin 3) = Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1)) from rfl]
    simp only [q4Tower, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Fin.addCases_right, Height.multDepth_diffSquareAdd,
      Circuit.multDepth_add, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.constructionX,
      Circuit.constructionPower, Circuit.constructionParameter, Circuit.input,
      Circuit.multDepth_wire,
      Height.denv_variable, Height.denv_power, Height.denv_parameter,
      Height.gadgetDp_one]
    omega
  · rw [show (2 : Fin 3) = Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1)) from rfl]
    simp only [q4Tower, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_right, Height.multDepth_diffSquareAdd,
      Circuit.multDepth_add, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.constructionX,
      Circuit.constructionPower, Circuit.constructionParameter, Circuit.input,
      Circuit.multDepth_wire,
      Height.denv_variable, Height.denv_power, Height.denv_parameter,
      Height.gadgetDp_one]
    omega

/-- Depth of the local `T` call over the crown tower: the tower depths satisfy the
canonical invariant, so both outputs obey the `tDB` closed form. -/
theorem multDepth_q4TCircuit_le (k : ℕ) (j : Fin 2) :
    (q4TCircuit (R := R) k).multDepth
      (Sum.elim Height.gadgetDepthEnv
        ((q4Tower (R := R)).multDepth Height.gadgetDepthEnv)) j
      ≤ 2 * Nat.clog 2 k + 3 := by
  obtain ⟨h0, h1, h2s⟩ := multDepth_q4Tower_le (R := R)
  set dT : Fin 3 → ℕ := (q4Tower (R := R)).multDepth Height.gadgetDepthEnv
    with hdTdef
  set dp' : ℕ → ℕ :=
    fun i => if i = 1 then dT 0 else if i = 2 then dT 1 else 0 with hdp'def
  have henv : (Sum.elim Height.gadgetDepthEnv dT) ∘ q4TLabel
      = Height.denv dp' (dT 2) := by
    funext input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi1 : i = 1
        · subst hi1; rfl
        · by_cases hi2 : i = 2
          · subst hi2; rfl
          · simp only [q4TLabel, hi1, hi2, if_false, Function.comp_apply,
              Sum.elim_inl, Height.denv_power, Height.denv_variable, hdp'def]
    | shiftedPower => rfl
    | parameter i => rfl
    | source i => rfl
  rw [q4TCircuit, Circuit.multDepth_relabel, henv]
  refine (Height.multDepth_tCircuit_le k 2 dp' (dT 2) (by omega) ?_ h2s j).trans
    ?_
  · intro i hi
    by_cases hi1 : i = 1
    · subst hi1; simpa [hdp'def] using h0
    · by_cases hi2 : i = 2
      · subst hi2; simpa [hdp'def] using h1
      · simp [hdp'def, hi1, hi2]
  · have := Height.tDB_le k k 2 (by omega)
    omega

private theorem multDepth_q4Circuit_le (k : ℕ) (hk : 1 ≤ k) :
    (q4Circuit (R := R) k).multDepth Height.gadgetDepthEnv 0 ≤
      2 * Nat.clog 2 (2 * (2 * k) + 1) + 1 := by
  have hT0 := multDepth_q4TCircuit_le (R := R) k 0
  have hT1 := multDepth_q4TCircuit_le (R := R) k 1
  have hc1 : Nat.clog 2 (2 * k) = Nat.clog 2 k + 1 := Height.clog_two_double k hk
  have hc2 : Nat.clog 2 (2 * (2 * k)) = Nat.clog 2 (2 * k) + 1 :=
    Height.clog_two_double (2 * k) (by omega)
  have hc3 : Nat.clog 2 (2 * (2 * k)) ≤ Nat.clog 2 (2 * (2 * k) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  simp only [q4Circuit, Circuit.multDepth_bind, Circuit.multDepth_add,
    Circuit.multDepth_mul, Circuit.multDepth_liftLeft,
    Circuit.multDepth_rightInput, Circuit.constructionX,
    Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
    Height.denv_variable, Height.denv_parameter]
  omega

def q4Realized [Nontrivial A] {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta
      (FastPoly.q4k1 H₂ (theta 1) (theta 4) (theta 2) (theta 3) (theta 0)
        k (fun i => theta (5 + i))) (2 * k) where
  circuit := q4Circuit k
  eval_eq := eval_q4Circuit hH₂m hH₂d theta k
  multiplication_count := q4Circuit_multiplications k hk
  depth_le := multDepth_q4Circuit_le k hk

/-! ## The `8k+3` known-powers gadget at level two -/

/-- The perturbed quartic and its scalar shift.  The level-one Mersenne circuit is
bound once even though it has no multiplication gates. -/
def knownPowerPair : Circuit R ConstructionInput 2 :=
  .bind ((peelCircuit 1).reindexConstructionParameters (fun i => 5 + i)) <|
    let q := Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 1)
    let old (p : Circuit R ConstructionInput 1) := p.liftLeft
    let H₄' := .add (old h₄) q
    .fork H₄' (.add H₄' (old (a 6)))

def knownTCircuit (k : ℕ) : Circuit R (Sum ConstructionInput (Fin 2)) 2 :=
  recurseWithPowerPair 2 (fun i => 7 + i) 0 1 (tCircuit (2 * k) 2)

def knownCircuit (k : ℕ) : Circuit R ConstructionInput 1 :=
  .bind knownPowerPair <|
    .bind (knownTCircuit k) <|
      let old (p : Circuit R ConstructionInput 1) := p.liftLeft.liftLeft
      let source : Circuit R (Sum (Sum ConstructionInput (Fin 2)) (Fin 2)) 2 :=
        .fork
          (Circuit.rightInput (R := R) (ι := Sum ConstructionInput (Fin 2))
            (0 : Fin 2))
          (Circuit.rightInput (R := R) (ι := Sum ConstructionInput (Fin 2))
            (1 : Fin 2))
      Circuit.finishFill (old x) (old h₂) (old (a 0)) (old (a 1)) (old (a 2))
        (old (a 3)) (old (a 4)) source

/-- Named normal form of the local `8k+3` expression in `odd_gadget_dispatch`.
At level `l=2` the intervening fill chain is the identity. -/
noncomputable def knownValue (H₂ H₄ : A[X]) (k : ℕ) (theta : ℕ → A) : A[X] :=
  let Hp := suppliedPowers H₂ H₄
  let q := FastPoly.peel Hp 1 (fun i => theta (5 + i))
  let S := FastPoly.Tpair (Function.update Hp 2 (H₄ + q))
    (H₄ + q + C (theta 6)) (2 * k) 2 (fun i => theta (7 + i))
  (X + C (theta 0)) * ((H₂ + C (theta 1)) * S.1 + C (theta 4)) +
    ((H₂ + C (theta 2)) * S.2 + C (theta 3))

private theorem eval_knownMers (H₂ H₄ : A[X]) (theta : ℕ → A) :
    ((peelCircuit (R := R) 1).reindexConstructionParameters (fun i => 5 + i)).eval
        (env H₂ H₄ theta) 0 =
      FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i)) := by
  rw [env, Circuit.eval_reindexConstructionParameters]
  exact eval_peelCircuit (R := R) (suppliedPowers H₂ H₄) H₄
    (fun i => theta (5 + i)) (fun _ => 0) 1

@[simp] theorem eval_knownPowerPair_zero (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (knownPowerPair (R := R)).eval (env H₂ H₄ theta) 0 =
      H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i)) := by
  rw [knownPowerPair, Circuit.eval_bind, Circuit.eval_fork_zero]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput,
    eval_h₄, eval_knownMers]

@[simp] theorem eval_knownPowerPair_one (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (knownPowerPair (R := R)).eval (env H₂ H₄ theta) 1 =
      H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i)) +
        C (theta 6) := by
  rw [knownPowerPair, Circuit.eval_bind, Circuit.eval_fork_one]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput,
    eval_h₄, eval_a, eval_knownMers]

theorem eval_knownTCircuit (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) :
    let values := (knownPowerPair (R := R)).eval (env H₂ H₄ theta)
    ((knownTCircuit (R := R) k).eval (Sum.elim (env H₂ H₄ theta) values) 0,
      (knownTCircuit (R := R) k).eval (Sum.elim (env H₂ H₄ theta) values) 1) =
      FastPoly.Tpair
        (Function.update (suppliedPowers H₂ H₄) 2
          (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
            (fun i => theta (5 + i))))
        (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1
          (fun i => theta (5 + i)) + C (theta 6))
        (2 * k) 2 (fun i => theta (7 + i)) := by
  dsimp only
  rw [knownTCircuit, recurseWithPowerPair, Circuit.eval_relabel]
  have henv :
      Sum.elim (env H₂ H₄ theta)
          ((knownPowerPair (R := R)).eval (env H₂ H₄ theta)) ∘
          ConstructionInput.withPowerPair 2 (fun i => 7 + i) 0 1 =
        constructionEnv
          (Function.update (suppliedPowers H₂ H₄) 2
            ((knownPowerPair (R := R)).eval (env H₂ H₄ theta) 0))
          ((knownPowerPair (R := R)).eval (env H₂ H₄ theta) 1)
          (fun i => theta (7 + i)) (fun _ => 0) := by
    simpa only [env] using
      constructionEnv_withPowerPair (suppliedPowers H₂ H₄) H₄ theta
        (fun _ => 0) ((knownPowerPair (R := R)).eval (env H₂ H₄ theta))
        2 (fun i => 7 + i) 0 1
  rw [henv, eval_knownPowerPair_zero, eval_knownPowerPair_one]
  exact eval_tCircuit (R := R)
    (Function.update (suppliedPowers H₂ H₄) 2
      (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i))))
    (H₄ + FastPoly.peel (suppliedPowers H₂ H₄) 1 (fun i => theta (5 + i)) +
      C (theta 6)) (fun i => theta (7 + i)) (2 * k) 2

theorem eval_knownCircuit (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) :
    (knownCircuit (R := R) k).eval (env H₂ H₄ theta) 0 =
      knownValue H₂ H₄ k theta := by
  rw [knownCircuit, Circuit.eval_bind, Circuit.eval_bind]
  have hpair := eval_knownTCircuit (R := R) H₂ H₄ theta k
  have h₁ := congrArg Prod.fst hpair
  have h₂' := congrArg Prod.snd hpair
  dsimp only at h₁ h₂'
  simp only [Circuit.eval_finishFill, Circuit.eval_fork_zero, Circuit.eval_fork_one,
    Circuit.eval_rightInput,
    Circuit.eval_liftLeft, knownValue,
    eval_h₂, eval_x, eval_a]
  rw [h₁, h₂']

omit [CommRing R] in
@[simp] theorem knownPowerPair_multiplications :
    (knownPowerPair (R := R)).gates.multiplications = 0 := by
  simp only [knownPowerPair, Circuit.gates_bind,
    Circuit.gates, GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, Circuit.gates_liftLeft,
    Circuit.gates_rightInput, Circuit.gates_reindexConstructionParameters,
    h₄, a, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]
  rw [gates_peelCircuit_multiplications (R := R) 1 (by omega),
    show 1 - 1 = 0 by omega]
  rfl

theorem knownCircuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (knownCircuit (R := R) k).gates.multiplications = 4 * k + 1 := by
  simp only [knownCircuit, knownTCircuit, Circuit.gates_bind,
    gates_recurseWithPowerPair, Circuit.finishFill,
    Circuit.gates,
    Circuit.gates_rightInput, Circuit.gates_liftLeft,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    knownPowerPair_multiplications, x, h₂, a,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]
  rw [gates_tCircuit_multiplications (2 * k) 2
    (show ValidTCall (2 * k) 2 from ⟨by omega, by omega⟩),
    show 2 - 1 = 1 by omega, pow_one]
  omega

omit [CommRing R] in
private theorem multDepth_knownPowerPair_le :
    ((knownPowerPair (R := R)).multDepth Height.gadgetDepthEnv 0 ≤ 2) ∧
      ((knownPowerPair (R := R)).multDepth Height.gadgetDepthEnv 1 ≤ 2) := by
  have hq : ((peelCircuit (R := R) 1).reindexConstructionParameters
      (fun i => 5 + i)).multDepth Height.gadgetDepthEnv 0 = 0 := by
    rw [Height.multDepth_reindexConstructionParameters]
    rfl
  constructor
  · rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
    simp only [knownPowerPair, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Circuit.multDepth_add, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.constructionPower,
      Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
      hq, Height.denv_power, Height.denv_parameter,
      Height.gadgetDp_two]
    omega
  · rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    simp only [knownPowerPair, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.multDepth_add, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.constructionPower,
      Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
      hq, Height.denv_power, Height.denv_parameter,
      Height.gadgetDp_two]
    omega

private theorem multDepth_knownCircuit_le (k : ℕ) (hk : 1 ≤ k) :
    (knownCircuit (R := R) k).multDepth Height.gadgetDepthEnv 0 ≤
      2 * Nat.clog 2 (2 * (4 * k + 1) + 1) + 1 := by
  obtain ⟨hp0, hp1⟩ := multDepth_knownPowerPair_le (R := R)
  set dP : Fin 2 → ℕ :=
    (knownPowerPair (R := R)).multDepth Height.gadgetDepthEnv with hdPdef
  have hT : ∀ j : Fin 2, (tCircuit (R := R) (2 * k) 2).multDepth
      (Height.denv (Function.update Height.gadgetDp 2 (dP 0)) (dP 1)) j
        ≤ 2 * Nat.clog 2 (2 * k) + 3 := by
    intro j
    refine (Height.multDepth_tCircuit_le (2 * k) 2 _ _ (by omega) ?_ hp1 j).trans
      ?_
    · intro i hi
      by_cases hi2 : i = 2
      · subst hi2; simpa [Function.update_self] using hp0
      · rw [Function.update_of_ne hi2]
        exact Height.gadgetDp_le i hi
    · have := Height.tDB_le (2 * k) (2 * k) 2 (by omega)
      omega
  have hT0 := hT 0
  have hT1 := hT 1
  have hc1 : Nat.clog 2 (2 * k) = Nat.clog 2 k + 1 := Height.clog_two_double k hk
  have hc2 : Nat.clog 2 (2 * (2 * k)) = Nat.clog 2 (2 * k) + 1 :=
    Height.clog_two_double (2 * k) (by omega)
  have hc3 : Nat.clog 2 (2 * (2 * (2 * k))) = Nat.clog 2 (2 * (2 * k)) + 1 :=
    Height.clog_two_double (2 * (2 * k)) (by omega)
  have hc4 : Nat.clog 2 (2 * (2 * (2 * k))) ≤ Nat.clog 2 (2 * (4 * k + 1) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  simp only [knownCircuit, Circuit.multDepth_bind, knownTCircuit, ← hdPdef,
    Height.multDepth_recurseWithPowerPair, Circuit.finishFill,
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

def knownRealized (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta (knownValue H₂ H₄ k theta) (4 * k + 1) where
  circuit := knownCircuit k
  eval_eq := eval_knownCircuit H₂ H₄ theta k
  multiplication_count := knownCircuit_multiplications k hk
  depth_le := multDepth_knownCircuit_le k hk

/-! ## The barred `8k+7` gadget -/

/-- The shared octic and its scalar shift. -/
def barredPowerPair : Circuit R ConstructionInput 2 :=
  let H₈ := .add
    (.mul (.add h₄ (.add x (a 1))) (.add h₄ (.add h₂ (a 2)))) (a 0)
  .bind H₈ <|
    let h₈ := Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 1)
    .fork h₈ (.add h₈ (a 3).liftLeft)

/-- The `T_{k,8}` tower is exactly `(H₂,H₄,H₈)` and zero elsewhere. -/
def barredTLabel : ConstructionInput → Sum ConstructionInput (Fin 2)
  | .variable => .inl .variable
  | .power i =>
      if i = 1 then .inl (.power 1)
      else if i = 2 then .inl (.power 2)
      else if i = 3 then .inr 0
      else .inl (.source 0)
  | .shiftedPower => .inr 1
  | .parameter i => .inl (.parameter (4 + i))
  | .source i => .inl (.source i)

def barredTCircuit (k : ℕ) : Circuit R (Sum ConstructionInput (Fin 2)) 2 :=
  (tCircuit k 3).relabel barredTLabel

/-- First product of the six-product `A₄` crown. -/
def Circuit.a4Seed {I : Type*}
    (x H₂ a₃ a₄ a₅ : Circuit R I 1) : Circuit R I 1 :=
  .add (.mul (.add x a₅) (.add H₂ a₄)) a₃

/-- The two quartic columns, evaluated after the cubic seed has been bound. -/
def Circuit.a4Middle {I : Type*}
    (H₄ S₁ S₂ a₂ b₃ b₄ : Circuit R I 1) : Circuit R (Sum I (Fin 1)) 2 :=
  let q₃ := Circuit.rightInput (R := R) (ι := I) (0 : Fin 1)
  let old (p : Circuit R I 1) := p.liftLeft
  .fork
    (.add (.mul (.add (old H₄) (old b₃)) (old S₁)) q₃)
    (.add (.mul (.add (old H₄) (old b₄)) (old S₂)) (old a₂))

/-- The two quadratic columns, evaluated after the quartic columns have been bound. -/
def Circuit.a4Columns {I : Type*}
    (H₂ a₀ a₁ b₁ b₂ : Circuit R I 1) :
    Circuit R (Sum (Sum I (Fin 1)) (Fin 2)) 2 :=
  let u₀ := Circuit.rightInput (R := R) (ι := Sum I (Fin 1)) (0 : Fin 2)
  let v₀ := Circuit.rightInput (R := R) (ι := Sum I (Fin 1)) (1 : Fin 2)
  let oldest (p : Circuit R I 1) := p.liftLeft.liftLeft
  .fork
    (.add (.mul (.add (oldest H₂) (oldest b₁)) u₀) (oldest a₁))
    (.add (.mul (.add (oldest H₂) (oldest b₂)) v₀) (oldest a₀))

/-- Final product of the `A₄` crown. -/
def Circuit.a4Finish {I : Type*} (x b₀ : Circuit R I 1) :
    Circuit R (Sum (Sum (Sum I (Fin 1)) (Fin 2)) (Fin 2)) 1 :=
  let c₁ := Circuit.rightInput (R := R)
    (ι := Sum (Sum I (Fin 1)) (Fin 2)) (0 : Fin 2)
  let c₂ := Circuit.rightInput (R := R)
    (ι := Sum (Sum I (Fin 1)) (Fin 2)) (1 : Fin 2)
  let first (p : Circuit R I 1) := p.liftLeft.liftLeft.liftLeft
  .add (.mul (.add (first x) (first b₀)) c₁) c₂

/-- Six-product `A₄` outer crown.  Each shared column is represented by one explicit
binding, so its cost and its semantic reuse are visible in the syntax. -/
def Circuit.a4Outer {I : Type*}
    (x H₂ H₄ S₁ S₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : Circuit R I 1) :
    Circuit R I 1 :=
  .bind (Circuit.a4Seed x H₂ a₃ a₄ a₅) <|
    .bind (Circuit.a4Middle H₄ S₁ S₂ a₂ b₃ b₄) <|
      .bind (Circuit.a4Columns H₂ a₀ a₁ b₁ b₂) (Circuit.a4Finish x b₀)

@[simp] theorem Circuit.eval_a4Seed {I : Type*}
    (x H₂ a₃ a₄ a₅ : Circuit R I 1) (input : I → A[X]) :
    (Circuit.a4Seed x H₂ a₃ a₄ a₅).eval input 0 =
      (x.eval input 0 + a₅.eval input 0) *
        (H₂.eval input 0 + a₄.eval input 0) + a₃.eval input 0 := by
  rfl

@[simp] theorem Circuit.eval_a4Middle_zero {I : Type*}
    (H₄ S₁ S₂ a₂ b₃ b₄ : Circuit R I 1) (input : I → A[X])
    (seed : Fin 1 → A[X]) :
    (Circuit.a4Middle H₄ S₁ S₂ a₂ b₃ b₄).eval
        (Sum.elim input seed) 0 =
      (H₄.eval input 0 + b₃.eval input 0) * S₁.eval input 0 + seed 0 := by
  rw [Circuit.a4Middle, Circuit.eval_fork_zero]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]

@[simp] theorem Circuit.eval_a4Middle_one {I : Type*}
    (H₄ S₁ S₂ a₂ b₃ b₄ : Circuit R I 1) (input : I → A[X])
    (seed : Fin 1 → A[X]) :
    (Circuit.a4Middle H₄ S₁ S₂ a₂ b₃ b₄).eval
        (Sum.elim input seed) 1 =
      (H₄.eval input 0 + b₄.eval input 0) * S₂.eval input 0 + a₂.eval input 0 := by
  rw [Circuit.a4Middle, Circuit.eval_fork_one]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft]

@[simp] theorem Circuit.eval_a4Columns_zero {I : Type*}
    (H₂ a₀ a₁ b₁ b₂ : Circuit R I 1) (input : I → A[X])
    (seed : Fin 1 → A[X])
    (middle : Fin 2 → A[X]) :
    (Circuit.a4Columns H₂ a₀ a₁ b₁ b₂).eval
        (Sum.elim (Sum.elim input seed) middle) 0 =
      (H₂.eval input 0 + b₁.eval input 0) * middle 0 + a₁.eval input 0 := by
  rw [Circuit.a4Columns, Circuit.eval_fork_zero]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]

@[simp] theorem Circuit.eval_a4Columns_one {I : Type*}
    (H₂ a₀ a₁ b₁ b₂ : Circuit R I 1) (input : I → A[X])
    (seed : Fin 1 → A[X])
    (middle : Fin 2 → A[X]) :
    (Circuit.a4Columns H₂ a₀ a₁ b₁ b₂).eval
        (Sum.elim (Sum.elim input seed) middle) 1 =
      (H₂.eval input 0 + b₂.eval input 0) * middle 1 + a₀.eval input 0 := by
  rw [Circuit.a4Columns, Circuit.eval_fork_one]
  simp only [Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]

@[simp] theorem Circuit.eval_a4Finish {I : Type*} (x b₀ : Circuit R I 1)
    (input : I → A[X]) (seed : Fin 1 → A[X])
    (middle columns : Fin 2 → A[X]) :
    (Circuit.a4Finish x b₀).eval
        (Sum.elim (Sum.elim (Sum.elim input seed) middle) columns) 0 =
      (x.eval input 0 + b₀.eval input 0) * columns 0 + columns 1 := by
  simp only [Circuit.a4Finish, Circuit.eval_add, Circuit.eval_mul,
    Circuit.eval_liftLeft, Circuit.eval_rightInput]

theorem Circuit.eval_a4Outer {I : Type*}
    (x H₂ H₄ S₁ S₂ a₀ a₁ a₂ a₃ a₄ a₅ b₀ b₁ b₂ b₃ b₄ : Circuit R I 1)
    (input : I → A[X]) :
    (Circuit.a4Outer x H₂ H₄ S₁ S₂ a₀ a₁ a₂ a₃ a₄ a₅
      b₀ b₁ b₂ b₃ b₄).eval input 0 =
      (x.eval input 0 + b₀.eval input 0) *
          ((H₂.eval input 0 + b₁.eval input 0) *
              ((H₄.eval input 0 + b₃.eval input 0) * S₁.eval input 0 +
                ((x.eval input 0 + a₅.eval input 0) *
                    (H₂.eval input 0 + a₄.eval input 0) + a₃.eval input 0)) +
            a₁.eval input 0) +
        ((H₂.eval input 0 + b₂.eval input 0) *
            ((H₄.eval input 0 + b₄.eval input 0) * S₂.eval input 0 +
              a₂.eval input 0) + a₀.eval input 0) := by
  rw [Circuit.a4Outer, Circuit.eval_bind, Circuit.eval_bind, Circuit.eval_bind]
  simp only [Circuit.eval_a4Finish, Circuit.eval_a4Columns_zero,
    Circuit.eval_a4Columns_one, Circuit.eval_a4Middle_zero,
    Circuit.eval_a4Middle_one, Circuit.eval_a4Seed]

private abbrev BarInput := Sum (Sum ConstructionInput (Fin 2)) (Fin 2)

private def barOld (p : Circuit R ConstructionInput 1) : Circuit R BarInput 1 :=
  p.liftLeft.liftLeft

private def barT (i : Fin 2) : Circuit R BarInput 1 :=
  Circuit.rightInput (R := R) (ι := Sum ConstructionInput (Fin 2)) i

def barredOuter (k : ℕ) : Circuit R BarInput 1 :=
  Circuit.a4Outer (barOld x) (barOld h₂) (barOld h₄) (barT 0) (barT 1)
    (barOld (a (8 * k - 4))) (barOld (a (8 * k - 3)))
    (barOld (a (8 * k - 2))) (barOld (a (8 * k - 1)))
    (barOld (a (8 * k))) (barOld (a (8 * k + 1)))
    (barOld (a (8 * k + 2))) (barOld (a (8 * k + 3)))
    (barOld (a (8 * k + 4))) (barOld (a (8 * k + 5)))
    (barOld (a (8 * k + 6)))

def barredCircuit (k : ℕ) : Circuit R ConstructionInput 1 :=
  .bind barredPowerPair (.bind (barredTCircuit k) (barredOuter k))

@[simp] theorem eval_barredPowerPair_zero (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (barredPowerPair (R := R)).eval (env H₂ H₄ theta) 0 =
      FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0) := by
  rw [barredPowerPair, Circuit.eval_bind, Circuit.eval_fork_zero]
  simp only [
    Circuit.eval_add, Circuit.eval_mul,
    Circuit.eval_rightInput, eval_h₄, eval_x, eval_h₂, eval_a,
    FastPoly.BarQGeneral.H8]

@[simp] theorem eval_barredPowerPair_one (H₂ H₄ : A[X]) (theta : ℕ → A) :
    (barredPowerPair (R := R)).eval (env H₂ H₄ theta) 1 =
      FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0) + C (theta 3) := by
  rw [barredPowerPair, Circuit.eval_bind, Circuit.eval_fork_one]
  simp only [
    Circuit.eval_add, Circuit.eval_mul, Circuit.eval_liftLeft,
    Circuit.eval_rightInput, eval_h₄, eval_x, eval_h₂, eval_a,
    FastPoly.BarQGeneral.H8]

theorem eval_barredTCircuit (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) :
    let values := (barredPowerPair (R := R)).eval (env H₂ H₄ theta)
    ((barredTCircuit (R := R) k).eval (Sum.elim (env H₂ H₄ theta) values) 0,
      (barredTCircuit (R := R) k).eval (Sum.elim (env H₂ H₄ theta) values) 1) =
      FastPoly.Tpair
        (FastPoly.BarQGeneral.tower H₂ H₄
          (FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0)))
        (FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0) + C (theta 3))
        k 3 (fun i => theta (4 + i)) := by
  dsimp only
  rw [barredTCircuit, Circuit.eval_relabel]
  have henv :
      Sum.elim (env H₂ H₄ theta)
          ((barredPowerPair (R := R)).eval (env H₂ H₄ theta)) ∘ barredTLabel =
        constructionEnv
          (FastPoly.BarQGeneral.tower H₂ H₄
            (FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0)))
          (FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0) + C (theta 3))
          (fun i => theta (4 + i)) (fun _ => 0) := by
    funext input
    cases input with
    | «variable» => rfl
    | power i =>
        rcases i with _ | _ | _ | i
        · rfl
        · rfl
        · rfl
        · rcases i with _ | i
          · change (barredPowerPair (R := R)).eval (env H₂ H₄ theta) 0 =
              FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0)
            exact eval_barredPowerPair_zero (R := R) H₂ H₄ theta
          · rfl
    | shiftedPower =>
        simp only [barredTLabel, Function.comp_apply, Sum.elim_inr,
          constructionEnv_shiftedPower, eval_barredPowerPair_one]
    | parameter i => rfl
    | source i => rfl
  rw [henv]
  exact eval_tCircuit (R := R)
    (FastPoly.BarQGeneral.tower H₂ H₄
      (FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0)))
    (FastPoly.BarQGeneral.H8 H₂ H₄ (theta 1) (theta 2) (theta 0) + C (theta 3))
    (fun i => theta (4 + i)) k 3

theorem eval_barredOuter (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) :
    let powerValues := (barredPowerPair (R := R)).eval (env H₂ H₄ theta)
    let tValues := (barredTCircuit (R := R) k).eval
      (Sum.elim (env H₂ H₄ theta) powerValues)
    (barredOuter (R := R) k).eval
      (Sum.elim (Sum.elim (env H₂ H₄ theta) powerValues) tValues) 0 =
      FastPoly.BarQGeneral.outer H₂ H₄ (tValues 0) (tValues 1)
        (theta (8 * k - 4)) (theta (8 * k - 3)) (theta (8 * k - 2))
        (theta (8 * k - 1)) (theta (8 * k)) (theta (8 * k + 1))
        (theta (8 * k + 2)) (theta (8 * k + 3)) (theta (8 * k + 4))
        (theta (8 * k + 5)) (theta (8 * k + 6)) := by
  dsimp only
  rw [barredOuter, Circuit.eval_a4Outer]
  simp only [barOld, barT, Circuit.eval_liftLeft, Circuit.eval_rightInput,
    eval_x, eval_h₂, eval_h₄, eval_a,
    FastPoly.BarQGeneral.outer, FastPoly.BarQGeneral.C1,
    FastPoly.BarQGeneral.C2, FastPoly.BarQGeneral.U0,
    FastPoly.BarQGeneral.V0, FastPoly.BarQGeneral.Q3]

theorem eval_barredCircuit (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) :
    (barredCircuit (R := R) k).eval (env H₂ H₄ theta) 0 =
      FastPoly.BarQGeneral.gadget H₂ H₄ k theta := by
  rw [barredCircuit, Circuit.eval_bind, Circuit.eval_bind]
  rw [eval_barredOuter]
  have hpair := eval_barredTCircuit (R := R) H₂ H₄ theta k
  have h₁ := congrArg Prod.fst hpair
  have h₂' := congrArg Prod.snd hpair
  dsimp only at h₁ h₂'
  simp only [FastPoly.BarQGeneral.gadget, FastPoly.BarQGeneral.barQ]
  rw [h₁, h₂']

omit [CommRing R] in
@[simp] theorem barredPowerPair_multiplications :
    (barredPowerPair (R := R)).gates.multiplications = 1 := by
  simp only [barredPowerPair, Circuit.gates_bind,
    Circuit.gates, GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    Circuit.gates_liftLeft, Circuit.gates_rightInput,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]

omit [CommRing R] in
@[simp] theorem barredOuter_multiplications (k : ℕ) :
    (barredOuter (R := R) k).gates.multiplications = 6 := by
  simp only [barredOuter, Circuit.a4Outer, barOld, barT,
    Circuit.a4Seed, Circuit.a4Middle, Circuit.a4Columns, Circuit.a4Finish,
    Circuit.gates_bind, Circuit.gates,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    Circuit.gates_liftLeft, Circuit.gates_rightInput,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionParameter]

theorem barredCircuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (barredCircuit (R := R) k).gates.multiplications = 4 * k + 3 := by
  simp only [barredCircuit, barredTCircuit, Circuit.gates_bind,
    Circuit.gates_relabel, GateCount.add_multiplications,
    barredPowerPair_multiplications, barredOuter_multiplications]
  rw [gates_tCircuit_multiplications k 3
    (show ValidTCall k 3 from ⟨by omega, by omega⟩)]
  omega

omit [CommRing R] in
private theorem multDepth_barredPowerPair_le :
    ((barredPowerPair (R := R)).multDepth Height.gadgetDepthEnv 0 ≤ 3) ∧
      ((barredPowerPair (R := R)).multDepth Height.gadgetDepthEnv 1 ≤ 3) := by
  constructor
  · rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
    simp only [barredPowerPair, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_left, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Circuit.constructionX, Circuit.constructionPower,
      Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
      Height.denv_variable, Height.denv_power,
      Height.denv_parameter, Height.gadgetDp_one, Height.gadgetDp_two]
    omega
  · rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    simp only [barredPowerPair, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Fin.addCases_right, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Circuit.constructionX, Circuit.constructionPower,
      Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
      Height.denv_variable, Height.denv_power,
      Height.denv_parameter, Height.gadgetDp_one, Height.gadgetDp_two]
    omega

private theorem multDepth_barredCircuit_le (k : ℕ) (hk : 1 ≤ k) :
    (barredCircuit (R := R) k).multDepth Height.gadgetDepthEnv 0 ≤
      2 * Nat.clog 2 (2 * (4 * k + 3) + 1) + 1 := by
  obtain ⟨hb0, hb1⟩ := multDepth_barredPowerPair_le (R := R)
  set dB : Fin 2 → ℕ :=
    (barredPowerPair (R := R)).multDepth Height.gadgetDepthEnv with hdBdef
  set dp' : ℕ → ℕ := fun i =>
    if i = 1 then 1 else if i = 2 then 2 else if i = 3 then dB 0 else 0
    with hdp'def
  have henv : (Sum.elim Height.gadgetDepthEnv dB) ∘ barredTLabel
      = Height.denv dp' (dB 1) := by
    funext input
    cases input with
    | «variable» => rfl
    | power i =>
        by_cases hi1 : i = 1
        · subst hi1; rfl
        · by_cases hi2 : i = 2
          · subst hi2; rfl
          · by_cases hi3 : i = 3
            · subst hi3; rfl
            · simp only [barredTLabel, hi1, hi2, hi3, if_false,
                Function.comp_apply, Sum.elim_inl, Height.denv_power,
                Height.denv_source, hdp'def]
    | shiftedPower => rfl
    | parameter i => rfl
    | source i => rfl
  have hT : ∀ j : Fin 2, (tCircuit (R := R) k 3).multDepth
      (Height.denv dp' (dB 1)) j ≤ 2 * Nat.clog 2 k + 4 := by
    intro j
    refine (Height.multDepth_tCircuit_le k 3 dp' (dB 1) (by omega) ?_ hb1 j).trans
      ?_
    · intro i hi
      by_cases hi1 : i = 1
      · subst hi1; simp [hdp'def]
      · by_cases hi2 : i = 2
        · subst hi2; simp [hdp'def]
        · by_cases hi3 : i = 3
          · subst hi3; simpa [hdp'def] using hb0
          · simp [hdp'def, hi1, hi2, hi3]
    · have := Height.tDB_le k k 3 (by omega)
      omega
  have hT0 := hT 0
  have hT1 := hT 1
  have hc1 : Nat.clog 2 (2 * k) = Nat.clog 2 k + 1 := Height.clog_two_double k hk
  have hc2 : Nat.clog 2 (2 * (2 * k)) = Nat.clog 2 (2 * k) + 1 :=
    Height.clog_two_double (2 * k) (by omega)
  have hc3 : Nat.clog 2 (2 * (2 * (2 * k))) = Nat.clog 2 (2 * (2 * k)) + 1 :=
    Height.clog_two_double (2 * (2 * k)) (by omega)
  have hc4 : Nat.clog 2 (2 * (2 * (2 * k))) ≤ Nat.clog 2 (2 * (4 * k + 3) + 1) :=
    Nat.clog_mono_right 2 (by omega)
  simp only [barredCircuit, Circuit.multDepth_bind, barredTCircuit,
    Circuit.multDepth_relabel, ← hdBdef, henv, barredOuter, Circuit.a4Outer,
    Circuit.a4Seed, Circuit.a4Middle, Circuit.a4Columns, Circuit.a4Finish,
    barOld, barT, Circuit.multDepth_fork, Circuit.multDepth_add,
    Circuit.multDepth_mul, Circuit.multDepth_liftLeft,
    Circuit.multDepth_rightInput,
    Circuit.constructionX, Circuit.constructionPower,
    Circuit.constructionParameter, Circuit.input, Circuit.multDepth_wire,
    Height.denv_variable, Height.denv_power,
    Height.denv_parameter, Height.gadgetDp_one, Height.gadgetDp_two]
  simp only [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left, Fin.addCases_right] at hT0 hT1 ⊢
  omega

def barredRealized (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta
      (FastPoly.BarQGeneral.gadget H₂ H₄ k theta) (4 * k + 3) where
  circuit := barredCircuit k
  eval_eq := eval_barredCircuit H₂ H₄ theta k
  multiplication_count := barredCircuit_multiplications k hk
  depth_le := multDepth_barredCircuit_le k hk

/-
For `k = 1` this circuit evaluates the uniform `BarQGeneral.gadget`, whereas the
algebraic dispatcher uses the optimized presentation `BarQ15.barQ15`.  Their equality
under the monic degree-two/four hypotheses is proved in `OddGadgetBarQ15.lean` and used
by `RealizedOddGadget.barredOne`; the exceptional presentation therefore has an
explicit semantic bridge rather than being identified only through its gate count.
-/

/-- The three uniform branch counts are exactly half the odd degree, rounded down. -/
theorem q4_half_degree (k : ℕ) (hk : 1 ≤ k) :
    (q4Circuit (R := R) k).gates.multiplications = (4 * k + 1) / 2 := by
  rw [q4Circuit_multiplications k hk]
  omega

theorem known_half_degree (k : ℕ) (hk : 1 ≤ k) :
    (knownCircuit (R := R) k).gates.multiplications = (8 * k + 3) / 2 := by
  rw [knownCircuit_multiplications k hk]
  omega

theorem barred_half_degree (k : ℕ) (hk : 1 ≤ k) :
    (barredCircuit (R := R) k).gates.multiplications = (8 * k + 7) / 2 := by
  rw [barredCircuit_multiplications k hk]
  omega

end OddGadget

end FastPoly.Cost
