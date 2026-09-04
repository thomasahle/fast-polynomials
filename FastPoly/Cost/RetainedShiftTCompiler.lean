import FastPoly.Cost.RetainedShiftTCircuit

/-!
# A retained-shift compiler for the shared `T` bases

The ordinary `T` compiler reconstructs the scalar difference between a power and its
shifted companion in each shared base.  At an actual call site that scalar is already
available.  This module threads it through input `.source 0`, changes only the shared
even and odd branches, and leaves every other branch literally equal to `tCircuitF`.

The fuelled definition is intentional: its branch equations line up with those of
`tCircuitF`, so semantic and cost proofs remain small and do not unfold a large
recursive circuit term.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

namespace RetainedShiftT

private abbrev rhoInput {R : Type u} : Circuit R ConstructionInput 1 :=
  Circuit.constructionSource 0

/-- Fuelled compiler which optimizes precisely the shared bases.  In the even shared
base the same retained scalar is passed to the recursive level-two call; this is the
stateful step missing from a merely local peephole. -/
def compilerF {R : Type u} [CommRing R] :
    ℕ → ℕ → ℕ → Circuit R ConstructionInput 2
  | 0, k, l => tCircuitF 0 k l
  | fuel + 1, k, l =>
      if k ≤ 1 then
        tCircuitF (fuel + 1) k l
      else if k % 2 = 0 then
        if l ≤ 1 then
          evenBaseCircuit k rhoInput (compilerF fuel (k / 2) 2)
        else
          tCircuitF (fuel + 1) k l
      else if l ≤ 2 then
        oddBaseCircuit k rhoInput (tCircuitF fuel ((k - 1) / 2) 3)
      else
        tCircuitF (fuel + 1) k l

/-- Retained-shift compiler for a complete `T_{k,2^l}` call. -/
def compiler {R : Type u} [CommRing R] (k l : ℕ) :
    Circuit R ConstructionInput 2 :=
  compilerF k k l

/-- Number of additions removed from the ordinary compiler. -/
def savingsF : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | fuel + 1, k, l =>
      if k ≤ 1 then 0
      else if k % 2 = 0 then
        if l ≤ 1 then savingsF fuel (k / 2) 2 + 1 else 0
      else if l ≤ 2 then 2
      else 0

def savings (k l : ℕ) : ℕ := savingsF k k l

/-! ## Stable branch equations -/

@[simp] theorem compilerF_zero {R : Type u} [CommRing R] (k l : ℕ) :
    compilerF (R := R) 0 k l = tCircuitF 0 k l := rfl

theorem compilerF_succ_le_one {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : k ≤ 1) :
    compilerF (R := R) (fuel + 1) k l = tCircuitF (fuel + 1) k l := by
  rw [compilerF, if_pos hk]

theorem compilerF_succ_even_base {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (heven : k % 2 = 0) (hl : l ≤ 1) :
    compilerF (R := R) (fuel + 1) k l =
      evenBaseCircuit k rhoInput (compilerF fuel (k / 2) 2) := by
  rw [compilerF, if_neg hk, if_pos heven, if_pos hl]

theorem compilerF_succ_even_main {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (heven : k % 2 = 0) (hl : ¬ l ≤ 1) :
    compilerF (R := R) (fuel + 1) k l = tCircuitF (fuel + 1) k l := by
  rw [compilerF, if_neg hk, if_pos heven, if_neg hl]

theorem compilerF_succ_odd_base {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (hodd : k % 2 ≠ 0) (hl : l ≤ 2) :
    compilerF (R := R) (fuel + 1) k l =
      oddBaseCircuit k rhoInput (tCircuitF fuel ((k - 1) / 2) 3) := by
  rw [compilerF, if_neg hk, if_neg hodd, if_pos hl]

theorem compilerF_succ_odd_main {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (hodd : k % 2 ≠ 0) (hl : ¬ l ≤ 2) :
    compilerF (R := R) (fuel + 1) k l = tCircuitF (fuel + 1) k l := by
  rw [compilerF, if_neg hk, if_neg hodd, if_neg hl]

@[simp] theorem savingsF_zero (k l : ℕ) : savingsF 0 k l = 0 := rfl

theorem savingsF_succ_le_one (fuel k l : ℕ) (hk : k ≤ 1) :
    savingsF (fuel + 1) k l = 0 := by
  rw [savingsF, if_pos hk]

theorem savingsF_succ_even_base (fuel k l : ℕ) (hk : ¬ k ≤ 1)
    (heven : k % 2 = 0) (hl : l ≤ 1) :
    savingsF (fuel + 1) k l = savingsF fuel (k / 2) 2 + 1 := by
  rw [savingsF, if_neg hk, if_pos heven, if_pos hl]

theorem savingsF_succ_even_main (fuel k l : ℕ) (hk : ¬ k ≤ 1)
    (heven : k % 2 = 0) (hl : ¬ l ≤ 1) :
    savingsF (fuel + 1) k l = 0 := by
  rw [savingsF, if_neg hk, if_pos heven, if_neg hl]

theorem savingsF_succ_odd_base (fuel k l : ℕ) (hk : ¬ k ≤ 1)
    (hodd : k % 2 ≠ 0) (hl : l ≤ 2) :
    savingsF (fuel + 1) k l = 2 := by
  rw [savingsF, if_neg hk, if_neg hodd, if_pos hl]

theorem savingsF_succ_odd_main (fuel k l : ℕ) (hk : ¬ k ≤ 1)
    (hodd : k % 2 ≠ 0) (hl : ¬ l ≤ 2) :
    savingsF (fuel + 1) k l = 0 := by
  rw [savingsF, if_neg hk, if_neg hodd, if_neg hl]

/-! ## Local exact-count comparisons -/

private theorem oldEvenBase_additions {R : Type u} [CommRing R] (k : ℕ)
    (inner : Circuit R ConstructionInput 2) :
    (tEvenBaseCircuit k inner).gates.additions = inner.gates.additions + 6 := by
  simp only [tEvenBaseCircuit, Circuit.gates_bind, gates_recurseWithPowerPair,
    tEvenBasePowerPair, Circuit.gates, GateCount.add_additions,
    GateCount.zero_additions, GateCount.adds_additions,
    Circuit.gates_diffSquareAdd_additions,
    Circuit.gates_rightInput, Circuit.gates_liftLeft,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionShiftedPower,
    Circuit.gates_constructionParameter]
  omega

private theorem oldOddBase_additions {R : Type u} [CommRing R] (k : ℕ)
    (inner : Circuit R ConstructionInput 2) :
    (tOddBaseCircuit k inner).gates.additions = inner.gates.additions + 17 := by
  rw [tOddBaseCircuit]
  simp only [finishOdd, Circuit.gates_bind, gates_recurseWithPowerPair,
    Circuit.gates, priorBound, Circuit.gates_input, Circuit.gates_rightInput,
    GateCount.add_additions, GateCount.zero_additions, GateCount.adds_additions,
    GateCount.muls_additions, tOddBaseAux, Circuit.gates_liftLeft,
    Circuit.gates_diffSquareAdd_additions,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionShiftedPower,
    Circuit.gates_constructionParameter,
    Circuit.gates_reindexConstructionParameters]
  have hq₃ : (peelCircuit (R := R) 2).gates.additions = 3 := by rfl
  rw [hq₃]
  omega

/-! ## Exact gate accounting -/

theorem compilerF_multiplications : ∀ {R : Type u} [CommRing R] fuel k l,
    (compilerF (R := R) fuel k l).gates.multiplications =
      (tCircuitF (R := R) fuel k l).gates.multiplications := by
  intro R _ fuel
  induction fuel with
  | zero =>
      intro k l
      rfl
  | succ fuel ih =>
      intro k l
      by_cases hk : k ≤ 1
      · rw [compilerF_succ_le_one fuel k l hk]
      · by_cases heven : k % 2 = 0
        · by_cases hl : l ≤ 1
          · rw [compilerF_succ_even_base fuel k l hk heven hl,
              tCircuitF_succ_even_base fuel k l hk heven hl,
              evenBaseCircuit_multiplications,
              gates_tEvenBaseCircuit_multiplications, ih]
            simp only [rhoInput, Circuit.gates_constructionSource,
              GateCount.zero_multiplications]
            omega
          · rw [compilerF_succ_even_main fuel k l hk heven hl]
        · by_cases hl : l ≤ 2
          · have hm₃ : (peelCircuit (R := R) 2).gates.multiplications = 1 := by rfl
            rw [compilerF_succ_odd_base fuel k l hk heven hl,
              tCircuitF_succ_odd_base fuel k l hk heven hl,
              oddBaseCircuit_multiplications,
              gates_tOddBaseCircuit_multiplications, hm₃]
            simp only [rhoInput, Circuit.gates_constructionSource,
              GateCount.zero_multiplications]
            omega
          · rw [compilerF_succ_odd_main fuel k l hk heven hl]

theorem compilerF_additions : ∀ {R : Type u} [CommRing R] fuel k l,
    (compilerF (R := R) fuel k l).gates.additions + savingsF fuel k l =
      (tCircuitF (R := R) fuel k l).gates.additions := by
  intro R _ fuel
  induction fuel with
  | zero =>
      intro k l
      rfl
  | succ fuel ih =>
      intro k l
      by_cases hk : k ≤ 1
      · rw [compilerF_succ_le_one fuel k l hk,
          savingsF_succ_le_one fuel k l hk]
        omega
      · by_cases heven : k % 2 = 0
        · by_cases hl : l ≤ 1
          · rw [compilerF_succ_even_base fuel k l hk heven hl,
              tCircuitF_succ_even_base fuel k l hk heven hl,
              savingsF_succ_even_base fuel k l hk heven hl,
              evenBaseCircuit_additions, oldEvenBase_additions]
            simp only [rhoInput, Circuit.gates_constructionSource,
              GateCount.zero_additions]
            have hinner := ih (k / 2) 2
            omega
          · rw [compilerF_succ_even_main fuel k l hk heven hl,
              savingsF_succ_even_main fuel k l hk heven hl]
            omega
        · by_cases hl : l ≤ 2
          · rw [compilerF_succ_odd_base fuel k l hk heven hl,
              tCircuitF_succ_odd_base fuel k l hk heven hl,
              savingsF_succ_odd_base fuel k l hk heven hl,
              oddBaseCircuit_additions, oldOddBase_additions]
            simp only [rhoInput, Circuit.gates_constructionSource,
              GateCount.zero_additions]
            omega
          · rw [compilerF_succ_odd_main fuel k l hk heven hl,
              savingsF_succ_odd_main fuel k l hk heven hl]
            omega

theorem compiler_multiplications {R : Type u} [CommRing R] (k l : ℕ) :
    (compiler (R := R) k l).gates.multiplications =
      (tCircuit (R := R) k l).gates.multiplications := by
  exact compilerF_multiplications k k l

theorem compiler_additions {R : Type u} [CommRing R] (k l : ℕ) :
    (compiler (R := R) k l).gates.additions + savings k l =
      (tCircuit (R := R) k l).gates.additions := by
  exact compilerF_additions k k l

/-- A direct odd level-two call saves the two redundant shared-base additions. -/
theorem savings_odd_two (m : ℕ) (hm : 1 ≤ m) :
    savings (2 * m + 1) 2 = 2 := by
  rw [savings]
  conv_lhs => rw [show 2 * m + 1 = (2 * m) + 1 by omega]
  rw [savingsF, if_neg (by omega : ¬ 2 * m + 1 ≤ 1),
    if_neg (by omega : (2 * m + 1) % 2 ≠ 0), if_pos (by omega : 2 ≤ 2)]

/-- A direct even level-two call never reaches either shared-base branch. -/
theorem savings_even_two (m : ℕ) (hm : 1 ≤ m) :
    savings (2 * m) 2 = 0 := by
  rw [savings]
  have hk : 2 * m = (2 * m - 1) + 1 := by omega
  conv_lhs => rw [hk]
  rw [savingsF, ← hk]
  rw [if_neg (by omega : ¬ 2 * m ≤ 1),
    if_pos (Nat.mul_mod_right 2 m), if_neg (by omega : ¬ 2 ≤ 1)]

/-- A valid level-one call saves one addition in its even base and threads the same
side wire to any odd shared base reached immediately afterward. -/
theorem savings_even_one (m : ℕ) (hm : 1 ≤ m) :
    savings (2 * m) 1 = savingsF (2 * m - 1) m 2 + 1 := by
  rw [savings]
  have hk : 2 * m = (2 * m - 1) + 1 := by omega
  conv_lhs => rw [hk]
  rw [savingsF, ← hk]
  rw [if_neg (by omega : ¬ 2 * m ≤ 1),
    if_pos (Nat.mul_mod_right 2 m), if_pos (by omega : 1 ≤ 1)]
  congr 2
  omega

/-! ## Semantic preservation -/

section Semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- Congruence of the ordinary shared-even shell in its recursive continuation. -/
private theorem eval_tEvenBaseCircuit_congr (k : ℕ)
    (left right : Circuit R ConstructionInput 2)
    (env : ConstructionInput → A[X])
    (hinner :
      left.eval
          (Sum.elim env ((tEvenBasePowerPair (R := R) k).eval env) ∘
            ConstructionInput.withPowerPair 2 id 0 1) =
        right.eval
          (Sum.elim env ((tEvenBasePowerPair (R := R) k).eval env) ∘
            ConstructionInput.withPowerPair 2 id 0 1)) :
    (tEvenBaseCircuit k left).eval env =
      (tEvenBaseCircuit k right).eval env := by
  rw [tEvenBaseCircuit, tEvenBaseCircuit, Circuit.eval_bind, Circuit.eval_bind,
    recurseWithPowerPair, recurseWithPowerPair, Circuit.eval_relabel,
    Circuit.eval_relabel]
  exact hinner

/-- The retained compiler computes exactly the same pair as `tCircuitF`, provided
`.source 0` is the scalar difference between the supplied shifted power and the power
at the current level. -/
theorem eval_compilerF_eq : ∀ fuel k l (env : ConstructionInput → A[X]),
    ValidTCall k l →
    env .shiftedPower = env (.power l) + env (.source 0) →
    (compilerF (R := R) fuel k l).eval env =
      (tCircuitF (R := R) fuel k l).eval env := by
  intro fuel
  induction fuel with
  | zero =>
      intro k l env hvalid hshift
      rfl
  | succ fuel ih =>
      intro k l env hvalid hshift
      by_cases hk : k ≤ 1
      · rw [compilerF_succ_le_one fuel k l hk]
      · by_cases heven : k % 2 = 0
        · by_cases hl : l ≤ 1
          · have hl1 : l = 1 := by
              exact Nat.le_antisymm hl hvalid.1
            subst l
            rw [compilerF_succ_even_base fuel k 1 hk heven (by omega),
              tCircuitF_succ_even_base fuel k 1 hk heven (by omega)]
            have hshift' : env .shiftedPower =
                env (.power 1) + (rhoInput (R := R)).eval env 0 := by
              simpa only [rhoInput, Circuit.eval_constructionSource] using hshift
            calc
              (evenBaseCircuit k (rhoInput (R := R))
                  (compilerF fuel (k / 2) 2)).eval env =
                  (tEvenBaseCircuit k (compilerF fuel (k / 2) 2)).eval env :=
                eval_evenBaseCircuit_eq k (rhoInput (R := R)) _ env hshift'
              _ = (tEvenBaseCircuit k (tCircuitF fuel (k / 2) 2)).eval env := by
                apply eval_tEvenBaseCircuit_congr
                let innerEnv : ConstructionInput → A[X] :=
                  Sum.elim env ((tEvenBasePowerPair (R := R) k).eval env) ∘
                    ConstructionInput.withPowerPair 2 id 0 1
                have hinnerValid : ValidTCall (k / 2) 2 := by
                  refine ⟨Nat.succ_le_succ (Nat.zero_le 1), ?_⟩
                  intro _ htwo
                  omega
                have hpair := eval_evenBasePowerPair_eq
                  (R := R) (A := A) k (rhoInput (R := R)) env hshift'
                have hretained :
                    (evenBasePowerPair k (rhoInput (R := R))).eval env 1 =
                      (evenBasePowerPair k (rhoInput (R := R))).eval env 0 +
                        env (.source 0) := by
                  rw [evenBasePowerPair, Circuit.eval_bind]
                  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
                    show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
                  simp only [Circuit.eval_fork, Fin.addCases_right,
                    Fin.addCases_left, Circuit.eval_add,
                    Circuit.eval_rightInput, Circuit.eval_liftLeft,
                    rhoInput, Circuit.constructionSource, Circuit.input,
                    Circuit.eval_wire]
                  rw [show (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 from rfl]
                have hold :
                    (tEvenBasePowerPair (R := R) k).eval env 1 =
                      (tEvenBasePowerPair (R := R) k).eval env 0 + env (.source 0) := by
                  calc
                    (tEvenBasePowerPair (R := R) k).eval env 1 =
                        (evenBasePowerPair k (rhoInput (R := R))).eval env 1 :=
                      (congrFun hpair 1).symm
                    _ = (evenBasePowerPair k (rhoInput (R := R))).eval env 0 +
                        env (.source 0) := hretained
                    _ = (tEvenBasePowerPair (R := R) k).eval env 0 +
                        env (.source 0) := by rw [congrFun hpair 0]
                have hinnerShift :
                    innerEnv .shiftedPower =
                      innerEnv (.power 2) + innerEnv (.source 0) := by
                  change
                    (tEvenBasePowerPair (R := R) k).eval env 1 =
                      (tEvenBasePowerPair (R := R) k).eval env 0 +
                        env (.source 0)
                  exact hold
                exact ih (k / 2) 2 innerEnv hinnerValid hinnerShift
          · rw [compilerF_succ_even_main fuel k l hk heven hl]
        · by_cases hl : l ≤ 2
          · have hl2 : l = 2 := by
              have hl_ne_one : l ≠ 1 := by
                intro hl1
                have := hvalid.2 (by omega) hl1
                exact heven this
              have hl_ge_two : 2 ≤ l := by
                cases l with
                | zero => exact (Nat.not_succ_le_zero 0 hvalid.1).elim
                | succ l =>
                    cases l with
                    | zero => exact (hl_ne_one rfl).elim
                    | succ l =>
                        exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le l))
              exact Nat.le_antisymm hl hl_ge_two
            subst l
            rw [compilerF_succ_odd_base fuel k 2 hk heven (by omega),
              tCircuitF_succ_odd_base fuel k 2 hk heven (by omega)]
            apply eval_oddBaseCircuit_eq k (rhoInput (R := R)) _ env (by omega)
            simpa only [rhoInput, Circuit.eval_constructionSource] using hshift
          · rw [compilerF_succ_odd_main fuel k l hk heven hl]

/-- Complete retained-shift calls preserve the ordinary `T` compiler's semantics. -/
theorem eval_compiler_eq (k l : ℕ) (env : ConstructionInput → A[X])
    (hvalid : ValidTCall k l)
    (hshift : env .shiftedPower = env (.power l) + env (.source 0)) :
    (compiler (R := R) k l).eval env = (tCircuit (R := R) k l).eval env := by
  exact eval_compilerF_eq k k l env hvalid hshift

end Semantics

end RetainedShiftT

end FastPoly.Cost
