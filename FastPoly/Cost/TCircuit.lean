import FastPoly.Cost.MersenneCircuit
import FastPoly.Section5.T
import FastPoly.Cost.PeeledCircuit

/-!
# Semantic compiler for the `T` recursion

The compiler in this file mirrors the four branches of `FastPoly.TF`.  Its only
arithmetic-specific operation is the explicit difference-of-squares shell
`(center + shift) * (center - shift) + tail`; no invertibility or characteristic
hypothesis occurs here.

Every value used by two downstream gates is introduced by `Circuit.bind`.  In
particular, the odd branches bind their auxiliary shift once before using it both in
the next power and in the final output factor.  Consequently the gate count of the
syntax is the gate count of the displayed straight-line program, rather than that of
an expanded expression tree.
-/

namespace FastPoly.Cost

open Polynomial

universe u v w

section primitives

variable {R : Type u} [CommRing R]

private abbrev tx : Circuit R ConstructionInput 1 := Circuit.constructionX
private abbrev th (i : ℕ) : Circuit R ConstructionInput 1 := Circuit.constructionPower i
private abbrev tht : Circuit R ConstructionInput 1 := Circuit.constructionShiftedPower
private abbrev ta (i : ℕ) : Circuit R ConstructionInput 1 := Circuit.constructionParameter i

private abbrev tmers (k : ℕ) (parameterMap : ℕ → ℕ) :
    Circuit R ConstructionInput 1 :=
  (peelCircuit k).reindexConstructionParameters parameterMap

/-- A bound difference-of-squares shell.  Binding the two operands is important when
either operand is itself a nontrivial circuit. -/
def Circuit.diffSquareAdd {ι : Type v} (center shift tail : Circuit R ι 1) :
    Circuit R ι 1 :=
  .bind (.fork center shift) <|
    .add
      (.mul
        (.add (Circuit.rightInput (ι := ι) (0 : Fin 2))
          (Circuit.rightInput (ι := ι) (1 : Fin 2)))
        (.sub (Circuit.rightInput (ι := ι) (0 : Fin 2))
          (Circuit.rightInput (ι := ι) (1 : Fin 2))))
      tail.liftLeft

@[simp] theorem Circuit.eval_diffSquareAdd {A : Type w} [CommRing A] [Algebra R A]
    {ι : Type v} (center shift tail : Circuit R ι 1) (env : ι → A) :
    (diffSquareAdd center shift tail).eval env 0 =
      (center.eval env 0 + shift.eval env 0) *
          (center.eval env 0 - shift.eval env 0) + tail.eval env 0 := by
  simp [diffSquareAdd, Circuit.eval_bind, Circuit.eval_add, Circuit.eval_mul,
    Circuit.eval_sub, Circuit.eval_fork, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left, Fin.addCases_right]

/-- Relabel the inputs of a recursive `T` call after a new power pair has been bound.
All old powers remain available; one tower level and the shifted power are replaced by
the two indicated bound outputs. -/
def ConstructionInput.withPowerPair {m : ℕ} (level : ℕ)
    (parameterMap : ℕ → ℕ) (powerSlot shiftedSlot : Fin m) :
    ConstructionInput → Sum ConstructionInput (Fin m)
  | .variable => .inl .variable
  | .power i => if i = level then .inr powerSlot else .inl (.power i)
  | .shiftedPower => .inr shiftedSlot
  | .parameter i => .inl (.parameter (parameterMap i))
  | .source i => .inl (.source i)

theorem constructionEnv_withPowerPair {A : Type w} [CommRing A]
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) {m : ℕ} (values : Fin m → A[X]) (level : ℕ)
    (parameterMap : ℕ → ℕ) (powerSlot shiftedSlot : Fin m) :
    Sum.elim (constructionEnv powers shifted parameters source) values ∘
        ConstructionInput.withPowerPair level parameterMap powerSlot shiftedSlot =
      constructionEnv (Function.update powers level (values powerSlot))
        (values shiftedSlot) (parameters ∘ parameterMap) source := by
  funext input
  cases input
  · rfl
  · rename_i i
    by_cases hi : i = level
    · subst hi
      simp only [ConstructionInput.withPowerPair, Function.comp_apply,
        Function.update_self, constructionEnv_power]
      rfl
    · simp only [ConstructionInput.withPowerPair, hi, if_false, Function.comp_apply,
        Function.update_of_ne hi, constructionEnv_power]
      rfl
  · rfl
  · rfl
  · rfl

/-- Feed a recursive `T` circuit with a newly bound power pair. -/
def recurseWithPowerPair {m : ℕ} (level : ℕ) (parameterMap : ℕ → ℕ)
    (powerSlot shiftedSlot : Fin m) (inner : Circuit R ConstructionInput 2) :
    Circuit R (Sum ConstructionInput (Fin m)) 2 :=
  inner.relabel
    (ConstructionInput.withPowerPair level parameterMap powerSlot shiftedSlot)

/-! ## Branch-local circuits -/

/-- Power pair produced by the shared even base. -/
def tEvenBasePowerPair (k : ℕ) : Circuit R ConstructionInput 2 :=
  let linear := .add tx (ta (2 * k - 3))
  let H₄ := Circuit.diffSquareAdd (th 1) linear (ta (2 * k - 4))
  .bind H₄ <|
    let h := Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 1)
    .fork h (.add h (.sub tht.liftLeft (th 1).liftLeft))

/-- Shared even base: compute `H₄` once, bind `(H₄,H̃₄)`, and recurse. -/
def tEvenBaseCircuit (k : ℕ) (inner : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  .bind (tEvenBasePowerPair k) <| recurseWithPowerPair 2 id 0 1 inner

/-- Power pair produced by an ordinary even step. -/
def tEvenMainPowerPair (k l : ℕ) : Circuit R ConstructionInput 2 :=
  let b := (k - 2) * 2 ^ l
  let s₁ := .add (th (l - 1)) (tmers (l - 1) (fun j => b + 2 ^ (l - 1) + 1 + j))
  let s₁t := .add (th (l - 1)) (ta (b + 2 ^ (l - 1)))
  let s₂ := tmers (l - 1) (fun j => b + 1 + j)
  .fork
    (Circuit.diffSquareAdd (th l) s₁ s₂)
    (Circuit.diffSquareAdd tht s₁t (ta b))

/-- Even main step: the two Mersenne tails and the two product gates are the complete
new cost; the resulting power pair is then passed to the recursive call. -/
def tEvenMainCircuit (k l : ℕ) (inner : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  .bind (tEvenMainPowerPair k l) <|
    recurseWithPowerPair (l + 1) id 0 1 inner

/-- An output from the first binding that remains in scope after a second binding. -/
def priorBound {m n : ℕ} (i : Fin m) :
    Circuit R (Sum (Sum ConstructionInput (Fin m)) (Fin n)) 1 :=
  Circuit.input (.inl (.inr i))

/-- Finish an odd branch from six bound auxiliaries:
`(new power,new shifted power,left factor,right factor,left tail,right tail)`. -/
def finishOdd (level : ℕ) (parameterMap : ℕ → ℕ)
    (aux : Circuit R ConstructionInput 6) (inner : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  .bind aux <|
    .bind (recurseWithPowerPair level parameterMap 0 1 inner) <|
      .fork
        (.add (.mul (priorBound (R := R) (n := 2) (2 : Fin 6))
            (Circuit.rightInput (ι := Sum ConstructionInput (Fin 6)) (0 : Fin 2)))
          (priorBound (R := R) (n := 2) (4 : Fin 6)))
        (.add (.mul (priorBound (R := R) (n := 2) (3 : Fin 6))
            (Circuit.rightInput (ι := Sum ConstructionInput (Fin 6)) (1 : Fin 2)))
          (priorBound (R := R) (n := 2) (5 : Fin 6)))

/-- Six auxiliaries retained across the recursive call in the shared odd base. -/
def tOddBaseAux (k : ℕ) : Circuit R ConstructionInput 6 :=
  let b := 4 * (k - 2)
  let s₁ : Circuit R ConstructionInput 1 :=
    .add (th 1) (.add tx (ta (b + 3)))
  .bind s₁ <|
    let s := Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 1)
    let H₈ := Circuit.diffSquareAdd
      (.add (th 2).liftLeft s)
      (.add tx.liftLeft (ta (b + 2)).liftLeft)
      (ta (b + 1)).liftLeft
    .bind H₈ <|
      let h := Circuit.rightInput (R := R)
        (ι := Sum ConstructionInput (Fin 1)) (0 : Fin 1)
      let s' : Circuit R (Sum (Sum ConstructionInput (Fin 1)) (Fin 1)) 1 :=
        Circuit.input (.inl (.inr (0 : Fin 1)))
      let old (c : Circuit R ConstructionInput 1) := c.liftLeft.liftLeft
      .fork
        (.fork h (.add h (old (ta b))))
        (.fork
          (.fork
            (.sub (old (th 2)) (.scale ((k - 1 : ℕ) : R) s'))
            (.sub (old tht)
              (.scale ((k - 1 : ℕ) : R)
                (.sub s' (.sub (old tht) (old (th 2)))))))
          (.fork
            (tmers 2 (fun j => 1 + j)).liftLeft.liftLeft
            (old (ta 0))))

/-- Shared odd base.  The common octic and the common linear shift are each bound once;
the `Q₃` tail is compiled by the same Mersenne compiler as every other `Q` block. -/
def tOddBaseCircuit (k : ℕ) (inner : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  finishOdd 3 (fun j => 4 + j) (tOddBaseAux k) inner

/-- The two degree-`2^(l-1)` shifts shared throughout an ordinary odd step. -/
def tOddMainShiftPair (k l : ℕ) : Circuit R ConstructionInput 2 :=
  let b := (k - 2) * 2 ^ l
  let s₁ : Circuit R ConstructionInput 1 :=
    .add (th (l - 1)) (tmers (l - 1) (fun j => b + 2 ^ (l - 1) + 1 + j))
  let s₁t : Circuit R ConstructionInput 1 :=
    .add (th (l - 1)) (ta (b + 2 ^ (l - 1)))
  .fork s₁ s₁t

/-- Six auxiliaries retained across the recursive call in an ordinary odd step. -/
def tOddMainAux (k l : ℕ) : Circuit R ConstructionInput 6 :=
  let b := (k - 2) * 2 ^ l
  .bind (tOddMainShiftPair k l) <|
    let s := Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 2)
    let st := Circuit.rightInput (R := R) (ι := ConstructionInput) (1 : Fin 2)
    let old (c : Circuit R ConstructionInput 1) := c.liftLeft
    let s₂ := .add (old (th (l - 2)))
      (old (tmers (l - 2) (fun j => b + 2 ^ (l - 2) + 1 + j)))
    let s₂t := .add (old (th (l - 2))) (old (ta (b + 2 ^ (l - 2))))
    let s₃ := old (tmers (l - 2) (fun j => b + 1 + j))
    let qtail := old (tmers l (fun j => 1 + j))
    .fork
      (.fork
        (Circuit.diffSquareAdd (.add (old (th l)) s) s₂ s₃)
        (Circuit.diffSquareAdd (.add (old tht) st) s₂t (old (ta b))))
      (.fork
        (.fork
          (.sub (old (th l)) (.scale ((k - 1 : ℕ) : R) s))
          (.sub (old tht) (.scale ((k - 1 : ℕ) : R) st)))
        (.fork qtail (old (ta 0))))

/-- Ordinary odd step.  The six auxiliaries keep the two recursively updated powers,
the two final monic factors, and the two additive tails alive across the recursive call. -/
def tOddMainCircuit (k l : ℕ) (inner : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  finishOdd (l + 1) (fun j => 2 ^ l + j) (tOddMainAux k l) inner

/-! ## Syntax-cost equations for the four branches

These equations expose only the multiplication structure of each compiled branch.
Their closed-form arithmetic is kept in `TCircuitCount.lean`. -/

omit [CommRing R] in
@[simp] theorem Circuit.gates_diffSquareAdd_multiplications {I : Type v}
    (center shift tail : Circuit R I 1) :
    (Circuit.diffSquareAdd center shift tail).gates.multiplications =
      center.gates.multiplications + shift.gates.multiplications +
        tail.gates.multiplications + 1 := by
  simp only [Circuit.diffSquareAdd, Circuit.gates_bind, Circuit.gates,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    Circuit.gates_rightInput, Circuit.gates_liftLeft]
  omega

omit [CommRing R] in
@[simp] theorem gates_recurseWithPowerPair {m : ℕ} (level : ℕ)
    (parameterMap : ℕ → ℕ) (powerSlot shiftedSlot : Fin m)
    (inner : Circuit R ConstructionInput 2) :
    (recurseWithPowerPair level parameterMap powerSlot shiftedSlot inner).gates =
      inner.gates := by
  rw [recurseWithPowerPair, Circuit.gates_relabel]

omit [CommRing R] in
theorem gates_finishOdd_multiplications (level : ℕ) (parameterMap : ℕ → ℕ)
    (aux : Circuit R ConstructionInput 6) (inner : Circuit R ConstructionInput 2) :
    (finishOdd level parameterMap aux inner).gates.multiplications =
      aux.gates.multiplications + inner.gates.multiplications + 2 := by
  simp only [finishOdd, Circuit.gates_bind, gates_recurseWithPowerPair,
    Circuit.gates, GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, GateCount.muls_multiplications,
    priorBound, Circuit.gates_input, Circuit.gates_rightInput]
  omega

omit [CommRing R] in
theorem gates_tEvenBaseCircuit_multiplications (k : ℕ)
    (inner : Circuit R ConstructionInput 2) :
    (tEvenBaseCircuit k inner).gates.multiplications =
      1 + inner.gates.multiplications := by
  simp only [tEvenBaseCircuit, Circuit.gates_bind, gates_recurseWithPowerPair,
    tEvenBasePowerPair, Circuit.gates, GateCount.add_multiplications,
    GateCount.zero_multiplications, GateCount.adds_multiplications,
    Circuit.gates_diffSquareAdd_multiplications,
    Circuit.gates_rightInput, tx, th, tht, ta,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionShiftedPower, Circuit.gates_constructionParameter,
    Circuit.gates_liftLeft]

omit [CommRing R] in
theorem gates_tEvenMainCircuit_multiplications (k l : ℕ)
    (inner : Circuit R ConstructionInput 2) :
    (tEvenMainCircuit k l inner).gates.multiplications =
      (peelCircuit (R := R) (l - 1)).gates.multiplications +
        (peelCircuit (R := R) (l - 1)).gates.multiplications + 2 +
          inner.gates.multiplications := by
  simp only [tEvenMainCircuit, Circuit.gates_bind, gates_recurseWithPowerPair,
    tEvenMainPowerPair, Circuit.gates, GateCount.add_multiplications,
    GateCount.zero_multiplications, GateCount.adds_multiplications,
    Circuit.gates_diffSquareAdd_multiplications,
    th, tht, ta, tmers,
    Circuit.gates_constructionPower, Circuit.gates_constructionShiftedPower,
    Circuit.gates_constructionParameter,
    Circuit.gates_reindexConstructionParameters]
  omega

theorem gates_tOddBaseCircuit_multiplications (k : ℕ)
    (inner : Circuit R ConstructionInput 2) :
    (tOddBaseCircuit k inner).gates.multiplications =
      (peelCircuit (R := R) 2).gates.multiplications + 3 +
        inner.gates.multiplications := by
  rw [tOddBaseCircuit, gates_finishOdd_multiplications]
  simp only [tOddBaseAux, Circuit.gates_bind, Circuit.gates,
    GateCount.add_multiplications, GateCount.zero_multiplications,
    GateCount.adds_multiplications, Circuit.gates_liftLeft,
    Circuit.gates_input, Circuit.gates_rightInput,
    Circuit.gates_diffSquareAdd_multiplications, tx, th, tht, ta, tmers,
    Circuit.gates_constructionX, Circuit.gates_constructionPower,
    Circuit.gates_constructionShiftedPower, Circuit.gates_constructionParameter,
    Circuit.gates_reindexConstructionParameters]
  omega

theorem gates_tOddMainCircuit_multiplications (k l : ℕ)
    (inner : Circuit R ConstructionInput 2) :
    (tOddMainCircuit k l inner).gates.multiplications =
      (peelCircuit (R := R) (l - 1)).gates.multiplications +
        (peelCircuit (R := R) (l - 2)).gates.multiplications +
        (peelCircuit (R := R) (l - 2)).gates.multiplications +
        (peelCircuit (R := R) l).gates.multiplications + 4 +
        inner.gates.multiplications := by
  rw [tOddMainCircuit, gates_finishOdd_multiplications]
  simp only [tOddMainAux, tOddMainShiftPair, Circuit.gates_bind,
    Circuit.gates, GateCount.add_multiplications,
    GateCount.zero_multiplications, GateCount.adds_multiplications,
    Circuit.gates_liftLeft, Circuit.gates_rightInput,
    Circuit.gates_diffSquareAdd_multiplications,
    th, tht, ta, tmers,
    Circuit.gates_constructionPower, Circuit.gates_constructionShiftedPower,
    Circuit.gates_constructionParameter,
    Circuit.gates_reindexConstructionParameters]
  omega

end primitives

/-! ## The compiler -/

/-- Fuel-indexed circuit matching `FastPoly.TF` branch for branch. -/
def tCircuitF {R : Type u} [CommRing R] : ℕ → ℕ → ℕ → Circuit R ConstructionInput 2
  | 0, _, l => .fork (Circuit.constructionPower l) Circuit.constructionShiftedPower
  | fuel + 1, k, l =>
      if k ≤ 1 then
        .fork (Circuit.constructionPower l) Circuit.constructionShiftedPower
      else if k % 2 = 0 then
        if l ≤ 1 then
          tEvenBaseCircuit k (tCircuitF fuel (k / 2) 2)
        else
          tEvenMainCircuit k l (tCircuitF fuel (k / 2) (l + 1))
      else if l ≤ 2 then
        tOddBaseCircuit k (tCircuitF fuel ((k - 1) / 2) 3)
      else
        tOddMainCircuit k l (tCircuitF fuel ((k - 1) / 2) (l + 1))

/-- Semantic circuit for `Tpair`. -/
def tCircuit {R : Type u} [CommRing R] (k l : ℕ) : Circuit R ConstructionInput 2 :=
  tCircuitF k k l

/-- Named branch equations keep proofs from unfolding the recursive body repeatedly. -/
theorem tCircuitF_succ_le_one {R : Type u} [CommRing R] (fuel k l : ℕ) (h : k ≤ 1) :
    tCircuitF (R := R) (fuel + 1) k l =
      .fork (Circuit.constructionPower l) Circuit.constructionShiftedPower := by
  rw [tCircuitF, if_pos h]

theorem tCircuitF_succ_even_base {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (heven : k % 2 = 0) (hl : l ≤ 1) :
    tCircuitF (R := R) (fuel + 1) k l =
      tEvenBaseCircuit k (tCircuitF fuel (k / 2) 2) := by
  rw [tCircuitF, if_neg hk, if_pos heven, if_pos hl]

theorem tCircuitF_succ_even_main {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (heven : k % 2 = 0) (hl : ¬ l ≤ 1) :
    tCircuitF (R := R) (fuel + 1) k l =
      tEvenMainCircuit k l (tCircuitF fuel (k / 2) (l + 1)) := by
  rw [tCircuitF, if_neg hk, if_pos heven, if_neg hl]

theorem tCircuitF_succ_odd_base {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (hodd : ¬ k % 2 = 0) (hl : l ≤ 2) :
    tCircuitF (R := R) (fuel + 1) k l =
      tOddBaseCircuit k (tCircuitF fuel ((k - 1) / 2) 3) := by
  rw [tCircuitF, if_neg hk, if_neg hodd, if_pos hl]

theorem tCircuitF_succ_odd_main {R : Type u} [CommRing R] (fuel k l : ℕ)
    (hk : ¬ k ≤ 1) (hodd : ¬ k % 2 = 0) (hl : ¬ l ≤ 2) :
    tCircuitF (R := R) (fuel + 1) k l =
      tOddMainCircuit k l (tCircuitF fuel ((k - 1) / 2) (l + 1)) := by
  rw [tCircuitF, if_neg hk, if_neg hodd, if_neg hl]

/-! ## Semantic reflection -/

section semantics

variable {R : Type u} {A : Type w} [CommRing R] [CommRing A] [Algebra R A]

private noncomputable def tenv (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) : ConstructionInput → A[X] :=
  constructionEnv powers shifted parameters source

@[simp] private theorem eval_tmers (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) (k : ℕ) (parameterMap : ℕ → ℕ) :
    (tmers (R := R) k parameterMap).eval (tenv powers shifted parameters source) 0 =
      FastPoly.peel powers k (parameters ∘ parameterMap) := by
  rw [tmers, tenv, Circuit.eval_reindexConstructionParameters]
  exact eval_peelCircuit (R := R) powers shifted (parameters ∘ parameterMap)
    source k

private theorem eval_recurseWithPowerPair {m : ℕ} (level : ℕ)
    (parameterMap : ℕ → ℕ) (powerSlot shiftedSlot : Fin m)
    (inner : Circuit R ConstructionInput 2) (powers : ℕ → A[X])
    (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) (values : Fin m → A[X]) :
    (recurseWithPowerPair level parameterMap powerSlot shiftedSlot inner).eval
        (Sum.elim (tenv powers shifted parameters source) values) =
      inner.eval
        (tenv (Function.update powers level (values powerSlot))
          (values shiftedSlot) (parameters ∘ parameterMap) source) := by
  rw [recurseWithPowerPair, Circuit.eval_relabel]
  apply congrArg (inner.eval)
  exact constructionEnv_withPowerPair powers shifted parameters source
    values level parameterMap powerSlot shiftedSlot

@[simp] private theorem eval_tEvenBasePowerPair_zero (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tEvenBasePowerPair (R := R) k).eval (tenv powers shifted parameters source) 0 =
      FastPoly.ebH powers k parameters := by
  rw [tEvenBasePowerPair]
  change
    (Circuit.diffSquareAdd (th (R := R) 1) (.add tx (ta (2 * k - 3)))
      (ta (2 * k - 4))).eval (tenv powers shifted parameters source) 0 = _
  rw [Circuit.eval_diffSquareAdd]
  rfl

@[simp] private theorem eval_tEvenBasePowerPair_one (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tEvenBasePowerPair (R := R) k).eval (tenv powers shifted parameters source) 1 =
      FastPoly.ebH powers k parameters + (shifted - powers 1) := by
  rw [tEvenBasePowerPair]
  change
    (Circuit.diffSquareAdd (th (R := R) 1) (.add tx (ta (2 * k - 3)))
        (ta (2 * k - 4))).eval (tenv powers shifted parameters source) 0 +
      (shifted - powers 1) = _
  rw [Circuit.eval_diffSquareAdd]
  rfl

private theorem eval_tEvenBaseCircuit (k : ℕ) (inner : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tEvenBaseCircuit k inner).eval (tenv powers shifted parameters source) =
      inner.eval
        (tenv (Function.update powers 2 (FastPoly.ebH powers k parameters))
          (FastPoly.ebH powers k parameters + (shifted - powers 1)) parameters
          source) := by
  rw [tEvenBaseCircuit, Circuit.eval_bind, eval_recurseWithPowerPair]
  rw [eval_tEvenBasePowerPair_zero, eval_tEvenBasePowerPair_one]
  rfl

@[simp] private theorem eval_tEvenMainPowerPair_zero (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tEvenMainPowerPair (R := R) k l).eval (tenv powers shifted parameters source) 0 =
      FastPoly.evenH powers k l parameters := by
  rw [tEvenMainPowerPair]
  change
    (Circuit.diffSquareAdd (th (R := R) l)
        (.add (th (l - 1))
          (tmers (l - 1) (fun j => (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j)))
        (tmers (l - 1) (fun j => (k - 2) * 2 ^ l + 1 + j))).eval
      (tenv powers shifted parameters source) 0 = _
  rw [Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add]
  rw [eval_tmers, eval_tmers]
  rfl

@[simp] private theorem eval_tEvenMainPowerPair_one (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tEvenMainPowerPair (R := R) k l).eval (tenv powers shifted parameters source) 1 =
      FastPoly.evenHt powers shifted k l parameters := by
  rw [tEvenMainPowerPair]
  change
    (Circuit.diffSquareAdd (tht (R := R))
        (.add (th (l - 1)) (ta ((k - 2) * 2 ^ l + 2 ^ (l - 1))))
        (ta ((k - 2) * 2 ^ l))).eval (tenv powers shifted parameters source) 0 = _
  rw [Circuit.eval_diffSquareAdd]
  rfl

private theorem eval_tEvenMainCircuit (k l : ℕ) (inner : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tEvenMainCircuit k l inner).eval (tenv powers shifted parameters source) =
      inner.eval
        (tenv (Function.update powers (l + 1) (FastPoly.evenH powers k l parameters))
          (FastPoly.evenHt powers shifted k l parameters) parameters source) := by
  rw [tEvenMainCircuit, Circuit.eval_bind, eval_recurseWithPowerPair]
  rw [eval_tEvenMainPowerPair_zero, eval_tEvenMainPowerPair_one]
  rfl

/-- Scaling a circuit by a natural-number constant has the same semantics as the
corresponding repeated additive scalar action.  This bridge is characteristic-free. -/
@[simp] private theorem eval_scale_nat {I : Type v} (n : ℕ)
    (p : Circuit R I 1) (env : I → A[X]) :
    (Circuit.scale ((n : ℕ) : R) p).eval env 0 = n • p.eval env 0 := by
  rw [Circuit.eval_scale]
  rw [map_natCast, ← nsmul_eq_mul]

@[simp] private theorem eval_tOddBaseAux_zero (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddBaseAux (R := R) k).eval (tenv powers shifted parameters source) 0 =
      FastPoly.obH8 powers k parameters := by
  simp only [tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork, Circuit.eval_add,
    Circuit.eval_sub, Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft,
    Circuit.eval_rightInput, tenv]
  rfl

@[simp] private theorem eval_tOddBaseAux_one (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddBaseAux (R := R) k).eval (tenv powers shifted parameters source) 1 =
      FastPoly.obH8 powers k parameters + C (parameters (4 * (k - 2))) := by
  simp only [tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork, Circuit.eval_add,
    Circuit.eval_sub, Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft,
    Circuit.eval_rightInput, tenv]
  rfl

@[simp] private theorem eval_tOddBaseAux_two (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddBaseAux (R := R) k).eval (tenv powers shifted parameters source) 2 =
      powers 2 - (k - 1) • FastPoly.obS1 powers k parameters := by
  change powers 2 - algebraMap R A[X] ((k - 1 : ℕ) : R) *
      (powers 1 + (X + C (parameters (4 * (k - 2) + 3)))) =
    powers 2 - (k - 1) • (powers 1 + (X + C (parameters (4 * (k - 2) + 3))))
  have hscale : algebraMap R A[X] ((k - 1 : ℕ) : R) *
      (powers 1 + (X + C (parameters (4 * (k - 2) + 3)))) =
        (k - 1) • (powers 1 + (X + C (parameters (4 * (k - 2) + 3)))) := by
    rw [map_natCast, ← nsmul_eq_mul]
  rw [hscale]

@[simp] private theorem eval_tOddBaseAux_three (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddBaseAux (R := R) k).eval (tenv powers shifted parameters source) 3 =
      shifted - (k - 1) •
        (FastPoly.obS1 powers k parameters - (shifted - powers 2)) := by
  change shifted - algebraMap R A[X] ((k - 1 : ℕ) : R) *
      ((powers 1 + (X + C (parameters (4 * (k - 2) + 3)))) -
        (shifted - powers 2)) =
    shifted - (k - 1) •
      ((powers 1 + (X + C (parameters (4 * (k - 2) + 3)))) -
        (shifted - powers 2))
  have hscale : algebraMap R A[X] ((k - 1 : ℕ) : R) *
      ((powers 1 + (X + C (parameters (4 * (k - 2) + 3)))) -
        (shifted - powers 2)) =
      (k - 1) • ((powers 1 + (X + C (parameters (4 * (k - 2) + 3)))) -
        (shifted - powers 2)) := by
    rw [map_natCast, ← nsmul_eq_mul]
  rw [hscale]

@[simp] private theorem eval_tOddBaseAux_four (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddBaseAux (R := R) k).eval (tenv powers shifted parameters source) 4 =
      FastPoly.peel powers 2 (fun j ↦ parameters (1 + j)) := by
  simp only [tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork, Circuit.eval_add,
    Circuit.eval_sub, Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft,
    Circuit.eval_rightInput]
  exact eval_tmers powers shifted parameters source 2 (fun j ↦ 1 + j)

@[simp] private theorem eval_tOddBaseAux_five (k : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddBaseAux (R := R) k).eval (tenv powers shifted parameters source) 5 =
      C (parameters 0) := by
  simp only [tOddBaseAux, Circuit.eval_bind, Circuit.eval_fork, Circuit.eval_add,
    Circuit.eval_sub, Circuit.eval_diffSquareAdd, Circuit.eval_liftLeft,
    Circuit.eval_rightInput, tenv]
  rfl

@[simp] private theorem eval_tOddMainShiftPair_zero (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainShiftPair (R := R) k l).eval (tenv powers shifted parameters source) 0 =
      FastPoly.tS1 powers k l parameters := by
  rw [tOddMainShiftPair]
  change powers (l - 1) +
    (tmers (R := R) (l - 1)
      (fun j ↦ (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j)).eval
        (tenv powers shifted parameters source) 0 = _
  rw [eval_tmers]
  rfl

@[simp] private theorem eval_tOddMainShiftPair_one (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainShiftPair (R := R) k l).eval (tenv powers shifted parameters source) 1 =
      FastPoly.tS1t powers k l parameters := by
  rw [tOddMainShiftPair]
  rfl

@[simp] private theorem eval_tOddMainAux_zero (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainAux (R := R) k l).eval (tenv powers shifted parameters source) 0 =
      FastPoly.oddH powers k l parameters := by
  rw [tOddMainAux, Circuit.eval_bind]
  rw [Circuit.eval_fork]
  rw [show (0 : Fin 6) = Fin.castAdd 4 (0 : Fin 2) from rfl]
  simp only [Fin.addCases_left]
  rw [Circuit.eval_fork]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_left]
  rw [Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput]
  rw [show (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 from rfl]
  rw [eval_tOddMainShiftPair_zero, eval_tmers, eval_tmers]
  rfl

@[simp] private theorem eval_tOddMainAux_one (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainAux (R := R) k l).eval (tenv powers shifted parameters source) 1 =
      FastPoly.oddHt powers shifted k l parameters := by
  rw [tOddMainAux, Circuit.eval_bind, Circuit.eval_fork]
  rw [show (1 : Fin 6) = Fin.castAdd 4 (1 : Fin 2) from rfl]
  simp only [Fin.addCases_left]
  rw [Circuit.eval_fork]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.eval_diffSquareAdd]
  simp only [Circuit.eval_add, Circuit.eval_liftLeft, Circuit.eval_rightInput]
  rw [show (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 from rfl]
  rw [eval_tOddMainShiftPair_one]
  rfl

@[simp] private theorem eval_tOddMainAux_two (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainAux (R := R) k l).eval (tenv powers shifted parameters source) 2 =
      powers l - (k - 1) • FastPoly.tS1 powers k l parameters := by
  rw [tOddMainAux, Circuit.eval_bind, Circuit.eval_fork]
  rw [show (2 : Fin 6) = Fin.natAdd 2 (0 : Fin 4) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.eval_fork]
  rw [show (0 : Fin 4) = Fin.castAdd 2 (0 : Fin 2) from rfl]
  simp only [Fin.addCases_left]
  rw [Circuit.eval_fork]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_left, Circuit.eval_sub, eval_scale_nat,
    Circuit.eval_liftLeft, Circuit.eval_rightInput]
  rw [show (Fin.castAdd 1 (0 : Fin 1) : Fin 2) = 0 from rfl]
  rw [eval_tOddMainShiftPair_zero]
  rfl

@[simp] private theorem eval_tOddMainAux_three (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainAux (R := R) k l).eval (tenv powers shifted parameters source) 3 =
      shifted - (k - 1) • FastPoly.tS1t powers k l parameters := by
  rw [tOddMainAux, Circuit.eval_bind, Circuit.eval_fork]
  rw [show (3 : Fin 6) = Fin.natAdd 2 (1 : Fin 4) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.eval_fork]
  rw [show (1 : Fin 4) = Fin.castAdd 2 (1 : Fin 2) from rfl]
  simp only [Fin.addCases_left]
  rw [Circuit.eval_fork]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_right, Circuit.eval_sub, eval_scale_nat,
    Circuit.eval_liftLeft, Circuit.eval_rightInput]
  rw [show (Fin.natAdd 1 (0 : Fin 1) : Fin 2) = 1 from rfl]
  rw [eval_tOddMainShiftPair_one]
  rfl

@[simp] private theorem eval_tOddMainAux_four (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainAux (R := R) k l).eval (tenv powers shifted parameters source) 4 =
      FastPoly.peel powers l (fun j ↦ parameters (1 + j)) := by
  rw [tOddMainAux, Circuit.eval_bind, Circuit.eval_fork]
  rw [show (4 : Fin 6) = Fin.natAdd 2 (2 : Fin 4) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.eval_fork]
  rw [show (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.eval_fork]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_left, Circuit.eval_liftLeft]
  exact eval_tmers powers shifted parameters source l (fun j ↦ 1 + j)

@[simp] private theorem eval_tOddMainAux_five (k l : ℕ)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (tOddMainAux (R := R) k l).eval (tenv powers shifted parameters source) 5 =
      C (parameters 0) := by
  rw [tOddMainAux, Circuit.eval_bind, Circuit.eval_fork]
  rw [show (5 : Fin 6) = Fin.natAdd 2 (3 : Fin 4) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.eval_fork]
  rw [show (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.eval_fork]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_right, Circuit.eval_liftLeft]
  rfl

private theorem eval_finishOdd_zero (level : ℕ) (parameterMap : ℕ → ℕ)
    (aux : Circuit R ConstructionInput 6) (inner : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (finishOdd level parameterMap aux inner).eval (tenv powers shifted parameters source) 0 =
      aux.eval (tenv powers shifted parameters source) 2 *
          inner.eval
            (tenv
              (Function.update powers level
                (aux.eval (tenv powers shifted parameters source) 0))
              (aux.eval (tenv powers shifted parameters source) 1)
              (parameters ∘ parameterMap) source) 0 +
        aux.eval (tenv powers shifted parameters source) 4 := by
  rw [finishOdd, Circuit.eval_bind, Circuit.eval_bind]
  rw [eval_recurseWithPowerPair]
  rw [Circuit.eval_fork]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_left, Circuit.eval_add, Circuit.eval_mul,
    priorBound, Circuit.eval_rightInput]
  rfl

private theorem eval_finishOdd_one (level : ℕ) (parameterMap : ℕ → ℕ)
    (aux : Circuit R ConstructionInput 6) (inner : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    (finishOdd level parameterMap aux inner).eval (tenv powers shifted parameters source) 1 =
      aux.eval (tenv powers shifted parameters source) 3 *
          inner.eval
            (tenv
              (Function.update powers level
                (aux.eval (tenv powers shifted parameters source) 0))
              (aux.eval (tenv powers shifted parameters source) 1)
              (parameters ∘ parameterMap) source) 1 +
        aux.eval (tenv powers shifted parameters source) 5 := by
  rw [finishOdd, Circuit.eval_bind, Circuit.eval_bind]
  rw [eval_recurseWithPowerPair]
  rw [Circuit.eval_fork]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_right, Circuit.eval_add, Circuit.eval_mul,
    priorBound, Circuit.eval_rightInput]
  rfl

private theorem eval_tOddBaseCircuit (k : ℕ) (inner : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    ((tOddBaseCircuit k inner).eval (tenv powers shifted parameters source) 0,
      (tOddBaseCircuit k inner).eval (tenv powers shifted parameters source) 1) =
      FastPoly.obOut powers shifted k parameters
        (inner.eval
            (tenv
              (Function.update powers 3 (FastPoly.obH8 powers k parameters))
              (FastPoly.obH8 powers k parameters +
                C (parameters (4 * (k - 2))))
              (fun j ↦ parameters (4 + j)) source) 0,
          inner.eval
            (tenv
              (Function.update powers 3 (FastPoly.obH8 powers k parameters))
              (FastPoly.obH8 powers k parameters +
                C (parameters (4 * (k - 2))))
              (fun j ↦ parameters (4 + j)) source) 1) := by
  apply Prod.ext
  · change (tOddBaseCircuit k inner).eval (tenv powers shifted parameters source) 0 = _
    rw [tOddBaseCircuit, eval_finishOdd_zero]
    rw [eval_tOddBaseAux_zero, eval_tOddBaseAux_one, eval_tOddBaseAux_two,
      eval_tOddBaseAux_four]
    rfl
  · change (tOddBaseCircuit k inner).eval (tenv powers shifted parameters source) 1 = _
    rw [tOddBaseCircuit, eval_finishOdd_one]
    rw [eval_tOddBaseAux_zero, eval_tOddBaseAux_one, eval_tOddBaseAux_three,
      eval_tOddBaseAux_five]
    rfl

private theorem eval_tOddMainCircuit (k l : ℕ) (inner : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    ((tOddMainCircuit k l inner).eval (tenv powers shifted parameters source) 0,
      (tOddMainCircuit k l inner).eval (tenv powers shifted parameters source) 1) =
      FastPoly.oddOut powers shifted k l parameters
        (inner.eval
            (tenv
              (Function.update powers (l + 1) (FastPoly.oddH powers k l parameters))
              (FastPoly.oddHt powers shifted k l parameters)
              (fun j ↦ parameters (2 ^ l + j)) source) 0,
          inner.eval
            (tenv
              (Function.update powers (l + 1) (FastPoly.oddH powers k l parameters))
              (FastPoly.oddHt powers shifted k l parameters)
              (fun j ↦ parameters (2 ^ l + j)) source) 1) := by
  apply Prod.ext
  · change (tOddMainCircuit k l inner).eval (tenv powers shifted parameters source) 0 = _
    rw [tOddMainCircuit, eval_finishOdd_zero]
    rw [eval_tOddMainAux_zero, eval_tOddMainAux_one, eval_tOddMainAux_two,
      eval_tOddMainAux_four]
    rfl
  · change (tOddMainCircuit k l inner).eval (tenv powers shifted parameters source) 1 = _
    rw [tOddMainCircuit, eval_finishOdd_one]
    rw [eval_tOddMainAux_zero, eval_tOddMainAux_one, eval_tOddMainAux_three,
      eval_tOddMainAux_five]
    rfl

/-- The compiler follows `TF` branch for branch.  This theorem has no
characteristic or unit hypotheses: those enter only when the resulting coefficient
map is decoded. -/
private theorem eval_tCircuitF : ∀ fuel k l (powers : ℕ → A[X])
    (shifted : A[X]) (parameters : ℕ → A) (source : Fin 2 → A[X]),
    ((tCircuitF (R := R) fuel k l).eval (tenv powers shifted parameters source) 0,
      (tCircuitF (R := R) fuel k l).eval (tenv powers shifted parameters source) 1) =
      FastPoly.TF fuel k l powers shifted parameters := by
  intro fuel
  induction fuel with
  | zero =>
      intro k l powers shifted parameters source
      rfl
  | succ fuel ih =>
      intro k l powers shifted parameters source
      by_cases hk : k ≤ 1
      · rw [tCircuitF_succ_le_one fuel k l hk,
          FastPoly.TF_succ_le_one hk]
        rfl
      · by_cases heven : k % 2 = 0
        · by_cases hl : l ≤ 1
          · rw [tCircuitF_succ_even_base fuel k l hk heven hl,
              FastPoly.TF_succ_even_base hk heven hl]
            rw [eval_tEvenBaseCircuit]
            exact ih (k / 2) 2
              (Function.update powers 2 (FastPoly.ebH powers k parameters))
              (FastPoly.ebH powers k parameters + (shifted - powers 1)) parameters
              source
          · rw [tCircuitF_succ_even_main fuel k l hk heven hl,
              FastPoly.TF_succ_even_main hk heven hl]
            rw [eval_tEvenMainCircuit]
            exact ih (k / 2) (l + 1)
              (Function.update powers (l + 1) (FastPoly.evenH powers k l parameters))
              (FastPoly.evenHt powers shifted k l parameters) parameters source
        · by_cases hl : l ≤ 2
          · rw [tCircuitF_succ_odd_base fuel k l hk heven hl,
              FastPoly.TF_succ_odd_base hk heven hl]
            rw [eval_tOddBaseCircuit]
            rw [ih]
          · rw [tCircuitF_succ_odd_main fuel k l hk heven hl,
              FastPoly.TF_succ_odd_main hk heven hl]
            rw [eval_tOddMainCircuit]
            rw [ih]

/-- Source-irrelevance form requested by the retained-shift compiler: the `T`
circuit never reads its source wires, so its semantics holds under an arbitrary
source environment. -/
theorem eval_tCircuit_with_source (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) (k l : ℕ) :
    ((tCircuit (R := R) k l).eval
        (constructionEnv powers shifted parameters source) 0,
      (tCircuit (R := R) k l).eval
        (constructionEnv powers shifted parameters source) 1) =
      FastPoly.Tpair powers shifted k l parameters :=
  eval_tCircuitF k k l powers shifted parameters source

/-- Semantic correctness of the compiled `Tpair` straight-line program. -/
theorem eval_tCircuit (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (k l : ℕ) :
    ((tCircuit (R := R) k l).eval
        (constructionEnv powers shifted parameters (fun _ ↦ 0)) 0,
      (tCircuit (R := R) k l).eval
        (constructionEnv powers shifted parameters (fun _ ↦ 0)) 1) =
      FastPoly.Tpair powers shifted k l parameters := by
  exact eval_tCircuitF k k l powers shifted parameters (fun _ ↦ 0)

end semantics

end FastPoly.Cost
