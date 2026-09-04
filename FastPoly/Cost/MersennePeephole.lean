import FastPoly.Cost.MersenneCircuitCount

/-!
# The optimized level-two Mersenne peephole

The uniform semantic compiler in `MersenneCircuit.lean` uses the same fill datum at
every level.  At level two its left head is therefore

`H₄ + Q₁ = H₄ + (x + c)`.

The manuscript uses a genuine peephole at this one level: it replaces that head by
`H₄ + c`.  This removes exactly one addition and leaves the multiplication topology
unchanged.  It also changes the polynomial family, so this file deliberately defines a
separate semantic sibling instead of asserting a false equality with `FastPoly.mers`.

Above level two the compiler is the generic fill compiler.  The definitions and proofs
below are characteristic-independent; only a future decoding theorem for the resulting
family can introduce admissibility assumptions.
-/

namespace FastPoly.Cost.MersennePeephole

open Polynomial

universe u v

private abbrev xWire {R : Type u} : Circuit R ConstructionInput 1 :=
  Circuit.constructionX

private abbrev powerWire {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionPower i

private abbrev parameterWire {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionParameter i

private abbrev reindex {R : Type u} (f : ℕ → ℕ)
    (c : Circuit R ConstructionInput 1) : Circuit R ConstructionInput 1 :=
  c.reindexConstructionParameters f

/-! ## The scalar-head level-two datum -/

/-- Polynomial data for the optimized level-two step.  If `p = doff k 2`, the slots
have the following manuscript interpretation (up to a harmless renaming):

* `p+2` is `β₃`, the scalar in the left head `H₄+β₃`;
* `p` is `β₄`, the scalar in the right head `H₄+β₄`;
* `p+3,p+4,p+5` are the three parameters of the additive `Q₃`;
* `p+1` is the right additive scalar `α₂`.
-/
noncomputable def scalarHeadDataValue {A : Type v} [CommRing A]
    (rec : ℕ → (ℕ → A) → A[X]) (k : ℕ) (parameters : ℕ → A) :
    FastPoly.FillData A :=
  let p := FastPoly.doff k 2
  { q := C (parameters (p + 2))
    qh := rec 2 (fun j => parameters (p + 3 + j))
    b := parameters p
    ah := parameters (p + 1) }

/-- Circuit data for the same optimized level-two step. -/
def scalarHeadDataCircuit {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k : ℕ) :
    FillCircuitData R ConstructionInput :=
  let p := FastPoly.doff k 2
  { q := parameterWire (p + 2)
    qh := reindex (fun j => p + 3 + j) (rec 2)
    b := parameterWire p
    ah := parameterWire (p + 1) }

/-- All higher levels retain the uniform datum.  Only `i=2` selects the scalar-head
peephole. -/
noncomputable def fillDataValue {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (rec : ℕ → (ℕ → A) → A[X])
    (k : ℕ) (parameters : ℕ → A) (i : ℕ) : FastPoly.FillData A :=
  if i = 2 then scalarHeadDataValue rec k parameters
  else FastPoly.mersD powers rec k parameters i

/-- Circuit-valued counterpart of `fillDataValue`. -/
def fillDataCircuit {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k i : ℕ) :
    FillCircuitData R ConstructionInput :=
  if i = 2 then scalarHeadDataCircuit rec k
  else
    { q := reindex (fun j => FastPoly.doff k i + 2 + j) (rec (i - 1))
      qh := reindex
        (fun j => FastPoly.doff k i + 2 + (2 ^ (i - 1) - 1) + j) (rec i)
      b := parameterWire (FastPoly.doff k i)
      ah := parameterWire (FastPoly.doff k i + 1) }

/-! ## Independent polynomial semantics -/

/-- The pair produced by the optimized fill, before the final `(x+β₀)` head. -/
noncomputable def fillPairValue {A : Type v} [CommRing A]
    (powers : ℕ → A[X]) (rec : ℕ → (ℕ → A) → A[X])
    (k : ℕ) (parameters : ℕ → A) (l : ℕ) (source : A[X] × A[X]) :
    A[X] × A[X] :=
  let chain := FastPoly.fillChain powers (fillDataValue powers rec k parameters) l source
  ((powers 1 + C (parameters 1)) * chain.1 + C (parameters 4),
    (powers 1 + C (parameters 2)) * chain.2 + C (parameters 3))

/-- Fuel-indexed optimized Mersenne family.  Its bases and all levels above two agree
with the uniform family; recursive fills use `scalarHeadDataValue` at their bottom
level. -/
noncomputable def valueF {A : Type v} [CommRing A] (powers : ℕ → A[X]) :
    ℕ → ℕ → (ℕ → A) → A[X]
  | 0, _, parameters => X + C (parameters 0)
  | f + 1, k, parameters =>
      match k with
      | 0 => X + C (parameters 0)
      | 1 => X + C (parameters 0)
      | 2 => (X + C (parameters 2)) * (powers 1 + C (parameters 1)) +
          C (parameters 0)
      | 3 =>
          (X + C (parameters 0)) *
              ((powers 1 + C (parameters 1)) * (powers 2 + C (parameters 5)) +
                C (parameters 4)) +
            ((powers 1 + C (parameters 2)) * (powers 2 + C (parameters 6)) +
              C (parameters 3))
      | kk + 4 =>
          let source : A[X] × A[X] :=
            (powers (kk + 3) + valueF powers f (kk + 2) (fun j => parameters (6 + j)),
              powers (kk + 3) + C (parameters 5))
          let pair := fillPairValue powers (valueF powers f) (kk + 4) parameters
            (kk + 2) source
          (X + C (parameters 0)) * pair.1 + pair.2

/-- The optimized Mersenne polynomial at its canonical fuel. -/
noncomputable def value {A : Type v} [CommRing A] (powers : ℕ → A[X])
    (k : ℕ) (parameters : ℕ → A) : A[X] :=
  valueF powers k k parameters

/-! ## Semantic compiler -/

/-- The level-one pair head, kept separate from the final affine head so its exact
`(4 additions, 2 multiplications)` cost is visible in the syntax. -/
def pairHead {R : Type u} (source : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 2 :=
  .bind source <|
    .fork
      (.add
        (.mul (.add (powerWire 1).liftLeft (parameterWire 1).liftLeft)
          (Circuit.rightInput (R := R) (i := (0 : Fin 2))))
        (parameterWire 4).liftLeft)
      (.add
        (.mul (.add (powerWire 1).liftLeft (parameterWire 2).liftLeft)
          (Circuit.rightInput (R := R) (i := (1 : Fin 2))))
        (parameterWire 3).liftLeft)

/-- The final `(x+β₀)A¹+A²` head. -/
def outerHead {R : Type u} (source : Circuit R ConstructionInput 2) :
    Circuit R ConstructionInput 1 :=
  .bind source <|
    .add
      (.mul (.add xWire.liftLeft (parameterWire 0).liftLeft)
        (Circuit.rightInput (R := R) (i := (0 : Fin 2))))
      (Circuit.rightInput (R := R) (i := (1 : Fin 2)))

/-- Compile one optimized fill pair from a recursively compiled Mersenne family. -/
def fillPairCircuit {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k l : ℕ)
    (source : Circuit R ConstructionInput 2) : Circuit R ConstructionInput 2 :=
  pairHead <| Circuit.fillChain (fun i => powerWire i) (fillDataCircuit rec k) l source

/-- Fuel-indexed circuit for `valueF`. -/
def circuitF {R : Type u} : ℕ → ℕ → Circuit R ConstructionInput 1
  | 0, _ => .add xWire (parameterWire 0)
  | f + 1, k =>
      match k with
      | 0 => .add xWire (parameterWire 0)
      | 1 => .add xWire (parameterWire 0)
      | 2 => .add
          (.mul (.add xWire (parameterWire 2))
            (.add (powerWire 1) (parameterWire 1)))
          (parameterWire 0)
      | 3 => .add
          (.mul (.add xWire (parameterWire 0))
            (.add
              (.mul (.add (powerWire 1) (parameterWire 1))
                (.add (powerWire 2) (parameterWire 5)))
              (parameterWire 4)))
          (.add
            (.mul (.add (powerWire 1) (parameterWire 2))
              (.add (powerWire 2) (parameterWire 6)))
            (parameterWire 3))
      | kk + 4 =>
          let source : Circuit R ConstructionInput 2 :=
            .fork
              (.add (powerWire (kk + 3))
                (reindex (fun j => 6 + j) (circuitF f (kk + 2))))
              (.add (powerWire (kk + 3)) (parameterWire 5))
          outerHead <| fillPairCircuit (circuitF f) (kk + 4) (kk + 2) source

/-- The canonical optimized semantic circuit. -/
def circuit {R : Type u} (k : ℕ) : Circuit R ConstructionInput 1 :=
  circuitF k k

theorem circuitF_succ_four {R : Type u} (f kk : ℕ) :
    circuitF (R := R) (f + 1) (kk + 4) =
      let source : Circuit R ConstructionInput 2 :=
        .fork
          (.add (powerWire (kk + 3))
            (reindex (fun j => 6 + j) (circuitF f (kk + 2))))
          (.add (powerWire (kk + 3)) (parameterWire 5))
      outerHead (fillPairCircuit (circuitF f) (kk + 4) (kk + 2) source) :=
  rfl

theorem valueF_succ_four {A : Type v} [CommRing A] (powers : ℕ → A[X])
    (parameters : ℕ → A) (f kk : ℕ) :
    valueF powers (f + 1) (kk + 4) parameters =
      let source : A[X] × A[X] :=
        (powers (kk + 3) + valueF powers f (kk + 2) (fun j => parameters (6 + j)),
          powers (kk + 3) + C (parameters 5))
      let pair := fillPairValue powers (valueF powers f) (kk + 4) parameters
        (kk + 2) source
      (X + C (parameters 0)) * pair.1 + pair.2 :=
  rfl

section semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private noncomputable def env (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) : ConstructionInput → A[X] :=
  constructionEnv powers shifted parameters source

@[simp] theorem eval_pairHead (source : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (initial : Fin 2 → A[X]) :
    ((pairHead source).eval (env powers shifted parameters initial) 0,
      (pairHead source).eval (env powers shifted parameters initial) 1) =
      ((powers 1 + C (parameters 1)) *
          source.eval (env powers shifted parameters initial) 0 + C (parameters 4),
        (powers 1 + C (parameters 2)) *
          source.eval (env powers shifted parameters initial) 1 + C (parameters 3)) := by
  apply Prod.ext
  · change (pairHead source).eval (env powers shifted parameters initial) 0 =
        (powers 1 + C (parameters 1)) *
          source.eval (env powers shifted parameters initial) 0 + C (parameters 4)
    rw [pairHead, Circuit.eval_bind, Circuit.eval_fork_zero]
    rfl
  · change (pairHead source).eval (env powers shifted parameters initial) 1 =
        (powers 1 + C (parameters 2)) *
          source.eval (env powers shifted parameters initial) 1 + C (parameters 3)
    rw [pairHead, Circuit.eval_bind, Circuit.eval_fork_one]
    rfl

@[simp] theorem eval_outerHead (source : Circuit R ConstructionInput 2)
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (initial : Fin 2 → A[X]) :
    (outerHead source).eval (env powers shifted parameters initial) 0 =
      (X + C (parameters 0)) * source.eval (env powers shifted parameters initial) 0 +
        source.eval (env powers shifted parameters initial) 1 := by
  rw [outerHead, Circuit.eval_bind]
  rfl

/-- Literal semantics of the manuscript's optimized middle A₄ step.  The first
component uses the scalar head `H₄+c`, not the uniform head `H₄+(x+c)`. -/
theorem eval_scalarHeadStep
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (initial : Fin 2 → A[X]) (recCircuit : ℕ → Circuit R ConstructionInput 1)
    (recValue : ℕ → (ℕ → A) → A[X])
    (hrec : ∀ p, (recCircuit 2).eval (env powers shifted p initial) 0 = recValue 2 p)
    (k : ℕ) (source : Circuit R ConstructionInput 2) :
    let p := FastPoly.doff k 2
    let step := Circuit.fillStep (powerWire 2) (scalarHeadDataCircuit recCircuit k) source
    (step.eval (env powers shifted parameters initial) 0,
      step.eval (env powers shifted parameters initial) 1) =
      ((powers 2 + C (parameters (p + 2))) *
          source.eval (env powers shifted parameters initial) 0 +
            recValue 2 (fun j => parameters (p + 3 + j)),
        (powers 2 + C (parameters p)) *
          source.eval (env powers shifted parameters initial) 1 +
            C (parameters (p + 1))) := by
  dsimp only
  apply Prod.ext
  · change
      (Circuit.fillStep (powerWire 2) (scalarHeadDataCircuit recCircuit k) source).eval
          (env powers shifted parameters initial) 0 = _
    rw [Circuit.eval_fillStep_zero]
    change (powers 2 + C (parameters (FastPoly.doff k 2 + 2))) *
          source.eval (env powers shifted parameters initial) 0 +
        (reindex (fun j => FastPoly.doff k 2 + 3 + j) (recCircuit 2)).eval
          (env powers shifted parameters initial) 0 = _
    rw [env, reindex, Circuit.eval_reindexConstructionParameters]
    change (powers 2 + C (parameters (FastPoly.doff k 2 + 2))) *
          source.eval (env powers shifted parameters initial) 0 +
        (recCircuit 2).eval
          (env powers shifted
            (parameters ∘ fun j => FastPoly.doff k 2 + 3 + j) initial) 0 = _
    rw [hrec]
    rfl
  · change
      (Circuit.fillStep (powerWire 2) (scalarHeadDataCircuit recCircuit k) source).eval
          (env powers shifted parameters initial) 1 = _
    rw [Circuit.eval_fillStep_one]
    rfl

/-- Evaluation of the optimized fill-pair compiler. -/
theorem eval_fillPairCircuit
    (powers : ℕ → A[X]) (shifted : A[X]) (parameters : ℕ → A)
    (initial : Fin 2 → A[X]) (recCircuit : ℕ → Circuit R ConstructionInput 1)
    (recValue : ℕ → (ℕ → A) → A[X])
    (hrec : ∀ i p, (recCircuit i).eval (env powers shifted p initial) 0 = recValue i p)
    (k l : ℕ) (source : Circuit R ConstructionInput 2) :
    ((fillPairCircuit recCircuit k l source).eval
        (env powers shifted parameters initial) 0,
      (fillPairCircuit recCircuit k l source).eval
        (env powers shifted parameters initial) 1) =
      fillPairValue powers recValue k parameters l
        (source.eval (env powers shifted parameters initial) 0,
          source.eval (env powers shifted parameters initial) 1) := by
  rw [fillPairCircuit, eval_pairHead]
  have hchain := Circuit.eval_fillChain
    (fun i => powerWire i) (fillDataCircuit recCircuit k)
    (env powers shifted parameters initial) l source
  have hchain₀ := congrArg Prod.fst hchain
  have hchain₁ := congrArg Prod.snd hchain
  dsimp only at hchain₀ hchain₁
  rw [hchain₀, hchain₁]
  have hpower :
      (fun i => (powerWire (R := R) i).eval (env powers shifted parameters initial) 0) =
        powers := by
    funext i
    rfl
  have hdata : ∀ i,
      (fillDataCircuit recCircuit k i).eval (env powers shifted parameters initial) =
        FillValues.ofPolynomialData (fillDataValue powers recValue k parameters i) := by
    intro i
    by_cases hi : i = 2
    · subst i
      apply FillValues.ext
      · rfl
      · change
          (reindex (fun j => FastPoly.doff k 2 + 3 + j) (recCircuit 2)).eval
              (env powers shifted parameters initial) 0 =
            recValue 2 (fun j => parameters (FastPoly.doff k 2 + 3 + j))
        rw [env, reindex, Circuit.eval_reindexConstructionParameters]
        change (recCircuit 2).eval
            (env powers shifted
              (parameters ∘ fun j => FastPoly.doff k 2 + 3 + j) initial) 0 = _
        rw [hrec]
        rfl
      · rfl
      · rfl
    · rw [fillDataCircuit, fillDataValue, if_neg hi, if_neg hi]
      apply FillValues.ext
      · change
          (reindex (fun j => FastPoly.doff k i + 2 + j) (recCircuit (i - 1))).eval
              (env powers shifted parameters initial) 0 =
            recValue (i - 1) (fun j => parameters (FastPoly.doff k i + 2 + j))
        rw [env, reindex, Circuit.eval_reindexConstructionParameters]
        change (recCircuit (i - 1)).eval
            (env powers shifted
              (parameters ∘ fun j => FastPoly.doff k i + 2 + j) initial) 0 = _
        rw [hrec]
        rfl
      · change
          (reindex
              (fun j => FastPoly.doff k i + 2 + (2 ^ (i - 1) - 1) + j)
              (recCircuit i)).eval (env powers shifted parameters initial) 0 =
            recValue i
              (fun j => parameters
                (FastPoly.doff k i + 2 + (2 ^ (i - 1) - 1) + j))
        rw [env, reindex, Circuit.eval_reindexConstructionParameters]
        change (recCircuit i).eval
            (env powers shifted
              (parameters ∘ fun j =>
                FastPoly.doff k i + 2 + (2 ^ (i - 1) - 1) + j) initial) 0 = _
        rw [hrec]
        rfl
      · rfl
      · rfl
  rw [show (fun i => (fillDataCircuit recCircuit k i).eval
          (env powers shifted parameters initial)) =
        fun i => FillValues.ofPolynomialData
          (fillDataValue powers recValue k parameters i) from funext hdata]
  rw [hpower, fillChainValue_ofPolynomialData]
  rfl

/-- The compiler evaluates to the independently defined optimized family. -/
theorem eval_circuitF (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    ∀ f k,
      (circuitF (R := R) f k).eval (env powers shifted parameters source) 0 =
        valueF powers f k parameters := by
  intro f
  induction f generalizing parameters with
  | zero => intro k; rfl
  | succ f ih =>
      intro k
      rcases k with _ | k
      · rfl
      · rcases k with _ | k
        · rfl
        · rcases k with _ | k
          · rfl
          · rcases k with _ | kk
            · rfl
            · rw [circuitF_succ_four, valueF_succ_four, eval_outerHead]
              let sourceCircuit : Circuit R ConstructionInput 2 :=
                .fork
                  (.add (powerWire (kk + 3))
                    (reindex (fun j => 6 + j) (circuitF f (kk + 2))))
                  (.add (powerWire (kk + 3)) (parameterWire 5))
              have hsource :
                  (sourceCircuit.eval (env powers shifted parameters source) 0,
                    sourceCircuit.eval (env powers shifted parameters source) 1) =
                    (powers (kk + 3) +
                        valueF powers f (kk + 2) (fun j => parameters (6 + j)),
                      powers (kk + 3) + C (parameters 5)) := by
                apply Prod.ext
                · change powers (kk + 3) +
                      (reindex (fun j => 6 + j) (circuitF f (kk + 2))).eval
                        (env powers shifted parameters source) 0 =
                    powers (kk + 3) +
                      valueF powers f (kk + 2) (fun j => parameters (6 + j))
                  rw [env, reindex, Circuit.eval_reindexConstructionParameters]
                  change powers (kk + 3) +
                      (circuitF f (kk + 2)).eval
                        (env powers shifted (parameters ∘ fun j => 6 + j) source) 0 = _
                  rw [ih]
                  rfl
                · rfl
              dsimp only [sourceCircuit] at hsource
              have hpair := eval_fillPairCircuit powers shifted parameters source
                (circuitF (R := R) f) (valueF powers f) (fun i p => ih p i)
                (kk + 4) (kk + 2) sourceCircuit
              have hpair₀ := congrArg Prod.fst hpair
              have hpair₁ := congrArg Prod.snd hpair
              dsimp only at hpair₀ hpair₁
              rw [hpair₀, hpair₁, hsource]

@[simp] theorem eval_circuit (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) (k : ℕ) :
    (circuit (R := R) k).eval (env powers shifted parameters source) 0 =
      value powers k parameters :=
  eval_circuitF powers shifted parameters source k k

end semantics

/-! ## Exact syntax-level costs -/

private def mersClosed (k : ℕ) : GateCount :=
  GateCount.of (5 * 2 ^ (k - 2) - 2) (2 ^ (k - 1) - 1)

private def fillPairClosed (l : ℕ) : GateCount :=
  GateCount.of (5 * (2 ^ (l - 1) + 2 ^ (l - 2)) - 4)
    (2 ^ l + 2 ^ (l - 1) - 1)

@[simp] theorem gates_pairHead {R : Type u} (source : Circuit R ConstructionInput 2) :
    (pairHead source).gates = source.gates + GateCount.of 4 2 := by
  ext <;>
    simp only [pairHead, Circuit.gates_bind, Circuit.gates, Circuit.gates_liftLeft,
      Circuit.gates_rightInput, Circuit.gates_constructionPower,
      Circuit.gates_constructionParameter, GateCount.add_additions,
      GateCount.add_multiplications, GateCount.zero_additions,
      GateCount.zero_multiplications, GateCount.adds_additions,
      GateCount.adds_multiplications, GateCount.muls_additions,
      GateCount.muls_multiplications, GateCount.of_additions,
      GateCount.of_multiplications]

@[simp] theorem gates_outerHead {R : Type u} (source : Circuit R ConstructionInput 2) :
    (outerHead source).gates = source.gates + GateCount.of 2 1 := by
  ext <;>
    simp only [outerHead, Circuit.gates_bind, Circuit.gates, Circuit.gates_liftLeft,
      Circuit.gates_rightInput, Circuit.gates_constructionX,
      Circuit.gates_constructionParameter, GateCount.add_additions,
      GateCount.add_multiplications, GateCount.zero_additions,
      GateCount.zero_multiplications, GateCount.adds_additions,
      GateCount.adds_multiplications, GateCount.muls_additions,
      GateCount.muls_multiplications, GateCount.of_additions,
      GateCount.of_multiplications]

/-- The manuscript A₄ step: one `Q₃`, two head products, and four structural
additions. -/
theorem gates_scalarHeadStep {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k : ℕ)
    (source : Circuit R ConstructionInput 2) :
    (Circuit.fillStep (powerWire 2) (scalarHeadDataCircuit rec k) source).gates =
      source.gates + (rec 2).gates + GateCount.of 4 2 := by
  ext <;>
    simp only [Circuit.fillStep, scalarHeadDataCircuit, Circuit.gates_bind,
      Circuit.gates, Circuit.gates_liftLeft, Circuit.gates_rightInput,
      Circuit.gates_constructionPower, Circuit.gates_constructionParameter,
      Circuit.gates_reindexConstructionParameters, GateCount.add_additions,
      GateCount.add_multiplications, GateCount.zero_additions,
      GateCount.zero_multiplications, GateCount.adds_additions,
      GateCount.adds_multiplications, GateCount.muls_additions,
      GateCount.muls_multiplications, GateCount.of_additions,
      GateCount.of_multiplications] <;> omega

/-- With the optimized three-addition, one-product `Q₃` base, the complete A₄ pair
(the scalar-head middle step followed by `pairHead`) costs exactly eleven additions and
five multiplications, as in `lem:fill-Q-count`. -/
theorem gates_fillPairCircuit_two_exact {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k : ℕ)
    (source : Circuit R ConstructionInput 2)
    (hq₃ : (rec 2).gates = GateCount.of 3 1) :
    (fillPairCircuit rec k 2 source).gates = source.gates + GateCount.of 11 5 := by
  rw [fillPairCircuit]
  change
    (pairHead (Circuit.fillStep (powerWire 2) (scalarHeadDataCircuit rec k) source)).gates = _
  rw [gates_pairHead, gates_scalarHeadStep, hq₃]
  ext <;> rfl

/-- A uniform level-two step with the same recursive inputs spends exactly one more
addition on `Q₁=x+c`; the multiplication counts agree. -/
theorem scalarHeadStep_saves_one {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k : ℕ)
    (source : Circuit R ConstructionInput 2)
    (hq₁ : (rec 1).gates = GateCount.of 1 0) :
    let uniform : FillCircuitData R ConstructionInput :=
      { q := reindex (fun j => FastPoly.doff k 2 + 2 + j) (rec 1)
        qh := reindex (fun j => FastPoly.doff k 2 + 3 + j) (rec 2)
        b := parameterWire (FastPoly.doff k 2)
        ah := parameterWire (FastPoly.doff k 2 + 1) }
    (Circuit.fillStep (powerWire 2) uniform source).gates =
      (Circuit.fillStep (powerWire 2) (scalarHeadDataCircuit rec k) source).gates +
        GateCount.adds 1 := by
  dsimp only
  ext <;>
    simp only [Circuit.fillStep, scalarHeadDataCircuit, Circuit.gates_bind,
      Circuit.gates, Circuit.gates_liftLeft, Circuit.gates_rightInput,
      Circuit.gates_constructionPower, Circuit.gates_constructionParameter,
      Circuit.gates_reindexConstructionParameters, hq₁, GateCount.add_additions,
      GateCount.add_multiplications, GateCount.zero_additions,
      GateCount.zero_multiplications, GateCount.adds_additions,
      GateCount.adds_multiplications, GateCount.muls_additions,
      GateCount.muls_multiplications, GateCount.of_additions,
      GateCount.of_multiplications] <;> omega

private theorem gates_fillStep_of_ne_two {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k i : ℕ) (hi : i ≠ 2)
    (source : Circuit R ConstructionInput 2) :
    (Circuit.fillStep (powerWire i) (fillDataCircuit rec k i) source).gates =
      source.gates + (rec (i - 1)).gates + (rec i).gates + GateCount.of 4 2 := by
  rw [fillDataCircuit, if_neg hi]
  ext <;>
    simp only [Circuit.fillStep, Circuit.gates_bind, Circuit.gates,
      Circuit.gates_liftLeft, Circuit.gates_rightInput,
      Circuit.gates_constructionPower, Circuit.gates_constructionParameter,
      Circuit.gates_reindexConstructionParameters, GateCount.add_additions,
      GateCount.add_multiplications, GateCount.zero_additions,
      GateCount.zero_multiplications, GateCount.adds_additions,
      GateCount.adds_multiplications, GateCount.muls_additions,
      GateCount.muls_multiplications, GateCount.of_additions,
      GateCount.of_multiplications] <;> omega

private theorem fillPairCircuit_two {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k : ℕ)
    (source : Circuit R ConstructionInput 2) :
    fillPairCircuit rec k 2 source =
      pairHead (Circuit.fillStep (powerWire 2) (scalarHeadDataCircuit rec k) source) := by
  rw [fillPairCircuit]
  rfl

private theorem fillPairCircuit_succ_three {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k i : ℕ)
    (source : Circuit R ConstructionInput 2) :
    fillPairCircuit rec k (i + 3) source =
      fillPairCircuit rec k (i + 2)
        (Circuit.fillStep (powerWire (i + 3)) (fillDataCircuit rec k (i + 3)) source) := by
  rfl

private theorem gates_fillPairCircuit {R : Type u}
    (rec : ℕ → Circuit R ConstructionInput 1) (k l : ℕ)
    (source : Circuit R ConstructionInput 2) (hl : 2 ≤ l)
    (hrec : ∀ i, 2 ≤ i → i ≤ l → (rec i).gates = mersClosed i) :
    (fillPairCircuit rec k l source).gates = source.gates + fillPairClosed l := by
  induction l using Nat.strong_induction_on generalizing source with
  | h l ih =>
      match l with
      | 0 => omega
      | 1 => omega
      | 2 =>
          rw [fillPairCircuit_two, gates_pairHead, gates_scalarHeadStep,
            hrec 2 (by omega) (by omega)]
          ext <;> rfl
      | i + 3 =>
          rw [fillPairCircuit_succ_three]
          rw [ih (i + 2) (by omega)
            (Circuit.fillStep (powerWire (i + 3)) (fillDataCircuit rec k (i + 3)) source)
            (by omega) (fun j hj2 hjle => hrec j hj2 (by omega))]
          rw [gates_fillStep_of_ne_two rec k (i + 3) (by omega)]
          rw [show i + 3 - 1 = i + 2 by omega,
            hrec (i + 2) (by omega) (by omega), hrec (i + 3) (by omega) (by omega)]
          have hp : 0 < (2 : ℕ) ^ i := Nat.pow_pos (by omega)
          apply GateCount.ext
          · simp only [mersClosed, add_tsub_cancel_right, Nat.add_one_sub_one,
              pow_succ, Nat.reduceSubDiff, fillPairClosed,
              GateCount.add_additions, GateCount.of_additions]
            omega
          · simp only [mersClosed, add_tsub_cancel_right, Nat.add_one_sub_one,
              pow_succ, Nat.reduceSubDiff, fillPairClosed,
              GateCount.add_multiplications, GateCount.of_multiplications]
            omega

private theorem gates_recursiveSource {R : Type u} (f kk : ℕ) :
    (.fork
        (.add (powerWire (kk + 3))
          (reindex (fun j => 6 + j) (circuitF f (kk + 2))))
        (.add (powerWire (kk + 3)) (parameterWire 5)) :
      Circuit R ConstructionInput 2).gates =
      (circuitF (R := R) f (kk + 2)).gates + GateCount.adds 2 := by
  ext <;>
    simp only [Circuit.gates, Circuit.gates_constructionPower,
      Circuit.gates_constructionParameter, Circuit.gates_reindexConstructionParameters,
      GateCount.add_additions, GateCount.add_multiplications,
      GateCount.zero_additions, GateCount.zero_multiplications,
      GateCount.adds_additions, GateCount.adds_multiplications] <;> omega

/-- Closed gate count for the optimized semantic sibling. -/
private theorem gates_circuitF_closed : ∀ n,
    ∀ (R : Type u) f, n ≤ 2 * f + 1 → 2 ≤ n →
      (circuitF (R := R) f n).gates = mersClosed n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro R f hf hn
      match n with
      | 0 => omega
      | 1 => omega
      | 2 =>
          cases f with
          | zero => omega
          | succ f =>
              ext <;> rfl
      | 3 =>
          cases f with
          | zero => omega
          | succ f =>
              ext <;> rfl
      | kk + 4 =>
          cases f with
          | zero => omega
          | succ f =>
              rw [circuitF_succ_four, gates_outerHead]
              let source : Circuit R ConstructionInput 2 :=
                .fork
                  (.add (powerWire (kk + 3))
                    (reindex (fun j => 6 + j) (circuitF f (kk + 2))))
                  (.add (powerWire (kk + 3)) (parameterWire 5))
              rw [gates_fillPairCircuit (circuitF (R := R) f) (kk + 4) (kk + 2)
                source (by omega) (fun i hi2 hile =>
                  ih i (by omega) R f (by omega) hi2)]
              dsimp only [source]
              rw [gates_recursiveSource,
                ih (kk + 2) (by omega) R f (by omega) (by omega)]
              have hp : 0 < (2 : ℕ) ^ kk := Nat.pow_pos (by omega)
              apply GateCount.ext
              · simp only [mersClosed, add_tsub_cancel_right, Nat.add_one_sub_one,
                  pow_succ, fillPairClosed, GateCount.add_additions,
                  GateCount.of_additions, GateCount.adds_additions, Nat.reduceSubDiff]
                omega
              · simp only [mersClosed, add_tsub_cancel_right, Nat.add_one_sub_one,
                  pow_succ, fillPairClosed, GateCount.add_multiplications,
                  GateCount.of_multiplications, GateCount.adds_multiplications,
                  add_zero, Nat.reduceSubDiff]
                omega

/-- Exact complete gate count of the optimized semantic circuit. -/
theorem gates_circuit {R : Type u} (k : ℕ) (hk : 2 ≤ k) :
    (circuit (R := R) k).gates =
      GateCount.of (5 * 2 ^ (k - 2) - 2) (2 ^ (k - 1) - 1) := by
  exact gates_circuitF_closed k R k (by omega) hk

/-- The optimized circuit has the same Mersenne multiplication count as the uniform
compiler. -/
theorem gates_circuit_multiplications {R : Type u} (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.multiplications = 2 ^ (k - 1) - 1 := by
  rcases eq_or_ne k 1 with rfl | hk1
  · rfl
  · rw [gates_circuit k (by omega)]
    rfl

/-- Direct comparison with the older uniform semantic compiler: the peephole changes
only additions, never the number of nonscalar products. -/
theorem gates_circuit_multiplications_eq_uniform {R : Type u} (k : ℕ) (hk : 1 ≤ k) :
    (circuit (R := R) k).gates.multiplications =
      (mersCircuit (R := R) k).gates.multiplications := by
  rw [gates_circuit_multiplications k hk,
    gates_mersCircuit_multiplications (R := R) k hk]

/-- Exact optimized addition count from the manuscript schedule. -/
theorem gates_circuit_additions {R : Type u} (k : ℕ) (hk : 2 ≤ k) :
    (circuit (R := R) k).gates.additions = 5 * 2 ^ (k - 2) - 2 := by
  rw [gates_circuit k hk]
  rfl

end FastPoly.Cost.MersennePeephole
