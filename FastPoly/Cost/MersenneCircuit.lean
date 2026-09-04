import FastPoly.Cost.ConstructionInput
import FastPoly.Cost.FillCircuitPolynomial
import FastPoly.Section4.KnownPowers

/-!
# Semantic compiler for the known-powers (Mersenne) construction

`mersCircuitF` mirrors `FastPoly.mersF` branch for branch. Its inputs are only symbolic
wires for `x`, the known power tower, and the fresh parameter block. The recursive fill
pair is explicitly bound before both components are consumed by the final head.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

private abbrev mx {R : Type u} : Circuit R ConstructionInput 1 :=
  Circuit.constructionX

private abbrev mh {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionPower i

private abbrev ma {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionParameter i

private abbrev reindex {R : Type u} (f : ℕ → ℕ) (c : Circuit R ConstructionInput 1) :
    Circuit R ConstructionInput 1 :=
  c.reindexConstructionParameters f

/-- Fuel-indexed circuit matching `FastPoly.mersF`. -/
def mersCircuitF {R : Type u} : ℕ → ℕ → Circuit R ConstructionInput 1
  | 0, _ => .add mx (ma 0)
  | f + 1, k =>
      match k with
      | 0 => .add mx (ma 0)
      | 1 => .add mx (ma 0)
      | 2 => .add (.mul (.add mx (ma 2)) (.add (mh 1) (ma 1))) (ma 0)
      | 3 =>
          .add
            (.mul (.add mx (ma 0))
              (.add (.mul (.add (mh 1) (ma 1)) (.add (mh 2) (ma 5))) (ma 4)))
            (.add (.mul (.add (mh 1) (ma 2)) (.add (mh 2) (ma 6))) (ma 3))
      | kk + 4 =>
          let source : Circuit R ConstructionInput 2 :=
            .fork
              (.add (mh (kk + 3))
                (reindex (fun j => 6 + j) (mersCircuitF f (kk + 2))))
              (.add (mh (kk + 3)) (ma 5))
          let data : ℕ → FillCircuitData R ConstructionInput := fun i =>
            { q := reindex (fun j => FastPoly.doff (kk + 4) i + 2 + j)
                (mersCircuitF f (i - 1))
              qh := reindex
                (fun j => FastPoly.doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)
                (mersCircuitF f i)
              b := ma (FastPoly.doff (kk + 4) i)
              ah := ma (FastPoly.doff (kk + 4) i + 1) }
          let chain := Circuit.fillChain (fun i => mh i) data (kk + 2) source
          Circuit.finishFill mx (mh 1) (ma 0) (ma 1) (ma 2) (ma 3) (ma 4) chain

/-- The optimized known-powers circuit. -/
def mersCircuit {R : Type u} (k : ℕ) : Circuit R ConstructionInput 1 :=
  mersCircuitF k k

/-- Circuit data at one recursive fill level. Exposed as a named definition so semantic
and cost proofs do not repeatedly unfold the large `mersCircuitF` branch. -/
def mersFillCircuitData {R : Type u} (f k i : ℕ) :
    FillCircuitData R ConstructionInput :=
  { q := reindex (fun j => FastPoly.doff k i + 2 + j) (mersCircuitF f (i - 1))
    qh := reindex (fun j => FastPoly.doff k i + 2 + (2 ^ (i - 1) - 1) + j)
      (mersCircuitF f i)
    b := ma (FastPoly.doff k i)
    ah := ma (FastPoly.doff k i + 1) }

/-! The following four equations are the cost-facing interface of one fill datum.
They hide the local parameter relabeling, which preserves syntax exactly. -/

@[simp] theorem gates_mersFillCircuitData_q {R : Type u} (f k i : ℕ) :
    (mersFillCircuitData (R := R) f k i).q.gates =
      (mersCircuitF (R := R) f (i - 1)).gates := by
  change (reindex (fun j ↦ FastPoly.doff k i + 2 + j)
    (mersCircuitF f (i - 1))).gates = _
  rw [reindex, Circuit.gates_reindexConstructionParameters]

@[simp] theorem gates_mersFillCircuitData_qh {R : Type u} (f k i : ℕ) :
    (mersFillCircuitData (R := R) f k i).qh.gates =
      (mersCircuitF (R := R) f i).gates := by
  change (reindex
    (fun j ↦ FastPoly.doff k i + 2 + (2 ^ (i - 1) - 1) + j)
    (mersCircuitF f i)).gates = _
  rw [reindex, Circuit.gates_reindexConstructionParameters]

@[simp] theorem gates_mersFillCircuitData_b {R : Type u} (f k i : ℕ) :
    (mersFillCircuitData (R := R) f k i).b.gates = 0 := by
  rfl

@[simp] theorem gates_mersFillCircuitData_ah {R : Type u} (f k i : ℕ) :
    (mersFillCircuitData (R := R) f k i).ah.gates = 0 := by
  rfl

/-- Named branch equation for recursive calls. -/
theorem mersCircuitF_succ_four {R : Type u} (f kk : ℕ) :
    mersCircuitF (R := R) (f + 1) (kk + 4) =
      let source : Circuit R ConstructionInput 2 :=
        .fork
          (.add (mh (kk + 3))
            (reindex (fun j => 6 + j) (mersCircuitF f (kk + 2))))
          (.add (mh (kk + 3)) (ma 5))
      let chain := Circuit.fillChain (fun i => mh i)
        (fun i => mersFillCircuitData f (kk + 4) i) (kk + 2) source
      Circuit.finishFill mx (mh 1) (ma 0) (ma 1) (ma 2) (ma 3) (ma 4) chain :=
  rfl

/-! Small and recursive multiplication equations for the actual circuit syntax.  They
are deliberately stated here, where the local wire abbreviations are transparent; the
closed-form arithmetic lives in `MersenneCircuitCount.lean`. -/

@[simp] theorem gates_mersCircuitF_zero_multiplications {R : Type u} (f : ℕ) :
    (mersCircuitF (R := R) f 0).gates.multiplications = 0 := by
  cases f <;> rfl

@[simp] theorem gates_mersCircuitF_one_multiplications {R : Type u} (f : ℕ) :
    (mersCircuitF (R := R) f 1).gates.multiplications = 0 := by
  cases f <;> rfl

@[simp] theorem gates_mersCircuitF_two_multiplications {R : Type u} (f : ℕ) :
    (mersCircuitF (R := R) (f + 1) 2).gates.multiplications = 1 := by
  rfl

@[simp] theorem gates_mersCircuitF_three_multiplications {R : Type u} (f : ℕ) :
    (mersCircuitF (R := R) (f + 1) 3).gates.multiplications = 3 := by
  rfl

/-- The source pair of a recursive Mersenne branch shares its lower recursive gadget
and therefore has exactly that gadget's multiplication count. -/
theorem gates_mersRecursiveSource_multiplications {R : Type u} (f kk : ℕ) :
    (.fork
        (.add (mh (kk + 3))
          (reindex (fun j ↦ 6 + j) (mersCircuitF f (kk + 2))))
        (.add (mh (kk + 3)) (ma 5)) : Circuit R ConstructionInput 2).gates.multiplications =
      (mersCircuitF (R := R) f (kk + 2)).gates.multiplications := by
  simp only [Circuit.gates, GateCount.add_multiplications,
    GateCount.zero_multiplications, GateCount.adds_multiplications,
    Circuit.gates_constructionPower, Circuit.gates_constructionParameter,
    reindex, Circuit.gates_reindexConstructionParameters]
  omega

section semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

private noncomputable def menv (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) : ConstructionInput → A[X] :=
  constructionEnv powers shifted parameters source

/-- Polynomial-side branch equation matching `mersCircuitF_succ_four`. Keeping this
equation named prevents the semantic proof from repeatedly unfolding the full recursive
definition. -/
private theorem mersF_succ_four_semantics (powers : ℕ → A[X])
    (parameters : ℕ → A) (f kk : ℕ) :
    FastPoly.mersF powers (f + 1) (kk + 4) parameters =
      let source : A[X] × A[X] :=
        (powers (kk + 3) + FastPoly.mersF powers f (kk + 2)
            (fun j => parameters (6 + j)),
          powers (kk + 3) + C (parameters 5))
      let data := FastPoly.mersD powers (FastPoly.mersF powers f)
        (kk + 4) parameters
      (X + C (parameters 0)) *
          ((powers 1 + C (parameters 1)) *
              (FastPoly.fillChain powers data (kk + 2) source).1 + C (parameters 4)) +
        ((powers 1 + C (parameters 2)) *
              (FastPoly.fillChain powers data (kk + 2) source).2 + C (parameters 3)) :=
  rfl

/-- The circuit compiler reflects the paper definition exactly. -/
theorem eval_mersCircuitF (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    ∀ f k,
      (mersCircuitF (R := R) f k).eval (menv powers shifted parameters source) 0 =
        FastPoly.mersF powers f k parameters := by
  intro f
  induction f generalizing powers shifted parameters source with
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
            · rw [mersCircuitF_succ_four]
              rw [mersF_succ_four_semantics]
              simp only [Circuit.eval_finishFill]
              have hchain := Circuit.eval_fillChain
                (fun i => mh i)
                (fun i => mersFillCircuitData (R := R) f (kk + 4) i)
                (menv powers shifted parameters source) (kk + 2)
                (.fork
                  (.add (mh (kk + 3))
                    (reindex (fun j => 6 + j) (mersCircuitF f (kk + 2))))
                  (.add (mh (kk + 3)) (ma 5)))
              have hchain₀ := congrArg Prod.fst hchain
              have hchain₁ := congrArg Prod.snd hchain
              dsimp only at hchain₀ hchain₁
              rw [hchain₀, hchain₁]
              have hpower :
                  (fun i => (mh (R := R) i).eval
                    (menv powers shifted parameters source) 0) = powers := by
                funext i
                rfl
              let sourceCircuit : Circuit R ConstructionInput 2 :=
                .fork
                  (.add (mh (kk + 3))
                    (reindex (fun j => 6 + j) (mersCircuitF f (kk + 2))))
                  (.add (mh (kk + 3)) (ma 5))
              have hsource :
                  (sourceCircuit.eval (menv powers shifted parameters source) 0,
                    sourceCircuit.eval (menv powers shifted parameters source) 1) =
                    (powers (kk + 3) + FastPoly.mersF powers f (kk + 2)
                        (fun j => parameters (6 + j)),
                      powers (kk + 3) + C (parameters 5)) := by
                apply Prod.ext
                · change
                    powers (kk + 3) +
                        (reindex (fun j => 6 + j) (mersCircuitF f (kk + 2))).eval
                          (menv powers shifted parameters source) 0 = _
                  rw [menv, reindex, Circuit.eval_reindexConstructionParameters]
                  change powers (kk + 3) +
                      (mersCircuitF f (kk + 2)).eval
                        (menv powers shifted (parameters ∘ fun j => 6 + j) source) 0 = _
                  rw [ih]
                  rfl
                · rfl
              dsimp only [sourceCircuit] at hsource
              -- Identify every recursively compiled fill datum with `mersD`.
              have hdata : ∀ i,
                  (mersFillCircuitData (R := R) f (kk + 4) i).eval
                      (menv powers shifted parameters source) =
                    FillValues.ofPolynomialData
                      (FastPoly.mersD powers (FastPoly.mersF powers f)
                        (kk + 4) parameters i) := by
                intro i
                apply FillValues.ext
                · change
                    (reindex (fun j => FastPoly.doff (kk + 4) i + 2 + j)
                        (mersCircuitF f (i - 1))).eval
                          (menv powers shifted parameters source) 0 =
                      FastPoly.mersF powers f (i - 1)
                        (fun j => parameters (FastPoly.doff (kk + 4) i + 2 + j))
                  rw [menv, reindex, Circuit.eval_reindexConstructionParameters]
                  change
                    (mersCircuitF f (i - 1)).eval
                        (menv powers shifted (parameters ∘
                          fun j => FastPoly.doff (kk + 4) i + 2 + j) source) 0 = _
                  rw [ih]
                  rfl
                · change
                    (reindex
                          (fun j => FastPoly.doff (kk + 4) i + 2 +
                          (2 ^ (i - 1) - 1) + j)
                        (mersCircuitF f i)).eval
                          (menv powers shifted parameters source) 0 =
                      FastPoly.mersF powers f i
                        (fun j => parameters (FastPoly.doff (kk + 4) i + 2 +
                          (2 ^ (i - 1) - 1) + j))
                  rw [menv, reindex, Circuit.eval_reindexConstructionParameters]
                  change
                    (mersCircuitF f i).eval
                        (menv powers shifted (parameters ∘
                          fun j => FastPoly.doff (kk + 4) i + 2 +
                            (2 ^ (i - 1) - 1) + j) source) 0 = _
                  rw [ih]
                  rfl
                · rfl
                · rfl
              rw [show (fun i => (mersFillCircuitData (R := R) f (kk + 4) i).eval
                    (menv powers shifted parameters source)) =
                    fun i => FillValues.ofPolynomialData
                      (FastPoly.mersD powers (FastPoly.mersF powers f)
                        (kk + 4) parameters i) from funext hdata]
              rw [hpower, hsource]
              rw [fillChainValue_ofPolynomialData]
              simp only [mx, mh, ma, menv, Circuit.eval_constructionX,
                Circuit.eval_constructionPower, Circuit.eval_constructionParameter]

@[simp] theorem eval_mersCircuit (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) (k : ℕ) :
    (mersCircuit (R := R) k).eval (menv powers shifted parameters source) 0 =
      FastPoly.mers powers k parameters :=
  eval_mersCircuitF powers shifted parameters source k k

end semantics

end FastPoly.Cost
