import FastPoly.Cost.MersenneCircuit

/-!
# Multiplication count of the semantic Mersenne circuit

This file counts gates in `mersCircuit` itself.  In particular, the theorem below is
attached to the same circuit whose evaluation is proved correct in
`MersenneCircuit.lean`; it is not a comparison with an independently annotated
schedule.

Only nonscalar multiplications are treated here.  The current uniform level-two fill
compiler uses one more addition than the direct `A₄` peephole used by the optimized
paper schedule, so an equality of their complete `GateCount`s would be false.  Keeping
that distinction explicit prevents the multiplication theorem from silently asserting
an unproved addition count.
-/

namespace FastPoly.Cost

open Circuit

universe u

/-- Multiplications contributed by the descending fill levels `l,l-1,...,2`, excluding
the source pair and the two level-one head products.  Its recursive terms are the gate
counts of the actual recursively compiled Mersenne circuits. -/
private def uniformChainMultiplicationsF {R : Type u} (f : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | i + 2 =>
      (mersCircuitF (R := R) f (i + 1)).gates.multiplications +
        (mersCircuitF (R := R) f (i + 2)).gates.multiplications + 2 +
          uniformChainMultiplicationsF (R := R) f (i + 1)

/-- Multiplications in the uniform fill pair used by `mersCircuitF`, before the final
outer product.  At level two this is `Q₁ + Q₃ + 4`; at every subsequent level it adds
the two recursive Mersenne gadgets and the two products of one fill step. -/
def uniformFillMultiplicationsF {R : Type u} (f : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | 2 =>
      (mersCircuitF (R := R) f 1).gates.multiplications +
        (mersCircuitF (R := R) f 2).gates.multiplications + 4
  | l + 3 =>
      uniformFillMultiplicationsF (R := R) f (l + 2) +
        (mersCircuitF (R := R) f (l + 2)).gates.multiplications +
        (mersCircuitF (R := R) f (l + 3)).gates.multiplications + 2

/-- A fill step charges its source once, each recursively compiled gadget once, and its
two displayed products. -/
private theorem multiplications_mersFillStep {R : Type u} (f k i : ℕ)
    (source : Circuit R ConstructionInput 2) :
    (Circuit.fillStep (Circuit.constructionPower i)
        (mersFillCircuitData f k i) source).gates.multiplications =
      source.gates.multiplications +
        (mersCircuitF (R := R) f (i - 1)).gates.multiplications +
        (mersCircuitF (R := R) f i).gates.multiplications + 2 := by
  rw [Circuit.fillStep, Circuit.gates_bind]
  simp only [Circuit.gates, Circuit.gates_liftLeft,
    Circuit.gates_rightInput,
    gates_mersFillCircuitData_q, gates_mersFillCircuitData_qh,
    gates_mersFillCircuitData_b, gates_mersFillCircuitData_ah,
    Circuit.gates_constructionPower, GateCount.add_multiplications,
    GateCount.zero_multiplications, GateCount.adds_multiplications,
    GateCount.muls_multiplications]
  omega

/-- The multiplication count of a fill chain is the count of its shared source plus the
sum of the multiplication counts of its descending steps. -/
private theorem multiplications_mersFillChain {R : Type u} (f k l : ℕ)
    (source : Circuit R ConstructionInput 2) :
    (Circuit.fillChain (fun i => Circuit.constructionPower i)
        (fun i => mersFillCircuitData f k i) l source).gates.multiplications =
      source.gates.multiplications + uniformChainMultiplicationsF (R := R) f l := by
  induction l generalizing source with
  | zero => rfl
  | succ l ih =>
      rcases l with _ | l
      · rfl
      · change
          (Circuit.fillChain (fun i => Circuit.constructionPower i)
              (fun i => mersFillCircuitData f k i) (l + 1)
              (Circuit.fillStep (Circuit.constructionPower (l + 2))
                (mersFillCircuitData f k (l + 2)) source)).gates.multiplications = _
        rw [ih, multiplications_mersFillStep]
        rw [show l + 2 - 1 = l + 1 by omega]
        simp only [uniformChainMultiplicationsF]
        omega

/-- The specialized final fill head contains exactly three products after its shared
source: two level-one head products and the final outer product. -/
private theorem multiplications_mersFinishFill {R : Type u}
    (source : Circuit R ConstructionInput 2) :
    (Circuit.finishFill Circuit.constructionX (Circuit.constructionPower 1)
        (Circuit.constructionParameter 0) (Circuit.constructionParameter 1)
        (Circuit.constructionParameter 2) (Circuit.constructionParameter 3)
        (Circuit.constructionParameter 4) source).gates.multiplications =
      source.gates.multiplications + 3 := by
  change (source.gates + GateCount.of 6 3).multiplications =
    source.gates.multiplications + 3
  simp only [GateCount.add_multiplications, GateCount.of_multiplications]

/-- The uniform fill-pair count is the descending-chain count plus its two level-one
head products. -/
private theorem uniformFillMultiplicationsF_eq_chain {R : Type u} (f l : ℕ)
    (hl : 2 ≤ l) :
    uniformFillMultiplicationsF (R := R) f l =
      uniformChainMultiplicationsF (R := R) f l + 2 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
      match l with
      | 0 => omega
      | 1 => omega
      | 2 =>
          simp only [uniformFillMultiplicationsF, uniformChainMultiplicationsF]
      | i + 3 =>
          have hprev : 2 ≤ i + 2 := by omega
          have hrec := ih (i + 2) (by omega) hprev
          simp only [uniformFillMultiplicationsF, uniformChainMultiplicationsF]
          rw [hrec]
          rw [show i + 1 + 1 = i + 2 by omega,
            show i + 1 + 2 = i + 3 by omega]
          rw [show uniformChainMultiplicationsF (R := R) f (i + 2) =
              (mersCircuitF (R := R) f (i + 1)).gates.multiplications +
                (mersCircuitF (R := R) f (i + 2)).gates.multiplications + 2 +
                uniformChainMultiplicationsF (R := R) f (i + 1) from rfl]
          omega

/-- Exact multiplication recurrence for the recursive branch of the semantic compiler.
The lower Mersenne gadget is shared by the source pair; the uniform fill pair contributes
the next block, and the last `+1` is the outer product. -/
theorem mersCircuitF_multiplications_step {R : Type u} (f k : ℕ) :
    (mersCircuitF (R := R) (f + 1) (k + 4)).gates.multiplications =
      (mersCircuitF (R := R) f (k + 2)).gates.multiplications +
        uniformFillMultiplicationsF (R := R) f (k + 2) + 1 := by
  rw [mersCircuitF_succ_four]
  dsimp only
  rw [multiplications_mersFinishFill, multiplications_mersFillChain]
  rw [gates_mersRecursiveSource_multiplications]
  have hfill := uniformFillMultiplicationsF_eq_chain (R := R) f (k + 2) (by omega)
  rw [hfill]
  omega

private def mersMultiplicationsClosed (k : ℕ) : ℕ :=
  2 ^ (k - 1) - 1

private def uniformFillMultiplicationsClosed (l : ℕ) : ℕ :=
  2 ^ l + 2 ^ (l - 1) - 1

/-- Simultaneous closed forms for the actual recursive circuit and its uniform fill
pair.  The fuel condition `n ≤ 2*f+1` is sharp for this compiler: the recursive branch
decreases the degree index by two and the fuel by one, while the degree-two and
degree-three bases require positive fuel. -/
private theorem uniform_fill_mers_multiplications_closed : ∀ n,
    (∀ (R : Type u) f, n ≤ 2 * f + 1 → 2 ≤ n →
      (mersCircuitF (R := R) f n).gates.multiplications =
        mersMultiplicationsClosed n) ∧
    (∀ (R : Type u) f, n ≤ 2 * f + 1 → 2 ≤ n →
      uniformFillMultiplicationsF (R := R) f n =
        uniformFillMultiplicationsClosed n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          constructor <;> intro R f hf hn <;> omega
      | 1 =>
          constructor <;> intro R f hf hn <;> omega
      | 2 =>
          constructor
          · intro R f hf hn
            cases f with
            | zero => omega
            | succ f =>
                rw [gates_mersCircuitF_two_multiplications]
                simp [mersMultiplicationsClosed]
          · intro R f hf hn
            cases f with
            | zero => omega
            | succ f =>
                simp only [uniformFillMultiplicationsF,
                  gates_mersCircuitF_one_multiplications,
                  gates_mersCircuitF_two_multiplications]
                simp [uniformFillMultiplicationsClosed]
      | 3 =>
          constructor
          · intro R f hf hn
            cases f with
            | zero => omega
            | succ f =>
                rw [gates_mersCircuitF_three_multiplications]
                simp [mersMultiplicationsClosed]
          · intro R f hf hn
            cases f with
            | zero => omega
            | succ f =>
                simp only [uniformFillMultiplicationsF,
                  gates_mersCircuitF_one_multiplications,
                  gates_mersCircuitF_two_multiplications]
                simp [uniformFillMultiplicationsClosed]
      | k + 4 =>
          let qNow : ∀ (R : Type u) f, k + 4 ≤ 2 * f + 1 →
              (mersCircuitF (R := R) f (k + 4)).gates.multiplications =
                mersMultiplicationsClosed (k + 4) := by
            intro R f hf
            cases f with
            | zero => omega
            | succ g =>
                rw [mersCircuitF_multiplications_step]
                have hq := (ih (k + 2) (by omega)).1 R g (by omega) (by omega)
                have hfill := (ih (k + 2) (by omega)).2 R g (by omega) (by omega)
                rw [hq, hfill]
                have hp : 0 < (2 : ℕ) ^ k := by positivity
                simp [mersMultiplicationsClosed, uniformFillMultiplicationsClosed,
                  pow_succ]
                omega
          refine ⟨?_, ?_⟩
          · intro R f hf hn
            exact qNow R f hf
          · intro R f hf hn
            rw [uniformFillMultiplicationsF]
            have hprevFill := (ih (k + 3) (by omega)).2 R f (by omega) (by omega)
            have hprevQ := (ih (k + 3) (by omega)).1 R f (by omega) (by omega)
            have hqNow := qNow R f hf
            rw [hprevFill, hprevQ, hqNow]
            have hp : 0 < (2 : ℕ) ^ k := by positivity
            simp [mersMultiplicationsClosed, uniformFillMultiplicationsClosed,
              pow_succ]
            omega

/-- Exact nonscalar-multiplication count of the actual semantic Mersenne circuit.
This is the circuit-level counterpart of the paper's `Q_{2^k-1}` count. -/
theorem gates_mersCircuit_multiplications {R : Type u} (k : ℕ) (hk : 1 ≤ k) :
    (mersCircuit (R := R) k).gates.multiplications = 2 ^ (k - 1) - 1 := by
  rcases eq_or_ne k 1 with rfl | hk1
  · rfl
  · exact (uniform_fill_mers_multiplications_closed k).1 R k (by omega) (by omega)

end FastPoly.Cost
