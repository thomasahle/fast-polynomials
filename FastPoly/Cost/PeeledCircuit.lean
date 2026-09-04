import FastPoly.Cost.ConstructionInput
import FastPoly.Section4.Peeled

/-!
# Semantic compiler for the peeled known-powers gadget

`peelCircuitF` mirrors `FastPoly.peelF` branch for branch over the shared
`ConstructionInput` wiring: bases `k ≤ 2` are identical to the Mersenne
compiler's, and the single recursive branch is the two-child peel

  `(H_{2^{k-1}} + γ) · W + B`

with the children reindexed to the parameter blocks `1+j` and `2^{k-1}+j`.
No fill chain, no per-level data, no fork source.  The exact ledger is
`GateCount.of (5·2^{k-2} - 2) (2^{k-1} - 1)` — the counts of
`lem:fill-Q-count`, attached here to a decodable family (`peel_correct`)
within a single circuit.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

private abbrev px {R : Type u} : Circuit R ConstructionInput 1 :=
  Circuit.constructionX

private abbrev ph {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionPower i

private abbrev pa {R : Type u} (i : ℕ) : Circuit R ConstructionInput 1 :=
  Circuit.constructionParameter i

private abbrev preindex {R : Type u} (f : ℕ → ℕ)
    (c : Circuit R ConstructionInput 1) : Circuit R ConstructionInput 1 :=
  c.reindexConstructionParameters f

/-- Fuel-indexed circuit matching `FastPoly.peelF`. -/
def peelCircuitF {R : Type u} : ℕ → ℕ → Circuit R ConstructionInput 1
  | 0, _ => .add px (pa 0)
  | f + 1, k =>
      match k with
      | 0 => .add px (pa 0)
      | 1 => .add px (pa 0)
      | 2 => .add (.mul (.add px (pa 2)) (.add (ph 1) (pa 1))) (pa 0)
      | 3 =>
          .add
            (.mul (.add (ph 2) (pa 0))
              (.add (.mul (.add px (pa 3)) (.add (ph 1) (pa 2))) (pa 1)))
            (.add (.mul (.add px (pa 6)) (.add (ph 1) (pa 5))) (pa 4))
      | kk + 4 =>
          .add
            (.mul (.add (ph (kk + 3)) (pa 0))
              (preindex (fun j => 1 + j) (peelCircuitF f (kk + 3))))
            (preindex (fun j => 2 ^ (kk + 3) + j) (peelCircuitF f (kk + 3)))

/-- The peeled known-powers circuit. -/
def peelCircuit {R : Type u} (k : ℕ) : Circuit R ConstructionInput 1 :=
  peelCircuitF k k

private theorem peelCircuitF_succ_step {R : Type u} (f kk : ℕ) :
    peelCircuitF (R := R) (f + 1) (kk + 4)
      = .add
          (.mul (.add (ph (kk + 3)) (pa 0))
            (preindex (fun j => 1 + j) (peelCircuitF f (kk + 3))))
          (preindex (fun j => 2 ^ (kk + 3) + j) (peelCircuitF f (kk + 3))) := rfl

section counts

variable {R : Type u}

private theorem gates_peelCircuitF_closed :
    ∀ f k, 2 ≤ k → k ≤ f + 1 →
      (peelCircuitF (R := R) f k).gates
        = GateCount.of (5 * 2 ^ (k - 2) - 2) (2 ^ (k - 1) - 1) := by
  intro f
  induction f with
  | zero =>
    intro k hk2 hkf
    omega
  | succ f ih =>
    intro k hk2 hkf
    match k with
    | 2 => rfl
    | 3 => rfl
    | kk + 4 =>
      have h1 := ih (kk + 3) (by omega) (by omega)
      have hexp : (peelCircuitF (R := R) (f + 1) (kk + 4)).gates
          = ((0 + 0 + GateCount.adds 1)
              + (peelCircuitF (R := R) f (kk + 3)).gates + GateCount.muls 1)
            + (peelCircuitF (R := R) f (kk + 3)).gates + GateCount.adds 1 := by
        rw [peelCircuitF_succ_step]
        simp [Circuit.gates, preindex,
          Circuit.gates_reindexConstructionParameters]
      rw [hexp, h1]
      have h1p : (1:ℕ) ≤ 2 ^ (kk + 1) := Nat.one_le_pow _ _ (by omega)
      have h2p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
      refine GateCount.ext ?_ ?_
      · simp only [GateCount.add_additions, GateCount.adds_additions,
          GateCount.muls_additions, GateCount.zero_additions,
          GateCount.of_additions,
          show kk + 3 - 2 = kk + 1 from rfl, show kk + 4 - 2 = kk + 2 from rfl]
        have : (5:ℕ) * 2 ^ (kk + 2) = 5 * 2 ^ (kk + 1) + 5 * 2 ^ (kk + 1) := by ring
        omega
      · simp only [GateCount.add_multiplications, GateCount.adds_multiplications,
          GateCount.muls_multiplications, GateCount.zero_multiplications,
          GateCount.of_multiplications,
          show kk + 3 - 1 = kk + 2 from rfl, show kk + 4 - 1 = kk + 3 from rfl]
        have : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
        omega

/-- **Exact complete gate count** of the peeled circuit: the fill ledger
`lem:fill-Q-count` attached to a decodable family. -/
theorem gates_peelCircuit {R : Type u} (k : ℕ) (hk : 2 ≤ k) :
    (peelCircuit (R := R) k).gates
      = GateCount.of (5 * 2 ^ (k - 2) - 2) (2 ^ (k - 1) - 1) :=
  gates_peelCircuitF_closed k k hk (by omega)

/-- Multiplication count alone, in the interface shape of
`gates_mersCircuit_multiplications`. -/
theorem gates_peelCircuit_multiplications {R : Type u} (k : ℕ) (hk : 1 ≤ k) :
    (peelCircuit (R := R) k).gates.multiplications = 2 ^ (k - 1) - 1 := by
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · match k, hk, hk1 with
    | 1, _, _ => rfl
  · rw [gates_peelCircuit k hk2]
    rfl

end counts

section semantics

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- The circuit compiler reflects the peeled family exactly. -/
theorem eval_peelCircuitF (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) :
    ∀ f k,
      (peelCircuitF (R := R) f k).eval
          (constructionEnv powers shifted parameters source) 0 =
        FastPoly.peelF powers f k parameters := by
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
            · show ((Circuit.add
                  (.mul (.add (ph (kk + 3)) (pa 0))
                    (preindex (fun j => 1 + j) (peelCircuitF f (kk + 3))))
                  (preindex (fun j => 2 ^ (kk + 3) + j)
                    (peelCircuitF f (kk + 3)))) : Circuit R ConstructionInput 1).eval
                    (constructionEnv powers shifted parameters source) 0
                = FastPoly.peelF powers (f + 1) (kk + 4) parameters
              simp only [Circuit.eval_add, Circuit.eval_mul, preindex,
                Circuit.eval_reindexConstructionParameters, Function.comp_def]
              rw [ih ((fun j => parameters (1 + j))) (kk + 3),
                ih ((fun j => parameters (2 ^ (kk + 3) + j))) (kk + 3)]
              rfl

@[simp] theorem eval_peelCircuit (powers : ℕ → A[X]) (shifted : A[X])
    (parameters : ℕ → A) (source : Fin 2 → A[X]) (k : ℕ) :
    (peelCircuit (R := R) k).eval
        (constructionEnv powers shifted parameters source) 0 =
      FastPoly.peel powers k parameters :=
  eval_peelCircuitF powers shifted parameters source k k

end semantics

end FastPoly.Cost
