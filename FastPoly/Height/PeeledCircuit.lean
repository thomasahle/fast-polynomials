import FastPoly.Height.Depth
import FastPoly.Section4.Peeled
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Circuit, ledger, and height of the peeled gadget

The peeled known-powers gadget as a `Cost.Circuit`, with input labels
`Sum.inl i` for the power `H_{2^i}` (`i = 0` is `x`) and `Sum.inr t` for the
parameter `α t`.  Four exact statements (`lem:peeled-Q-count` of the paper):

* `peelC_multiplications` : exactly `2^(k-1) - 1` products (`k ≥ 1`);
* `peelC_additions`       : exactly `5·2^(k-2) - 2` additions (`k ≥ 2`)
  — the ledger `lem:fill-Q-count`;
* `peelC_eval`            : the circuit computes the `peel` family of
  `FastPoly.Section4.Peeled` (whose decoder is `peel_correct`);
* `peelC_multDepth`       : height exactly `k` (`k ≥ 2`) when the power wires
  sit at depth `i` and the parameter wires at depth `0`.

This file is a standalone paper-witness: the realization lanes consume the
`ConstructionInput` compiler (`Cost/PeeledCircuit.lean`) instead, but only this
file certifies the *exact* height `= k` of `lem:peeled-Q-count` (the master
ledger proves `≤`).
-/

namespace FastPoly.Height

open FastPoly.Cost Polynomial

variable {R : Type*} [CommRing R]

/-- The peeled gadget circuit at level `k`, reading its parameters from offset
`off`.  `Sum.inl i` is the power wire `H_{2^i}` (`i = 0` is `x`), `Sum.inr t`
the parameter wire `α t`. -/
def peelC (k off : ℕ) : Circuit R (ℕ ⊕ ℕ) 1 :=
  match k with
  | 0 => .add (Circuit.input (.inl 0)) (Circuit.input (.inr off))
  | 1 => .add (Circuit.input (.inl 0)) (Circuit.input (.inr off))
  | 2 =>
      .add (.mul (.add (Circuit.input (.inl 0)) (Circuit.input (.inr (off + 2))))
                 (.add (Circuit.input (.inl 1)) (Circuit.input (.inr (off + 1)))))
           (Circuit.input (.inr off))
  | (kk + 3) =>
      .add (.mul (.add (Circuit.input (.inl (kk + 2))) (Circuit.input (.inr off)))
                 (peelC (kk + 2) (off + 1)))
           (peelC (kk + 2) (off + 2 ^ (kk + 2)))

omit [CommRing R] in
private theorem peelC_gates_step (kk off : ℕ) :
    (peelC (R := R) (kk + 3) off).gates
      = ((0 + 0 + GateCount.adds 1) + (peelC (R := R) (kk + 2) (off + 1)).gates
          + GateCount.muls 1)
        + (peelC (R := R) (kk + 2) (off + 2 ^ (kk + 2))).gates
        + GateCount.adds 1 := rfl

omit [CommRing R] in
/-- Exact multiplication count: `2^(k-1) - 1` (the ledger of `lem:fill-Q-count`). -/
theorem peelC_multiplications :
    ∀ k, 1 ≤ k → ∀ off : ℕ,
      (peelC (R := R) k off).gates.multiplications = 2 ^ (k - 1) - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk off
    match k with
    | 1 => rfl
    | 2 => rfl
    | (kk + 3) =>
      have h1 := ih (kk + 2) (by omega) (by omega) (off + 1)
      have h2 := ih (kk + 2) (by omega) (by omega) (off + 2 ^ (kk + 2))
      rw [peelC_gates_step]
      rw [show kk + 2 - 1 = kk + 1 from rfl] at h1 h2
      simp only [GateCount.add_multiplications, GateCount.adds_multiplications,
        GateCount.muls_multiplications, GateCount.zero_multiplications, h1, h2,
        show kk + 3 - 1 = kk + 2 from rfl]
      have hp : (1:ℕ) ≤ 2 ^ (kk + 1) := Nat.one_le_pow _ _ (by omega)
      have hd : (2:ℕ) ^ (kk + 2) = 2 ^ (kk + 1) + 2 ^ (kk + 1) := by ring
      omega

omit [CommRing R] in
/-- Exact addition count: `5·2^(k-2) - 2` (the ledger of `lem:fill-Q-count`). -/
theorem peelC_additions :
    ∀ k, 2 ≤ k → ∀ off : ℕ,
      (peelC (R := R) k off).gates.additions = 5 * 2 ^ (k - 2) - 2 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk off
    match k with
    | 2 => rfl
    | (kk + 3) =>
      have h1 := ih (kk + 2) (by omega) (by omega) (off + 1)
      have h2 := ih (kk + 2) (by omega) (by omega) (off + 2 ^ (kk + 2))
      rw [peelC_gates_step]
      rw [show kk + 2 - 2 = kk from rfl] at h1 h2
      simp only [GateCount.add_additions, GateCount.adds_additions,
        GateCount.muls_additions, GateCount.zero_additions, h1, h2,
        show kk + 3 - 2 = kk + 1 from rfl]
      have hp : (2:ℕ) ≤ 5 * 2 ^ kk := by
        have : (1:ℕ) ≤ 2 ^ kk := Nat.one_le_pow _ _ (by omega)
        omega
      have hd : (5:ℕ) * 2 ^ (kk + 1) = 5 * 2 ^ kk + 5 * 2 ^ kk := by ring
      omega

/-- The circuit computes the `peel` family: with the power wires holding `Hp`
(and `Hp 0 = x`) and the parameter wires holding `C ∘ α`, output `0` is
`Q_{2^k-1}` on the parameter block starting at `off`. -/
theorem peelC_eval {A : Type*} [CommRing A] [Algebra R A]
    (Hp : ℕ → A[X]) (α : ℕ → A) (env : ℕ ⊕ ℕ → A[X])
    (henv1 : ∀ i, env (.inl i) = Hp i)
    (henv2 : ∀ t, env (.inr t) = C (α t))
    (h0 : Hp 0 = X) :
    ∀ k off, (peelC (R := R) k off).eval env 0
      = peel Hp k (fun t => α (off + t)) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro off
    match k with
    | 0 =>
      show env (.inl 0) + env (.inr off) = X + C (α (off + 0))
      rw [henv1, henv2, h0]
      rfl
    | 1 =>
      show env (.inl 0) + env (.inr off) = X + C (α (off + 0))
      rw [henv1, henv2, h0]
      rfl
    | 2 =>
      show (env (.inl 0) + env (.inr (off + 2))) * (env (.inl 1) + env (.inr (off + 1)))
          + env (.inr off)
          = (X + C (α (off + 2))) * (Hp 1 + C (α (off + 1))) + C (α (off + 0))
      rw [henv1, henv1, henv2, henv2, henv2, h0]
      rfl
    | (kk + 3) =>
      have h1 := ih (kk + 2) (by omega) (off + 1)
      have h2 := ih (kk + 2) (by omega) (off + 2 ^ (kk + 2))
      show (env (.inl (kk + 2)) + env (.inr off))
            * (peelC (R := R) (kk + 2) (off + 1)).eval env 0
          + (peelC (R := R) (kk + 2) (off + 2 ^ (kk + 2))).eval env 0
          = peel Hp (kk + 3) (fun t => α (off + t))
      rw [henv1, henv2, h1, h2, peel_unfold]
      congr 1
      · congr 1
        exact congrArg _ (funext fun t => congrArg α (by omega))
      · exact congrArg _ (funext fun t => congrArg α (by omega))

omit [CommRing R] in
/-- Height: with the power wires at depth `i` (`x` at `0`) and the parameter
wires at depth `0`, the peeled circuit has multiplicative depth exactly `k`
for `k ≥ 2` (`lem:peeled-Q-count`). -/
theorem peelC_multDepth :
    ∀ k, 2 ≤ k → ∀ off : ℕ,
      (peelC (R := R) k off).multDepth (Sum.elim id fun _ => 0) 0 = k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk off
    match k with
    | 2 => rfl
    | (kk + 3) =>
      have h1 := ih (kk + 2) (by omega) (by omega) (off + 1)
      have h2 := ih (kk + 2) (by omega) (by omega) (off + 2 ^ (kk + 2))
      show max
          (max (max ((Sum.elim id (fun _ => 0) : ℕ ⊕ ℕ → ℕ) (.inl (kk + 2)))
                ((Sum.elim id (fun _ => 0) : ℕ ⊕ ℕ → ℕ) (.inr off)))
            ((peelC (R := R) (kk + 2) (off + 1)).multDepth (Sum.elim id fun _ => 0) 0)
            + 1)
          ((peelC (R := R) (kk + 2) (off + 2 ^ (kk + 2))).multDepth
            (Sum.elim id fun _ => 0) 0)
          = kk + 3
      rw [h1, h2]
      simp only [Sum.elim_inl, Sum.elim_inr, id_eq]
      omega

end FastPoly.Height
