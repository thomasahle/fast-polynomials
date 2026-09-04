import FastPoly.Cost.Model
import FastPoly.Section5.T

/-!
# Exact gate counts for the fill, Mersenne, and `T` schedules

The first mutually fuelled schedule is the optimized paper schedule for the fill and
known-powers gadgets. Its well-founded order is the one used in the LaTeX proof:

* `Q_r` first uses `Q_{r-2}` and the already constructed level-`r-2` fill;
* the level-`r` fill then uses the level-`r-1` fill, `Q_{r-1}`, and the just constructed
  `Q_r`.

The `T` schedule below mirrors the four branches of `TF`. It records multiplication gates
only, since this is the cost used by the main theorem.
-/

namespace FastPoly.Cost

open Program

private def seq4 (p₁ p₂ p₃ p₄ : Program Unit) : Program Unit :=
  thenSchedule p₁ (thenSchedule p₂ (thenSchedule p₃ p₄))

private def seq5 (p₁ p₂ p₃ p₄ p₅ : Program Unit) : Program Unit :=
  thenSchedule p₁ (seq4 p₂ p₃ p₄ p₅)

mutual
  /-- Fuelled optimized schedule for `Q_{2^k-1}`. Direct bases are available at every
  fuel; fuel zero marks an unavailable non-base recursive call. -/
  def mersScheduleF : ℕ → ℕ → Program Unit
    | _, 0 => schedule (GateCount.of 1 0)
    | _, 1 => schedule (GateCount.of 1 0)
    | _, 2 => schedule (GateCount.of 3 1)
    | _, 3 => schedule (GateCount.of 8 3)
    | 0, _ + 4 => pure ()
    | f + 1, k + 4 =>
        seq4 (mersScheduleF f (k + 2))
          (fillPairScheduleF f (k + 2))
          (schedule (GateCount.adds 4))
          (schedule (GateCount.muls 1))

  /-- Fuelled optimized schedule for `(A¹_{2^l},A²_{2^l})`, before the final
  `(x+β₀)A¹+A²` gate. -/
  def fillPairScheduleF : ℕ → ℕ → Program Unit
    | _, 0 => pure ()
    | _, 1 => schedule (GateCount.of 4 2)
    | _, 2 => schedule (GateCount.of 11 5)
    | 0, _ + 3 => pure ()
    | f + 1, l + 3 =>
        seq4 (fillPairScheduleF f (l + 2))
          (mersScheduleF f (l + 2))
          (mersScheduleF f (l + 3))
          (schedule (GateCount.of 4 2))
end

/-- The optimized paper schedule for `Q_{2^k-1}`. -/
def mersSchedule (k : ℕ) : Program Unit := mersScheduleF k k

/-- The optimized paper schedule for `(A¹_{2^l},A²_{2^l})`. -/
def fillPairSchedule (l : ℕ) : Program Unit := fillPairScheduleF l l

/-- The optimized paper schedule for `A_{2^l}=(x+β₀)A¹_{2^l}+A²_{2^l}`. -/
def fillSchedule (l : ℕ) : Program Unit :=
  thenSchedule (fillPairSchedule l) (schedule (GateCount.of 2 1))

theorem mersScheduleF_step (f k : ℕ) :
    mersScheduleF (f + 1) (k + 4) =
      seq4 (mersScheduleF f (k + 2)) (fillPairScheduleF f (k + 2))
        (schedule (GateCount.adds 4)) (schedule (GateCount.muls 1)) := rfl

theorem fillPairScheduleF_step (f l : ℕ) :
    fillPairScheduleF (f + 1) (l + 3) =
      seq4 (fillPairScheduleF f (l + 2)) (mersScheduleF f (l + 2))
        (mersScheduleF f (l + 3)) (schedule (GateCount.of 4 2)) := rfl

private def mersClosed (k : ℕ) : GateCount :=
  GateCount.of (5 * 2 ^ (k - 2) - 2) (2 ^ (k - 1) - 1)

private def fillPairClosed (l : ℕ) : GateCount :=
  GateCount.of (5 * (2 ^ (l - 1) + 2 ^ (l - 2)) - 4)
    (2 ^ l + 2 ^ (l - 1) - 1)

/-- Simultaneous closed forms. The asymmetric fuel bounds are exact: `Q_k` needs `k-3`
recursive rounds, while the level-`l` fill needs `l-2`. -/
private theorem fill_mers_closed_fuel : ∀ n,
    (∀ f, n ≤ f + 3 → 2 ≤ n → (mersScheduleF f n).gates = mersClosed n) ∧
    (∀ f, n ≤ f + 2 → 2 ≤ n → (fillPairScheduleF f n).gates = fillPairClosed n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      match n with
      | 0 =>
          constructor <;> intro f hf hn <;> omega
      | 1 =>
          constructor <;> intro f hf hn <;> omega
      | 2 =>
          constructor
          · intro f hf hn
            simp [mersScheduleF, mersClosed, GateCount.of]
          · intro f hf hn
            simp [fillPairScheduleF, fillPairClosed, GateCount.of]
      | 3 =>
          constructor
          · intro f hf hn
            simp [mersScheduleF, mersClosed, GateCount.of]
          · intro f hf hn
            cases f with
            | zero => omega
            | succ g =>
                rw [show fillPairScheduleF (g + 1) 3 =
                    seq4 (fillPairScheduleF g 2) (mersScheduleF g 2)
                      (mersScheduleF g 3) (schedule (GateCount.of 4 2)) from rfl]
                have hf2 := (ih 2 (by omega)).2 g (by omega) (by omega)
                have hq2 := (ih 2 (by omega)).1 g (by omega) (by omega)
                have hq3 : (mersScheduleF g 3).gates = mersClosed 3 := by
                  simp [mersScheduleF, mersClosed, GateCount.of]
                rw [show (seq4 (fillPairScheduleF g 2) (mersScheduleF g 2)
                    (mersScheduleF g 3) (schedule (GateCount.of 4 2))).gates =
                    (fillPairScheduleF g 2).gates + ((mersScheduleF g 2).gates +
                    ((mersScheduleF g 3).gates + GateCount.of 4 2)) from rfl,
                  hf2, hq2, hq3]
                ext <;> norm_num [fillPairClosed, mersClosed, GateCount.of]
      | k + 4 =>
          let qNow : ∀ f, k + 4 ≤ f + 3 → 2 ≤ k + 4 →
              (mersScheduleF f (k + 4)).gates = mersClosed (k + 4) := by
            intro f hf hn
            cases f with
            | zero => omega
            | succ g =>
                rw [mersScheduleF_step]
                have hq := (ih (k + 2) (by omega)).1 g (by omega) (by omega)
                have ha := (ih (k + 2) (by omega)).2 g (by omega) (by omega)
                rw [show (seq4 (mersScheduleF g (k + 2)) (fillPairScheduleF g (k + 2))
                    (schedule (GateCount.adds 4)) (schedule (GateCount.muls 1))).gates =
                    (mersScheduleF g (k + 2)).gates +
                    ((fillPairScheduleF g (k + 2)).gates +
                    (GateCount.adds 4 + GateCount.muls 1)) from rfl,
                  hq, ha]
                have hp : 0 < (2 : ℕ) ^ k := by positivity
                ext <;> simp [mersClosed, fillPairClosed, GateCount.of, pow_succ] <;> omega
          refine ⟨qNow, ?_⟩
          intro f hf hn
          cases f with
          | zero => omega
          | succ g =>
              rw [fillPairScheduleF_step]
              have haPrev := (ih (k + 3) (by omega)).2 g (by omega) (by omega)
              have hqPrev := (ih (k + 3) (by omega)).1 g (by omega) (by omega)
              have hqNow := qNow g (by omega) (by omega)
              rw [show (seq4 (fillPairScheduleF g (k + 3)) (mersScheduleF g (k + 3))
                  (mersScheduleF g (k + 4)) (schedule (GateCount.of 4 2))).gates =
                  (fillPairScheduleF g (k + 3)).gates +
                  ((mersScheduleF g (k + 3)).gates +
                  ((mersScheduleF g (k + 4)).gates + GateCount.of 4 2)) from rfl,
                haPrev, hqPrev, hqNow]
              have hp : 0 < (2 : ℕ) ^ k := by positivity
              ext <;> simp [mersClosed, fillPairClosed, GateCount.of, pow_succ] <;> omega

/-- Paper `lem:fill-Q-count`, pair part. -/
theorem fill_pair_count (l : ℕ) (hl : 2 ≤ l) :
    (fillPairSchedule l).gates =
      GateCount.of (5 * (2 ^ (l - 1) + 2 ^ (l - 2)) - 4)
        (2 ^ l + 2 ^ (l - 1) - 1) := by
  exact (fill_mers_closed_fuel l).2 l (by omega) hl

/-- Paper `lem:fill-Q-count`, final fill part. -/
theorem fill_count (l : ℕ) (hl : 2 ≤ l) :
    (fillSchedule l).gates =
      GateCount.of (5 * (2 ^ (l - 1) + 2 ^ (l - 2)) - 2)
        (2 ^ l + 2 ^ (l - 1)) := by
  rw [fillSchedule, show (thenSchedule (fillPairSchedule l)
      (schedule (GateCount.of 2 1))).gates =
      (fillPairSchedule l).gates + GateCount.of 2 1 from rfl, fill_pair_count l hl]
  have hp0 : 0 < (2 : ℕ) ^ (l - 2) := by positivity
  have hp1 : 0 < (2 : ℕ) ^ (l - 1) := by positivity
  have hp2 : 0 < (2 : ℕ) ^ l := by positivity
  ext <;> simp [GateCount.of] <;> omega

/-- Paper `lem:fill-Q-count`, Mersenne part. -/
theorem mers_count (k : ℕ) (hk : 2 ≤ k) :
    (mersSchedule k).gates = GateCount.of (5 * 2 ^ (k - 2) - 2) (2 ^ (k - 1) - 1) := by
  exact (fill_mers_closed_fuel k).1 k (by omega) hk

/-- The multiplication formula also includes the linear base `Q₁`. -/
theorem mers_multiplication_count (k : ℕ) (hk : 1 ≤ k) :
    (mersSchedule k).gates.multiplications = 2 ^ (k - 1) - 1 := by
  rcases eq_or_ne k 1 with rfl | hk1
  · simp [mersSchedule, mersScheduleF]
  · rw [mers_count k (by omega)]
    rfl

private theorem two_pow_pred (n : ℕ) (hn : 1 ≤ n) :
    2 ^ n = 2 * 2 ^ (n - 1) := by
  calc
    2 ^ n = 2 ^ ((n - 1) + 1) := by
      congr 1
      omega
    _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (n - 1) := by omega

private theorem even_step_arith (k l : ℕ) (hk : 1 < k) (heven : k % 2 = 0)
    (hl : 2 ≤ l) :
    (2 ^ (l - 2) - 1) +
        ((2 ^ (l - 2) - 1) + (2 + ((k / 2 - 1) * 2 ^ l))) =
      (k - 1) * 2 ^ (l - 1) := by
  have hpos : 0 < (2 : ℕ) ^ (l - 2) := by positivity
  have hp1 : 2 ^ (l - 1) = 2 * 2 ^ (l - 2) :=
    two_pow_pred (l - 1) (by omega)
  have hp2 : 2 ^ l = 2 * 2 ^ (l - 1) := two_pow_pred l (by omega)
  have hover : (2 ^ (l - 2) - 1) + ((2 ^ (l - 2) - 1) + 2) =
      2 ^ (l - 1) := by omega
  generalize hr : k / 2 - 1 = r
  have hkrel : k - 1 = 2 * r + 1 := by omega
  calc
    (2 ^ (l - 2) - 1) +
          ((2 ^ (l - 2) - 1) + (2 + (r * 2 ^ l))) =
        2 ^ (l - 1) + r * 2 ^ l := by omega
    _ = (k - 1) * 2 ^ (l - 1) := by rw [hkrel, hp2]; ring

private theorem odd_base_arith (k : ℕ) (hk : 1 < k) (hodd : ¬ k % 2 = 0) :
    1 + (3 + (((k - 1) / 2 - 1) * 4 + 0)) = (k - 1) * 2 := by
  generalize hr : (k - 1) / 2 - 1 = r
  have hkrel : k - 1 = 2 * (r + 1) := by omega
  rw [hkrel]
  ring

private theorem odd_step_arith (k l : ℕ) (hk : 1 < k) (hodd : ¬ k % 2 = 0)
    (hl : 3 ≤ l) :
    (2 ^ (l - 2) - 1) +
        ((2 ^ (l - 3) - 1) +
        ((2 ^ (l - 3) - 1) +
        ((2 ^ (l - 1) - 1) + (4 + (((k - 1) / 2 - 1) * 2 ^ l))))) =
      (k - 1) * 2 ^ (l - 1) := by
  have hpos : 0 < (2 : ℕ) ^ (l - 3) := by positivity
  have hp1 : 2 ^ (l - 2) = 2 * 2 ^ (l - 3) :=
    two_pow_pred (l - 2) (by omega)
  have hp2 : 2 ^ (l - 1) = 2 * 2 ^ (l - 2) :=
    two_pow_pred (l - 1) (by omega)
  have hp3 : 2 ^ l = 2 * 2 ^ (l - 1) := two_pow_pred l (by omega)
  have hover :
      (2 ^ (l - 2) - 1) +
          ((2 ^ (l - 3) - 1) +
          ((2 ^ (l - 3) - 1) + ((2 ^ (l - 1) - 1) + 4))) = 2 ^ l := by
    omega
  generalize hr : (k - 1) / 2 - 1 = r
  have hkrel : k - 1 = 2 * (r + 1) := by omega
  calc
    (2 ^ (l - 2) - 1) +
          ((2 ^ (l - 3) - 1) +
          ((2 ^ (l - 3) - 1) +
          ((2 ^ (l - 1) - 1) + (4 + (r * 2 ^ l))))) =
        2 ^ l + r * 2 ^ l := by omega
    _ = (k - 1) * 2 ^ (l - 1) := by rw [hkrel, hp3]; ring

/-- Calls reachable from the paper's `T` construction. Level one is the shared even base;
an odd nontrivial call can first occur only at level two. -/
def ValidTCall (k l : ℕ) : Prop :=
  1 ≤ l ∧ (1 < k → l = 1 → k % 2 = 0)

private def mersMulFragment (k : ℕ) : Program Unit :=
  schedule (GateCount.muls (mersSchedule k).gates.multiplications)

/-- Fuel-indexed multiplication schedule matching the four branches of `TF`. -/
def tMulScheduleF : ℕ → ℕ → ℕ → Program Unit
  | 0, _, _ => pure ()
  | f + 1, k, l =>
      if k ≤ 1 then pure ()
      else if k % 2 = 0 then
        if l ≤ 1 then
          thenSchedule (schedule (GateCount.muls 1)) (tMulScheduleF f (k / 2) 2)
        else
          seq4 (mersMulFragment (l - 1)) (mersMulFragment (l - 1))
            (schedule (GateCount.muls 2)) (tMulScheduleF f (k / 2) (l + 1))
      else if l ≤ 2 then
        seq4 (mersMulFragment 2) (schedule (GateCount.muls 3))
          (tMulScheduleF f ((k - 1) / 2) 3) (pure ())
      else
        seq5 (mersMulFragment (l - 1)) (mersMulFragment (l - 2))
          (mersMulFragment (l - 2)) (mersMulFragment l)
          (thenSchedule (schedule (GateCount.muls 4))
            (tMulScheduleF f ((k - 1) / 2) (l + 1)))

/-- Multiplication schedule for `Tpair`. -/
def tMulSchedule (k l : ℕ) : Program Unit := tMulScheduleF k k l

theorem tMulScheduleF_succ (f k l : ℕ) :
    tMulScheduleF (f + 1) k l =
      if k ≤ 1 then pure ()
      else if k % 2 = 0 then
        if l ≤ 1 then
          thenSchedule (schedule (GateCount.muls 1)) (tMulScheduleF f (k / 2) 2)
        else
          seq4 (mersMulFragment (l - 1)) (mersMulFragment (l - 1))
            (schedule (GateCount.muls 2)) (tMulScheduleF f (k / 2) (l + 1))
      else if l ≤ 2 then
        seq4 (mersMulFragment 2) (schedule (GateCount.muls 3))
          (tMulScheduleF f ((k - 1) / 2) 3) (pure ())
      else
        seq5 (mersMulFragment (l - 1)) (mersMulFragment (l - 2))
          (mersMulFragment (l - 2)) (mersMulFragment l)
          (thenSchedule (schedule (GateCount.muls 4))
            (tMulScheduleF f ((k - 1) / 2) (l + 1))) := rfl

/-!
The following branch equations are the public interface to the `T` multiplication
schedule.  In particular, clients need not unfold the private sequencing combinators
or the private `mersMulFragment`; this keeps the numerical recurrence and the semantic
circuit compiler independently refactorable.
-/

theorem tMulScheduleF_succ_even_base_multiplications (f k l : ℕ)
    (hk : ¬ k ≤ 1) (heven : k % 2 = 0) (hl : l ≤ 1) :
    (tMulScheduleF (f + 1) k l).gates.multiplications =
      1 + (tMulScheduleF f (k / 2) 2).gates.multiplications := by
  rw [tMulScheduleF_succ, if_neg hk, if_pos heven, if_pos hl]
  rfl

theorem tMulScheduleF_succ_even_main_multiplications (f k l : ℕ)
    (hk : ¬ k ≤ 1) (heven : k % 2 = 0) (hl : ¬ l ≤ 1) :
    (tMulScheduleF (f + 1) k l).gates.multiplications =
      (mersSchedule (l - 1)).gates.multiplications +
        ((mersSchedule (l - 1)).gates.multiplications +
          (2 + (tMulScheduleF f (k / 2) (l + 1)).gates.multiplications)) := by
  rw [tMulScheduleF_succ, if_neg hk, if_pos heven, if_neg hl]
  rfl

theorem tMulScheduleF_succ_odd_base_multiplications (f k l : ℕ)
    (hk : ¬ k ≤ 1) (hodd : ¬ k % 2 = 0) (hl : l ≤ 2) :
    (tMulScheduleF (f + 1) k l).gates.multiplications =
      (mersSchedule 2).gates.multiplications +
        (3 + ((tMulScheduleF f ((k - 1) / 2) 3).gates.multiplications + 0)) := by
  rw [tMulScheduleF_succ, if_neg hk, if_neg hodd, if_pos hl]
  rfl

theorem tMulScheduleF_succ_odd_main_multiplications (f k l : ℕ)
    (hk : ¬ k ≤ 1) (hodd : ¬ k % 2 = 0) (hl : ¬ l ≤ 2) :
    (tMulScheduleF (f + 1) k l).gates.multiplications =
      (mersSchedule (l - 1)).gates.multiplications +
        ((mersSchedule (l - 2)).gates.multiplications +
          ((mersSchedule (l - 2)).gates.multiplications +
            ((mersSchedule l).gates.multiplications +
              (4 + (tMulScheduleF f ((k - 1) / 2) (l + 1)).gates.multiplications)))) := by
  rw [tMulScheduleF_succ, if_neg hk, if_neg hodd, if_neg hl]
  rfl

/-- Fuel-general form of paper `lem:T-multiplication-count`. -/
theorem t_multiplication_count_fuel : ∀ k f l, k ≤ f → ValidTCall k l →
    (tMulScheduleF f k l).gates.multiplications = (k - 1) * 2 ^ (l - 1) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro f l hkf hvalid
      cases f with
      | zero =>
          have hk0 : k = 0 := by omega
          subst hk0
          simp [tMulScheduleF]
      | succ g =>
          rw [tMulScheduleF_succ]
          by_cases hk1 : k ≤ 1
          · rw [if_pos hk1]
            simp
            omega
          · rw [if_neg hk1]
            rcases hvalid with ⟨hl1, hlevel⟩
            by_cases heven : k % 2 = 0
            · rw [if_pos heven]
              by_cases hlbase : l ≤ 1
              · rw [if_pos hlbase]
                have hl : l = 1 := by omega
                subst hl
                have hhalf : k / 2 < k := Nat.div_lt_self (by omega) (by norm_num)
                have hrec := ih (k / 2) hhalf g 2 (by omega)
                  (show ValidTCall (k / 2) 2 from ⟨by omega, by omega⟩)
                rw [show (thenSchedule (schedule (GateCount.muls 1))
                    (tMulScheduleF g (k / 2) 2)).gates.multiplications =
                    1 + (tMulScheduleF g (k / 2) 2).gates.multiplications from rfl,
                  hrec]
                norm_num
                omega
              · rw [if_neg hlbase]
                have hl2 : 2 ≤ l := by omega
                have hhalf : k / 2 < k := Nat.div_lt_self (by omega) (by norm_num)
                have hrec := ih (k / 2) hhalf g (l + 1) (by omega)
                  (show ValidTCall (k / 2) (l + 1) from ⟨by omega, by omega⟩)
                have hq := mers_multiplication_count (l - 1) (by omega)
                rw [show (seq4 (mersMulFragment (l - 1)) (mersMulFragment (l - 1))
                    (schedule (GateCount.muls 2))
                    (tMulScheduleF g (k / 2) (l + 1))).gates.multiplications =
                    (mersSchedule (l - 1)).gates.multiplications +
                    ((mersSchedule (l - 1)).gates.multiplications +
                    (2 + (tMulScheduleF g (k / 2) (l + 1)).gates.multiplications))
                    from rfl,
                  hq, hrec]
                simpa only [show l - 1 - 1 = l - 2 by omega,
                  show l + 1 - 1 = l by omega] using
                  even_step_arith k l (by omega) heven hl2
            · rw [if_neg heven]
              by_cases hlbase : l ≤ 2
              · rw [if_pos hlbase]
                have hl : l = 2 := by
                  by_contra hne
                  have hl' : l = 1 := by omega
                  exact heven (hlevel (by omega) hl')
                subst hl
                have hhalf : (k - 1) / 2 < k := by omega
                have hrec := ih ((k - 1) / 2) hhalf g 3 (by omega)
                  (show ValidTCall ((k - 1) / 2) 3 from ⟨by omega, by omega⟩)
                have hq := mers_multiplication_count 2 (by omega)
                rw [show (seq4 (mersMulFragment 2) (schedule (GateCount.muls 3))
                    (tMulScheduleF g ((k - 1) / 2) 3) (pure ())).gates.multiplications =
                    (mersSchedule 2).gates.multiplications +
                    (3 + ((tMulScheduleF g ((k - 1) / 2) 3).gates.multiplications + 0))
                    from rfl,
                  hq, hrec]
                norm_num
                exact odd_base_arith k (by omega) heven
              · rw [if_neg hlbase]
                have hl3 : 3 ≤ l := by omega
                have hhalf : (k - 1) / 2 < k := by omega
                have hrec := ih ((k - 1) / 2) hhalf g (l + 1) (by omega)
                  (show ValidTCall ((k - 1) / 2) (l + 1) from ⟨by omega, by omega⟩)
                have hq1 := mers_multiplication_count (l - 1) (by omega)
                have hq2 := mers_multiplication_count (l - 2) (by omega)
                have hql := mers_multiplication_count l (by omega)
                rw [show (seq5 (mersMulFragment (l - 1)) (mersMulFragment (l - 2))
                    (mersMulFragment (l - 2)) (mersMulFragment l)
                    (thenSchedule (schedule (GateCount.muls 4))
                      (tMulScheduleF g ((k - 1) / 2) (l + 1)))).gates.multiplications =
                    (mersSchedule (l - 1)).gates.multiplications +
                    ((mersSchedule (l - 2)).gates.multiplications +
                    ((mersSchedule (l - 2)).gates.multiplications +
                    ((mersSchedule l).gates.multiplications +
                    (4 + (tMulScheduleF g ((k - 1) / 2) (l + 1)).gates.multiplications))))
                    from rfl,
                  hq1, hq2, hql, hrec]
                simpa only [show l - 1 - 1 = l - 2 by omega,
                  show l - 2 - 1 = l - 3 by omega,
                  show l + 1 - 1 = l by omega] using
                  odd_step_arith k l (by omega) heven hl3

/-- Paper `lem:T-multiplication-count`. -/
theorem t_multiplication_count (k l : ℕ) (hvalid : ValidTCall k l) :
    (tMulSchedule k l).gates.multiplications = (k - 1) * 2 ^ (l - 1) :=
  t_multiplication_count_fuel k k l le_rfl hvalid

end FastPoly.Cost
