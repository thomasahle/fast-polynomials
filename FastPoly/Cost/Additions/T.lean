import FastPoly.Cost.Counts
import Mathlib.Data.Nat.Log

/-!
# Addition counts for the Mersenne, fill, and shared T schedules

This module contains the exact share-aware recurrences for the primitive schedules and
both the sharp and uniform bounds for the shared T construction. Its branch equations
are the only lemmas that unfold tAdd; downstream gadget and final-cost modules reason
through those equations.
-/

namespace FastPoly.Cost

/-- Ceiling binary logarithm, with `ceilLog2 0 = ceilLog2 1 = 0`. -/
def ceilLog2 (n : ℕ) : ℕ := Nat.clog 2 n

@[simp] theorem ceilLog2_zero : ceilLog2 0 = 0 := by
  rw [ceilLog2, Nat.clog_zero_right]

@[simp] theorem ceilLog2_one : ceilLog2 1 = 0 := by
  rw [ceilLog2, Nat.clog_one_right]

/-- Exact additions in the optimized `Q_{2^s-1}` schedule.  Defining this as a
projection keeps the addition theorem attached to the same schedule used by the
multiplication theorem. -/
def mersAdd (s : ℕ) : ℕ := (mersSchedule s).gates.additions

/-- Exact additions in the full level-`s` fill schedule. -/
def fillAdd (s : ℕ) : ℕ := (fillSchedule s).gates.additions

@[simp] theorem mersAdd_one : mersAdd 1 = 1 := rfl

theorem mersAdd_of_two_le (s : ℕ) (hs : 2 ≤ s) :
    mersAdd s = 5 * 2 ^ (s - 2) - 2 := by
  have h := congrArg GateCount.additions (mers_count s hs)
  simpa only [mersAdd, GateCount.of_additions] using h

@[simp] theorem fillAdd_one : fillAdd 1 = 6 := rfl

theorem fillAdd_of_two_le (s : ℕ) (hs : 2 ≤ s) :
    fillAdd s = 5 * (2 ^ (s - 1) + 2 ^ (s - 2)) - 2 := by
  have h := congrArg GateCount.additions (fill_count s hs)
  simpa only [fillAdd, GateCount.of_additions] using h

/-- Exact addition recurrence for the shared `T_{k,2^l}` schedule.  Power inputs are
already available.  The constants `5` and `15` include the two sharing optimizations at
the shared bases; see `eq:shared-factor` in the manuscript. -/
def tAdd (k l : ℕ) : ℕ :=
  if k ≤ 1 then 0
  else if k % 2 = 0 then
    if l ≤ 1 then tAdd (k / 2) 2 + 5
    else tAdd (k / 2) (l + 1) + 2 * mersAdd (l - 1) + 8
  else if l ≤ 2 then
    tAdd ((k - 1) / 2) 3 + 15
  else
    tAdd ((k - 1) / 2) (l + 1) +
      mersAdd (l - 1) + 2 * mersAdd (l - 2) + mersAdd l + 16
termination_by k
decreasing_by all_goals omega

/-! Named branch equations.  All subsequent proofs use these equations rather than
repeatedly unfolding `tAdd`. -/

theorem tAdd_of_le_one (k l : ℕ) (hk : k ≤ 1) : tAdd k l = 0 := by
  conv_lhs => rw [tAdd]
  rw [if_pos hk]

@[simp] theorem tAdd_one (l : ℕ) : tAdd 1 l = 0 :=
  tAdd_of_le_one 1 l le_rfl

@[simp] theorem tAdd_zero (l : ℕ) : tAdd 0 l = 0 :=
  tAdd_of_le_one 0 l (by omega)

theorem tAdd_even_base (m : ℕ) (hm : 1 ≤ m) :
    tAdd (2 * m) 1 = tAdd m 2 + 5 := by
  conv_lhs => rw [tAdd]
  rw [if_neg (by omega), if_pos (by omega), if_pos (by omega)]
  have hhalf : 2 * m / 2 = m := by omega
  rw [hhalf]

theorem tAdd_even_step (m l : ℕ) (hm : 1 ≤ m) (hl : 2 ≤ l) :
    tAdd (2 * m) l = tAdd m (l + 1) + 2 * mersAdd (l - 1) + 8 := by
  conv_lhs => rw [tAdd]
  rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
  have hhalf : 2 * m / 2 = m := by omega
  rw [hhalf]

theorem tAdd_odd_base (m : ℕ) (hm : 1 ≤ m) :
    tAdd (2 * m + 1) 2 = tAdd m 3 + 15 := by
  conv_lhs => rw [tAdd]
  rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  have hhalf : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hhalf]

theorem tAdd_odd_step (m l : ℕ) (hm : 1 ≤ m) (hl : 3 ≤ l) :
    tAdd (2 * m + 1) l = tAdd m (l + 1) +
      mersAdd (l - 1) + 2 * mersAdd (l - 2) + mersAdd l + 16 := by
  conv_lhs => rw [tAdd]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have hhalf : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hhalf]

private theorem two_pow_pred (n : ℕ) (hn : 1 ≤ n) :
    2 ^ n = 2 * 2 ^ (n - 1) := by
  calc
    2 ^ n = 2 ^ ((n - 1) + 1) := by congr 1; omega
    _ = 2 ^ (n - 1) * 2 := by rw [pow_succ]
    _ = 2 * 2 ^ (n - 1) := by omega

/-- The ordinary even branch has this simpler fresh cost. -/
theorem tAdd_even_step_closed (m l : ℕ) (hm : 1 ≤ m) (hl : 3 ≤ l) :
    tAdd (2 * m) l = tAdd m (l + 1) + 5 * 2 ^ (l - 2) + 4 := by
  rw [tAdd_even_step m l hm (by omega), mersAdd_of_two_le (l - 1) (by omega)]
  have hp : 2 ^ (l - 2) = 2 * 2 ^ (l - 3) :=
    two_pow_pred (l - 2) (by omega)
  rw [show l - 1 - 2 = l - 3 by omega, hp]
  have hpos : 0 < 5 * 2 ^ (l - 3) := by positivity
  omega

/-- Above the exceptional level three, the ordinary odd branch has twice the even fresh
cost. -/
theorem tAdd_odd_step_closed (m l : ℕ) (hm : 1 ≤ m) (hl : 4 ≤ l) :
    tAdd (2 * m + 1) l = tAdd m (l + 1) + 10 * 2 ^ (l - 2) + 8 := by
  rw [tAdd_odd_step m l hm (by omega),
    mersAdd_of_two_le (l - 1) (by omega),
    mersAdd_of_two_le (l - 2) (by omega),
    mersAdd_of_two_le l (by omega)]
  have hp1 : 2 ^ (l - 2) = 2 * 2 ^ (l - 3) :=
    two_pow_pred (l - 2) (by omega)
  have hp2 : 2 ^ (l - 3) = 2 * 2 ^ (l - 4) :=
    two_pow_pred (l - 3) (by omega)
  rw [show l - 1 - 2 = l - 3 by omega,
    show l - 2 - 2 = l - 4 by omega, hp1, hp2]
  have hpos : 0 < 5 * 2 ^ (l - 4) := by positivity
  omega

theorem tAdd_even_two (m : ℕ) (hm : 1 ≤ m) :
    tAdd (2 * m) 2 = tAdd m 3 + 10 := by
  rw [tAdd_even_step m 2 hm (by omega), mersAdd_one]

theorem tAdd_even_three (m : ℕ) (hm : 1 ≤ m) :
    tAdd (2 * m) 3 = tAdd m 4 + 14 := by
  simpa only [show 5 * 2 ^ (3 - 2) + 4 = 14 by rfl]
    using tAdd_even_step_closed m 3 hm (by omega)

theorem tAdd_odd_three (m : ℕ) (hm : 1 ≤ m) :
    tAdd (2 * m + 1) 3 = tAdd m 4 + 29 := by
  rw [tAdd_odd_step m 3 hm (by omega), mersAdd_of_two_le 2 (by omega),
    mersAdd_one, mersAdd_of_two_le 3 (by omega)]
  simp only [Nat.reduceSub, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]

/-! ## Binary-logarithm bookkeeping -/

theorem ceilLog2_two_mul (m : ℕ) (hm : 1 ≤ m) :
    ceilLog2 (2 * m) = ceilLog2 m + 1 := by
  calc
    ceilLog2 (2 * m) = Nat.clog 2 ((2 * m + 2 - 1) / 2) + 1 :=
      Nat.clog_of_two_le (by omega) (by omega)
    _ = ceilLog2 m + 1 := by
      rw [ceilLog2]
      congr 2
      omega

theorem ceilLog2_two_mul_add_one (m : ℕ) (hm : 1 ≤ m) :
    ceilLog2 (2 * m + 1) = ceilLog2 (m + 1) + 1 := by
  calc
    ceilLog2 (2 * m + 1) = Nat.clog 2 ((2 * m + 1 + 2 - 1) / 2) + 1 :=
      Nat.clog_of_two_le (by omega) (by omega)
    _ = ceilLog2 (m + 1) + 1 := by
      rw [ceilLog2]
      congr 2
      omega

theorem ceilLog2_succ_half_le (m : ℕ) (hm : 1 ≤ m) :
    ceilLog2 m + 1 ≤ ceilLog2 (2 * m + 1) := by
  rw [ceilLog2_two_mul_add_one m hm]
  exact Nat.add_le_add_right (Nat.clog_mono_right 2 (by omega)) 1

@[simp] theorem ceilLog2_two : ceilLog2 2 = 1 := by
  simpa only [ceilLog2_one, zero_add] using ceilLog2_two_mul 1 (by omega)

@[simp] theorem ceilLog2_three : ceilLog2 3 = 2 := by
  simpa only [ceilLog2_two, Nat.reduceAdd] using
    ceilLog2_two_mul_add_one 1 (by omega)

/-- Monotonicity of the binary ceiling logarithm. -/
theorem ceilLog2_mono {m n : ℕ} (h : m ≤ n) :
    ceilLog2 m ≤ ceilLog2 n := by
  exact Nat.clog_mono_right 2 h

/-! ## The sharp `T` bounds -/

/-- Strengthened high-level estimate.  The `+4` form avoids truncated subtraction and is
equivalent to manuscript `eq:T-add-sharp-high`. -/
theorem tAdd_sharp_high : ∀ k : ℕ, 2 ≤ k → ∀ l : ℕ, 4 ≤ l →
    tAdd k l + 4 ≤ 5 * 2 ^ (l - 2) * (k - 1) + 8 * ceilLog2 k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk l hl
      by_cases heven : k % 2 = 0
      · let m := k / 2
        have hm : 1 ≤ m := by omega
        have hkform : k = 2 * m := by omega
        rw [hkform, tAdd_even_step_closed m l hm (by omega),
          ceilLog2_two_mul m hm]
        rcases eq_or_ne m 1 with hmEq | hm1
        · rw [hmEq, tAdd_one, ceilLog2_one]
          omega
        · have hm2 : 2 ≤ m := by omega
          have hmk : m < k := by omega
          have hrec := ih m hmk hm2 (l + 1) (by omega)
          have hp : 2 ^ (l + 1 - 2) = 2 * 2 ^ (l - 2) := by
            rw [show l + 1 - 2 = l - 1 by omega]
            exact two_pow_pred (l - 1) (by omega)
          rw [hp] at hrec
          have hshape : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
          rw [hshape]
          calc
            tAdd m (l + 1) + 5 * 2 ^ (l - 2) + 4 + 4
                = (tAdd m (l + 1) + 4) + (5 * 2 ^ (l - 2) + 4) := by omega
            _ ≤ (5 * (2 * 2 ^ (l - 2)) * (m - 1) + 8 * ceilLog2 m) +
                (5 * 2 ^ (l - 2) + 4) := Nat.add_le_add_right hrec _
            _ ≤ 5 * 2 ^ (l - 2) * (2 * (m - 1) + 1) +
                8 * (ceilLog2 m + 1) := by ring_nf; omega
      · have hodd : k % 2 = 1 := by omega
        let m := (k - 1) / 2
        have hm : 1 ≤ m := by omega
        have hkform : k = 2 * m + 1 := by omega
        rw [hkform, tAdd_odd_step_closed m l hm hl,
          show 2 * m + 1 - 1 = 2 * m by omega]
        have hlog : ceilLog2 m + 1 ≤ ceilLog2 (2 * m + 1) :=
          ceilLog2_succ_half_le m hm
        rcases eq_or_ne m 1 with hmEq | hm1
        · rw [hmEq, tAdd_one, ceilLog2_three]
          omega
        · have hm2 : 2 ≤ m := by omega
          have hmk : m < k := by omega
          have hrec := ih m hmk hm2 (l + 1) (by omega)
          have hp : 2 ^ (l + 1 - 2) = 2 * 2 ^ (l - 2) := by
            rw [show l + 1 - 2 = l - 1 by omega]
            exact two_pow_pred (l - 1) (by omega)
          rw [hp] at hrec
          calc
            tAdd m (l + 1) + 10 * 2 ^ (l - 2) + 8 + 4
                = (tAdd m (l + 1) + 4) + (10 * 2 ^ (l - 2) + 8) := by omega
            _ ≤ (5 * (2 * 2 ^ (l - 2)) * (m - 1) + 8 * ceilLog2 m) +
                (10 * 2 ^ (l - 2) + 8) := Nat.add_le_add_right hrec _
            _ = 5 * 2 ^ (l - 2) * (2 * m) + 8 * (ceilLog2 m + 1) := by
              generalize hr : m - 1 = r
              have hmShape : m = r + 1 := by omega
              rw [hmShape]
              ring
            _ ≤ 5 * 2 ^ (l - 2) * (2 * m) + 8 * ceilLog2 (2 * m + 1) := by
              exact Nat.add_le_add_left (Nat.mul_le_mul_left 8 hlog) _

/-- Level-three consequence, including its exceptional odd fresh cost `29`. -/
theorem tAdd_sharp_three (k : ℕ) (hk : 1 ≤ k) :
    tAdd k 3 ≤ 10 * (k - 1) + 8 * ceilLog2 k := by
  by_cases hk1 : k ≤ 1
  · have hkEq : k = 1 := by omega
    subst hkEq
    rw [tAdd_one, ceilLog2_one]
  · by_cases heven : k % 2 = 0
    · let m := k / 2
      have hm : 1 ≤ m := by omega
      have hkform : k = 2 * m := by omega
      rw [hkform, tAdd_even_three m hm, ceilLog2_two_mul m hm]
      rcases eq_or_ne m 1 with hmEq | hm1
      · rw [hmEq, tAdd_one, ceilLog2_one]
        omega
      · have hm2 : 2 ≤ m := by omega
        have hrec := tAdd_sharp_high m hm2 4 (by omega)
        rw [show 2 ^ (4 - 2) = 4 by rfl] at hrec
        have hshape : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
        rw [hshape]
        calc
          tAdd m 4 + 14 ≤ 20 * (m - 1) + 8 * ceilLog2 m + 10 := by
            omega
          _ ≤ 10 * (2 * (m - 1) + 1) + 8 * (ceilLog2 m + 1) := by ring_nf; omega
    · have hodd : k % 2 = 1 := by omega
      let m := (k - 1) / 2
      have hm : 1 ≤ m := by omega
      have hkform : k = 2 * m + 1 := by omega
      rw [hkform, tAdd_odd_three m hm,
        show 2 * m + 1 - 1 = 2 * m by omega]
      have hlog := ceilLog2_succ_half_le m hm
      rcases eq_or_ne m 1 with hmEq | hm1
      · rw [hmEq, tAdd_one, ceilLog2_three]
        omega
      · have hm2 : 2 ≤ m := by omega
        have hrec := tAdd_sharp_high m hm2 4 (by omega)
        rw [show 2 ^ (4 - 2) = 4 by rfl] at hrec
        calc
          tAdd m 4 + 29 ≤ 20 * (m - 1) + 8 * ceilLog2 m + 25 := by
            omega
          _ ≤ 10 * (2 * m) + 8 * (ceilLog2 m + 1) := by omega
          _ ≤ 10 * (2 * m) + 8 * ceilLog2 (2 * m + 1) := by
            exact Nat.add_le_add_left (Nat.mul_le_mul_left 8 hlog) _

/-- Level-two form used by every auxiliary gadget. -/
theorem tAdd_sharp_two (k : ℕ) (hk : 1 ≤ k) :
    tAdd k 2 ≤ 5 * (k - 1) + 8 * ceilLog2 k := by
  by_cases hk1 : k ≤ 1
  · have hkEq : k = 1 := by omega
    subst hkEq
    rw [tAdd_one, ceilLog2_one]
  · by_cases heven : k % 2 = 0
    · let m := k / 2
      have hm : 1 ≤ m := by omega
      have hkform : k = 2 * m := by omega
      rw [hkform, tAdd_even_two m hm, ceilLog2_two_mul m hm]
      have hrec := tAdd_sharp_three m hm
      have hshape : 2 * m - 1 = 2 * (m - 1) + 1 := by omega
      rw [hshape]
      calc
        tAdd m 3 + 10 ≤ 10 * (m - 1) + 8 * ceilLog2 m + 10 := by omega
        _ ≤ 5 * (2 * (m - 1) + 1) + 8 * (ceilLog2 m + 1) := by ring_nf; omega
    · have hodd : k % 2 = 1 := by omega
      let m := (k - 1) / 2
      have hm : 1 ≤ m := by omega
      have hkform : k = 2 * m + 1 := by omega
      rw [hkform, tAdd_odd_base m hm,
        show 2 * m + 1 - 1 = 2 * m by omega]
      have hrec := tAdd_sharp_three m hm
      have hlog := ceilLog2_succ_half_le m hm
      calc
        tAdd m 3 + 15 ≤ 10 * (m - 1) + 8 * ceilLog2 m + 15 := by omega
        _ ≤ 5 * (2 * m) + 8 * (ceilLog2 m + 1) := by ring_nf; omega
        _ ≤ 5 * (2 * m) + 8 * ceilLog2 (2 * m + 1) := by
          exact Nat.add_le_add_left (Nat.mul_le_mul_left 8 hlog) _

/-! ## Uniform linear `T` bounds -/

private theorem two_pow_two_pred (l : ℕ) (hl : 2 ≤ l) :
    2 ^ l = 4 * 2 ^ (l - 2) := by
  rw [two_pow_pred l (by omega), two_pow_pred (l - 1) (by omega)]
  rw [show l - 1 - 1 = l - 2 by omega]
  ring

/-- A single upper recurrence covering the exceptional odd level three and every
ordinary odd level above it. -/
private theorem tAdd_odd_step_coarse (m l : ℕ) (hm : 1 ≤ m) (hl : 3 ≤ l) :
    tAdd (2 * m + 1) l ≤ tAdd m (l + 1) + 10 * 2 ^ (l - 2) + 9 := by
  rcases eq_or_lt_of_le hl with rfl | hl4
  · rw [tAdd_odd_three m hm]
    simp only [Nat.reduceSub, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
    omega
  · rw [tAdd_odd_step_closed m l hm (by omega)]
    omega

/-- Subtraction-free form of manuscript `eq:T-add-bound-high`:
`τ(k,l) ≤ 2(k-1)2^l - (3·2^(l-2)-4)`. -/
theorem tAdd_uniform_high : ∀ k : ℕ, 2 ≤ k → ∀ l : ℕ, 3 ≤ l →
    tAdd k l + 3 * 2 ^ (l - 2) ≤ 2 * (k - 1) * 2 ^ l + 4 := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
      intro hk l hl
      have hp : 0 < 2 ^ (l - 2) := by positivity
      have hpTwo : 2 ≤ 2 ^ (l - 2) := by
        rw [two_pow_pred (l - 2) (by omega)]
        have : 0 < 2 ^ (l - 2 - 1) := by positivity
        omega
      have hpow : 2 ^ l = 4 * 2 ^ (l - 2) := two_pow_two_pred l (by omega)
      by_cases heven : k % 2 = 0
      · let m := k / 2
        have hm : 1 ≤ m := by omega
        have hkform : k = 2 * m := by omega
        rw [hkform, tAdd_even_step_closed m l hm hl,
          show 2 * m - 1 = 2 * (m - 1) + 1 by omega, hpow]
        rcases eq_or_ne m 1 with hmEq | hm1
        · rw [hmEq, tAdd_one]
          ring_nf
          omega
        · have hm2 : 2 ≤ m := by omega
          have hmk : m < k := by omega
          have hrec := ih m hmk hm2 (l + 1) (by omega)
          have hpRec : 2 ^ (l + 1 - 2) = 2 * 2 ^ (l - 2) := by
            rw [show l + 1 - 2 = l - 1 by omega]
            exact two_pow_pred (l - 1) (by omega)
          have hpowRec : 2 ^ (l + 1) = 8 * 2 ^ (l - 2) := by
            rw [two_pow_pred (l + 1) (by omega),
              show l + 1 - 1 = l by omega, hpow]
            ring
          rw [hpRec, hpowRec] at hrec
          ring_nf at hrec ⊢
          omega
      · have hodd : k % 2 = 1 := by omega
        let m := (k - 1) / 2
        have hm : 1 ≤ m := by omega
        have hkform : k = 2 * m + 1 := by omega
        rw [hkform, show 2 * m + 1 - 1 = 2 * m by omega, hpow]
        have hstep := tAdd_odd_step_coarse m l hm hl
        rcases eq_or_ne m 1 with hmEq | hm1
        · rw [hmEq] at hstep ⊢
          rw [tAdd_one] at hstep
          ring_nf at hstep ⊢
          omega
        · have hm2 : 2 ≤ m := by omega
          have hmk : m < k := by omega
          have hrec := ih m hmk hm2 (l + 1) (by omega)
          have hpRec : 2 ^ (l + 1 - 2) = 2 * 2 ^ (l - 2) := by
            rw [show l + 1 - 2 = l - 1 by omega]
            exact two_pow_pred (l - 1) (by omega)
          have hpowRec : 2 ^ (l + 1) = 8 * 2 ^ (l - 2) := by
            rw [two_pow_pred (l + 1) (by omega),
              show l + 1 - 1 = l by omega, hpow]
            ring
          rw [hpRec, hpowRec] at hrec
          have hmul : m * 2 ^ (l - 2) =
              (m - 1) * 2 ^ (l - 2) + 2 ^ (l - 2) := by
            generalize hr : m - 1 = r
            have hmShape : m = r + 1 := by omega
            rw [hmShape]
            ring
          ring_nf at hrec hstep ⊢
          ring_nf at hmul
          omega

/-- Manuscript `eq:T-add-bound-2`. -/
theorem tAdd_uniform_two (k : ℕ) (hk : 1 ≤ k) :
    tAdd k 2 ≤ 8 * (k - 1) + 2 := by
  rcases eq_or_ne k 1 with rfl | hk1
  · rw [tAdd_one]
    omega
  by_cases heven : k % 2 = 0
  · let m := k / 2
    have hm : 1 ≤ m := by omega
    have hkform : k = 2 * m := by omega
    rw [hkform, tAdd_even_two m hm,
      show 2 * m - 1 = 2 * (m - 1) + 1 by omega]
    rcases eq_or_ne m 1 with hmEq | hm1
    · rw [hmEq, tAdd_one]
    · have hm2 : 2 ≤ m := by omega
      have hrec := tAdd_uniform_high m hm2 3 (by omega)
      ring_nf at hrec ⊢
      omega
  · have hodd : k % 2 = 1 := by omega
    let m := (k - 1) / 2
    have hm : 1 ≤ m := by omega
    have hkform : k = 2 * m + 1 := by omega
    rw [hkform, tAdd_odd_base m hm,
      show 2 * m + 1 - 1 = 2 * m by omega]
    rcases eq_or_ne m 1 with hmEq | hm1
    · rw [hmEq, tAdd_one]
      omega
    · have hm2 : 2 ≤ m := by omega
      have hrec := tAdd_uniform_high m hm2 3 (by omega)
      ring_nf at hrec ⊢
      omega

/-- Manuscript `eq:T-add-bound-1`. -/
theorem tAdd_uniform_one (k : ℕ) (hk : 1 ≤ k) :
    tAdd (2 * k) 1 ≤ 8 * k - 1 := by
  rw [tAdd_even_base k hk]
  have hrec := tAdd_uniform_two k hk
  omega

end FastPoly.Cost
