import FastPoly.Cost.Counts

/-!
# Exact multiplication counts for the auxiliary odd gadgets

Each definition below is a straight-line-program schedule for one of the three
constructions in paper `lem:odd-gadgets-count`.  The known powers supplied to a gadget
are inputs and therefore carry no cost here.  Sequential composition is legitimate
because the parameter blocks are disjoint; the schedules charge every shared producer
exactly once.
-/

namespace FastPoly.Cost

open Program

/-- The level-one fill is the direct `A₂` base; all later levels satisfy the same
closed multiplication formula. -/
theorem fill_multiplication_count (l : ℕ) (hl : 1 ≤ l) :
    (fillSchedule l).gates.multiplications = 3 * 2 ^ (l - 1) := by
  rcases eq_or_ne l 1 with rfl | hl1
  · rfl
  · rw [fill_count l (by omega)]
    simp only [GateCount.of_multiplications]
    have hp : 2 ^ l = 2 * 2 ^ (l - 1) := by
      calc
        2 ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
        _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
        _ = 2 * 2 ^ (l - 1) := by omega
    rw [hp]
    ring

/-- Schedule for `Q_{4k+1}(x,H₂)`: the `T_{2k,2}` pair followed by the final
product `(x+β)T¹`. -/
def fourKPlusOneSchedule (k : ℕ) : Program Unit :=
  thenSchedule (tMulSchedule (2 * k) 1) (schedule (GateCount.muls 1))

/-- First clause of paper `lem:odd-gadgets-count`. -/
theorem fourKPlusOne_multiplication_count (k : ℕ) (hk : 1 ≤ k) :
    (fourKPlusOneSchedule k).gates.multiplications = 2 * k := by
  have ht := t_multiplication_count (2 * k) 1
    (show ValidTCall (2 * k) 1 from ⟨by omega, by omega⟩)
  rw [fourKPlusOneSchedule,
    show (thenSchedule (tMulSchedule (2 * k) 1)
      (schedule (GateCount.muls 1))).gates.multiplications =
      (tMulSchedule (2 * k) 1).gates.multiplications + 1 from rfl,
    ht]
  norm_num
  omega

/-- Schedule for the known-powers construction of
`Q_{2^(l+1) k + (2^l-1)}`.  Its three charged pieces are the perturbing Mersenne
polynomial, `T_{2k,2^l}`, and the outer level-`l-1` fill. -/
def knownPowersOddSchedule (k l : ℕ) : Program Unit :=
  thenSchedule (mersSchedule (l - 1))
    (thenSchedule (tMulSchedule (2 * k) l) (fillSchedule (l - 1)))

/-- Second clause of paper `lem:odd-gadgets-count`, in its displayed sum form. -/
theorem knownPowersOdd_multiplication_sum (k l : ℕ) (_hk : 1 ≤ k) (hl : 2 ≤ l) :
    (knownPowersOddSchedule k l).gates.multiplications =
      (2 ^ (l - 2) - 1) + (2 * k - 1) * 2 ^ (l - 1) + 3 * 2 ^ (l - 2) := by
  have hq := mers_multiplication_count (l - 1) (by omega)
  have ht := t_multiplication_count (2 * k) l
    (show ValidTCall (2 * k) l from ⟨by omega, by omega⟩)
  have ha := fill_multiplication_count (l - 1) (by omega)
  rw [knownPowersOddSchedule,
    show (thenSchedule (mersSchedule (l - 1))
      (thenSchedule (tMulSchedule (2 * k) l)
        (fillSchedule (l - 1)))).gates.multiplications =
      (mersSchedule (l - 1)).gates.multiplications +
        ((tMulSchedule (2 * k) l).gates.multiplications +
          (fillSchedule (l - 1)).gates.multiplications) from rfl,
    hq, ht, ha]
  simp only [show l - 1 - 1 = l - 2 by omega, Nat.add_assoc]

/-- Arithmetic simplification of the second gadget cost. -/
theorem knownPowersOdd_multiplication_count (k l : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ l) :
    (knownPowersOddSchedule k l).gates.multiplications =
      2 ^ l * k + 2 ^ (l - 1) - 1 := by
  rw [knownPowersOdd_multiplication_sum k l hk hl]
  have hp0 : 0 < (2 : ℕ) ^ (l - 2) := by positivity
  have hp1 : 2 ^ (l - 1) = 2 * 2 ^ (l - 2) := by
    calc
      2 ^ (l - 1) = 2 ^ ((l - 2) + 1) := by congr 1; omega
      _ = 2 ^ (l - 2) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 2) := by omega
  have hp2 : 2 ^ l = 2 * 2 ^ (l - 1) := by
    calc
      2 ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
      _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 1) := by omega
  rw [hp1, hp2]
  have hkpred : 2 * k - 1 + 1 = 2 * k := by omega
  have hmiddle :
      (2 * k - 1) * (2 * 2 ^ (l - 2)) + 2 * 2 ^ (l - 2) =
        4 * k * 2 ^ (l - 2) := by
    calc
      (2 * k - 1) * (2 * 2 ^ (l - 2)) + 2 * 2 ^ (l - 2) =
          (2 * k - 1 + 1) * (2 * 2 ^ (l - 2)) := by ring
      _ = (2 * k) * (2 * 2 ^ (l - 2)) := by rw [hkpred]
      _ = 4 * k * 2 ^ (l - 2) := by ring
  have htarget :
      2 * 2 ^ (l - 1) * k = 4 * k * 2 ^ (l - 2) := by
    rw [hp1]
    ring
  rw [htarget]
  omega

/-- The displayed cost is exactly half, rounded down, of the gadget degree. -/
theorem knownPowersOdd_half_degree (k l : ℕ) (hk : 1 ≤ k) (hl : 2 ≤ l) :
    (knownPowersOddSchedule k l).gates.multiplications =
      (2 ^ (l + 1) * k + (2 ^ l - 1)) / 2 := by
  rw [knownPowersOdd_multiplication_count k l hk hl]
  have hp : 2 ^ (l + 1) = 2 * 2 ^ l := by rw [pow_succ]; ring
  rw [hp]
  have hpos : 0 < (2 : ℕ) ^ l := by positivity
  have hlpow : 2 ^ l = 2 * 2 ^ (l - 1) := by
    calc
      2 ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
      _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 1) := by omega
  have hnum :
      2 * 2 ^ l * k + (2 ^ l - 1) =
        2 * (2 ^ l * k + 2 ^ (l - 1) - 1) + 1 := by
    rw [hlpow]
    have hmul : 2 * (2 * 2 ^ (l - 1)) * k =
        2 * ((2 * 2 ^ (l - 1)) * k) := by ring
    rw [hmul]
    omega
  rw [hnum]
  omega

/-- Schedule for `bar Q_{8k+7}`: one product for `H₈`, the `T_{k,8}` call,
and the six-product level-two fill. -/
def barredEightKPlusSevenSchedule (k : ℕ) : Program Unit :=
  thenSchedule (schedule (GateCount.muls 1))
    (thenSchedule (tMulSchedule k 3) (fillSchedule 2))

/-- Third clause of paper `lem:odd-gadgets-count`, including `bar Q₁₅` at `k=1`. -/
theorem barredEightKPlusSeven_multiplication_count (k : ℕ) (hk : 1 ≤ k) :
    (barredEightKPlusSevenSchedule k).gates.multiplications = 4 * k + 3 := by
  have ht := t_multiplication_count k 3
    (show ValidTCall k 3 from ⟨by omega, by omega⟩)
  have ha := fill_multiplication_count 2 (by omega)
  rw [barredEightKPlusSevenSchedule,
    show (thenSchedule (schedule (GateCount.muls 1))
      (thenSchedule (tMulSchedule k 3) (fillSchedule 2))).gates.multiplications =
      1 + ((tMulSchedule k 3).gates.multiplications +
        (fillSchedule 2).gates.multiplications) from rfl,
    ht, ha]
  norm_num
  omega

/-- Mersenne gadgets also attain half their odd degree, rounded down. -/
theorem mers_half_degree (l : ℕ) (hl : 1 ≤ l) :
    (mersSchedule l).gates.multiplications = (2 ^ l - 1) / 2 := by
  rw [mers_multiplication_count l hl]
  have hp : 2 ^ l = 2 * 2 ^ (l - 1) := by
    calc
      2 ^ l = 2 ^ ((l - 1) + 1) := by congr 1; omega
      _ = 2 ^ (l - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (l - 1) := by omega
  rw [hp]
  have hpos : 0 < (2 : ℕ) ^ (l - 1) := by positivity
  omega

end FastPoly.Cost
