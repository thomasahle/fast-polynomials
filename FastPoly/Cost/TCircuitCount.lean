import FastPoly.Cost.PeeledCircuit
import FastPoly.Cost.TCircuit
import FastPoly.Cost.Counts

/-!
# Multiplication count of the semantic `T` circuit

This file counts the same `tCircuit` whose polynomial semantics is established by
`eval_tCircuit`.  The old numerical schedule remains useful as a compact arithmetic
recurrence, but the bridge below proves that every multiplication in that recurrence
is present in the compiled circuit syntax.

Although the scalar-labelled syntax is parameterized by a commutative ring, the count
uses no characteristic or unit hypothesis.
-/

namespace FastPoly.Cost

universe u

/-- The semantic compiler and the paper's multiplication recurrence have identical
multiplication counts at every fuel, size, and tower level. -/
theorem tCircuitF_multiplications_eq_schedule : ∀ {R : Type u} [CommRing R] fuel k l,
    (tCircuitF (R := R) fuel k l).gates.multiplications =
      (tMulScheduleF fuel k l).gates.multiplications := by
  intro R _ fuel
  induction fuel with
  | zero =>
      intro k l
      rfl
  | succ fuel ih =>
      intro k l
      by_cases hk : k ≤ 1
      · rw [tCircuitF_succ_le_one fuel k l hk, tMulScheduleF_succ, if_pos hk]
        rfl
      · by_cases heven : k % 2 = 0
        · by_cases hl : l ≤ 1
          · rw [tCircuitF_succ_even_base fuel k l hk heven hl,
              tMulScheduleF_succ_even_base_multiplications fuel k l hk heven hl,
              gates_tEvenBaseCircuit_multiplications, ih]
          · have hl1 : 1 ≤ l - 1 := by omega
            rw [tCircuitF_succ_even_main fuel k l hk heven hl,
              tMulScheduleF_succ_even_main_multiplications fuel k l hk heven hl,
              gates_tEvenMainCircuit_multiplications, ih,
              gates_peelCircuit_multiplications (R := R) (l - 1) hl1,
              mers_multiplication_count (l - 1) hl1]
            omega
        · by_cases hl : l ≤ 2
          · rw [tCircuitF_succ_odd_base fuel k l hk heven hl,
              tMulScheduleF_succ_odd_base_multiplications fuel k l hk heven hl,
              gates_tOddBaseCircuit_multiplications, ih,
              gates_peelCircuit_multiplications (R := R) 2 (by omega),
              mers_multiplication_count 2 (by omega)]
            omega
          · have hl1 : 1 ≤ l - 1 := by omega
            have hl2 : 1 ≤ l - 2 := by omega
            have hll : 1 ≤ l := by omega
            rw [tCircuitF_succ_odd_main fuel k l hk heven hl,
              tMulScheduleF_succ_odd_main_multiplications fuel k l hk heven hl,
              gates_tOddMainCircuit_multiplications, ih,
              gates_peelCircuit_multiplications (R := R) (l - 1) hl1,
              gates_peelCircuit_multiplications (R := R) (l - 2) hl2,
              gates_peelCircuit_multiplications (R := R) l hll,
              mers_multiplication_count (l - 1) hl1,
              mers_multiplication_count (l - 2) hl2,
              mers_multiplication_count l hll]
            omega

/-- Exact nonscalar-multiplication count of the semantic `Tpair` circuit. -/
theorem gates_tCircuit_multiplications {R : Type u} [CommRing R] (k l : ℕ)
    (hvalid : ValidTCall k l) :
    (tCircuit (R := R) k l).gates.multiplications = (k - 1) * 2 ^ (l - 1) := by
  rw [tCircuit, tCircuitF_multiplications_eq_schedule]
  exact t_multiplication_count_fuel k k l (by omega) hvalid

end FastPoly.Cost
