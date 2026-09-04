import FastPoly.Cost.Additions.T
import FastPoly.Cost.RetainedShiftTCompiler

/-!
# Exact addition count of the retained-shift `T` compiler

The numerical `tAdd` recurrence counts the optimized shared bases.  This module proves
that it is also the literal addition count of `RetainedShiftT.compiler`.  The proof
first identifies peeled-tail circuit counts with `mersAdd`, then follows the compiler's
named branch equations.  High-level calls cannot encounter a shared base and are
handled by a separate fuel induction; level-one even calls carry the retained scalar
through the recursive level-two call exactly as the circuit does.
-/

namespace FastPoly.Cost

universe u

/-- A peeled known-powers circuit has exactly the selected `mersAdd` cost. -/
theorem gates_peelCircuit_additions_eq_mersAdd {R : Type u} [CommRing R]
    (k : ℕ) (hk : 1 ≤ k) :
    (peelCircuit (R := R) k).gates.additions = mersAdd k := by
  rcases eq_or_ne k 1 with rfl | hk1
  · rfl
  · have hk2 : 2 ≤ k := by omega
    rw [gates_peelCircuit k hk2, mersAdd_of_two_le k hk2]
    rfl

/-- Exact fresh additions in an ordinary even main branch. -/
theorem gates_tEvenMainCircuit_additions {R : Type u} [CommRing R]
    (k l : ℕ) (inner : Circuit R ConstructionInput 2)
    (hl : 2 ≤ l) :
    (tEvenMainCircuit k l inner).gates.additions =
      inner.gates.additions + 2 * mersAdd (l - 1) + 8 := by
  simp only [tEvenMainCircuit, Circuit.gates_bind, gates_recurseWithPowerPair,
    tEvenMainPowerPair, Circuit.gates, GateCount.add_additions,
    GateCount.zero_additions, GateCount.adds_additions,
    Circuit.gates_diffSquareAdd_additions,
    Circuit.gates_constructionPower, Circuit.gates_constructionShiftedPower,
    Circuit.gates_constructionParameter,
    Circuit.gates_reindexConstructionParameters]
  rw [gates_peelCircuit_additions_eq_mersAdd (R := R) (l - 1) (by omega)]
  omega

/-- Exact fresh additions in an ordinary odd main branch. -/
theorem gates_tOddMainCircuit_additions {R : Type u} [CommRing R]
    (k l : ℕ) (inner : Circuit R ConstructionInput 2)
    (hl : 3 ≤ l) :
    (tOddMainCircuit k l inner).gates.additions =
      inner.gates.additions + mersAdd (l - 1) + 2 * mersAdd (l - 2) +
        mersAdd l + 16 := by
  rw [tOddMainCircuit]
  simp only [finishOdd, tOddMainAux, tOddMainShiftPair,
    Circuit.gates_bind, gates_recurseWithPowerPair,
    Circuit.gates, priorBound, Circuit.gates_input,
    Circuit.gates_rightInput, Circuit.gates_liftLeft,
    Circuit.gates_diffSquareAdd_additions,
    GateCount.add_additions, GateCount.zero_additions,
    GateCount.adds_additions, GateCount.muls_additions,
    Circuit.gates_constructionPower, Circuit.gates_constructionShiftedPower,
    Circuit.gates_constructionParameter,
    Circuit.gates_reindexConstructionParameters]
  rw [gates_peelCircuit_additions_eq_mersAdd (R := R) (l - 1) (by omega),
    gates_peelCircuit_additions_eq_mersAdd (R := R) (l - 2) (by omega),
    gates_peelCircuit_additions_eq_mersAdd (R := R) l (by omega)]
  omega

/-- Above the shared-base levels, the ordinary compiler already has the optimized
`tAdd` count. -/
theorem tCircuitF_additions_eq_tAdd_of_three_le :
    ∀ {R : Type u} [CommRing R] fuel k l, k ≤ fuel → 3 ≤ l →
      (tCircuitF (R := R) fuel k l).gates.additions = tAdd k l := by
  intro R _ fuel
  induction fuel with
  | zero =>
      intro k l hk hl
      have hk0 : k = 0 := by omega
      subst k
      rw [tCircuitF, tAdd_zero]
      rfl
  | succ fuel ih =>
      intro k l hkfuel hl
      by_cases hk : k ≤ 1
      · rw [tCircuitF_succ_le_one fuel k l hk, tAdd_of_le_one k l hk]
        rfl
      · by_cases heven : k % 2 = 0
        · let m := k / 2
          have hm : 1 ≤ m := by omega
          have hkform : k = 2 * m := by omega
          rw [tCircuitF_succ_even_main fuel k l hk heven (by omega)]
          rw [gates_tEvenMainCircuit_additions k l _ (by omega)]
          have hmfuel : m ≤ fuel := by omega
          have hinner := ih m (l + 1) hmfuel (by omega)
          rw [hinner, hkform, tAdd_even_step m l hm (by omega)]
        · let m := (k - 1) / 2
          have hm : 1 ≤ m := by omega
          have hkform : k = 2 * m + 1 := by omega
          rw [tCircuitF_succ_odd_main fuel k l hk heven (by omega)]
          rw [gates_tOddMainCircuit_additions k l _ hl]
          have hmfuel : m ≤ fuel := by omega
          have hinner := ih m (l + 1) hmfuel (by omega)
          rw [hinner, hkform, tAdd_odd_step m l hm hl]

namespace RetainedShiftT

/-- Fuelled retained compiler count, used by the level-one even recursion. -/
theorem compilerF_additions_eq_tAdd :
    ∀ {R : Type u} [CommRing R] fuel k l, k ≤ fuel → ValidTCall k l →
      (compilerF (R := R) fuel k l).gates.additions = tAdd k l := by
  intro R _ fuel
  induction fuel with
  | zero =>
      intro k l hk hvalid
      have hk0 : k = 0 := by omega
      subst k
      rw [compilerF_zero, tCircuitF, tAdd_zero]
      rfl
  | succ fuel ih =>
      intro k l hkfuel hvalid
      have hlpos : 1 ≤ l := hvalid.1
      by_cases hk : k ≤ 1
      · rw [compilerF_succ_le_one fuel k l hk, tCircuitF_succ_le_one fuel k l hk,
          tAdd_of_le_one k l hk]
        rfl
      · by_cases heven : k % 2 = 0
        · by_cases hl : l ≤ 1
          · have hl1 : l = 1 := by omega
            subst l
            let m := k / 2
            have hm : 1 ≤ m := by omega
            have hkform : k = 2 * m := by omega
            rw [compilerF_succ_even_base fuel k 1 hk heven (by omega),
              evenBaseCircuit_additions]
            simp only [Circuit.gates_constructionSource, GateCount.zero_additions]
            have hmfuel : m ≤ fuel := by
              have hbound : 2 * m ≤ fuel + 1 := by simpa only [← hkform] using hkfuel
              omega
            have hinner := ih m 2 hmfuel
              (show ValidTCall m 2 from ⟨by omega, by omega⟩)
            rw [hinner, hkform, tAdd_even_base m hm]
            omega
          · have hl2 : 2 ≤ l := by omega
            rw [compilerF_succ_even_main fuel k l hk heven hl,
              tCircuitF_succ_even_main fuel k l hk heven hl,
              gates_tEvenMainCircuit_additions k l _ hl2]
            let m := k / 2
            have hm : 1 ≤ m := by omega
            have hkform : k = 2 * m := by omega
            have hmfuel : m ≤ fuel := by omega
            have hinner := tCircuitF_additions_eq_tAdd_of_three_le
              (R := R) fuel m (l + 1) hmfuel (by omega)
            rw [hinner, hkform, tAdd_even_step m l hm hl2]
        · by_cases hl : l ≤ 2
          · have hl2 : l = 2 := by
              rcases hvalid with ⟨hlpos, hpar⟩
              have hne : l ≠ 1 := by
                intro hl1
                exact heven (hpar (by omega) hl1)
              omega
            subst l
            let m := (k - 1) / 2
            have hm : 1 ≤ m := by omega
            have hkform : k = 2 * m + 1 := by omega
            rw [compilerF_succ_odd_base fuel k 2 hk heven (by omega),
              oddBaseCircuit_additions]
            simp only [Circuit.gates_constructionSource, GateCount.zero_additions]
            have hmfuel : m ≤ fuel := by omega
            have hinner := tCircuitF_additions_eq_tAdd_of_three_le
              (R := R) fuel m 3 hmfuel (by omega)
            rw [hinner, hkform, tAdd_odd_base m hm]
            omega
          · rw [compilerF_succ_odd_main fuel k l hk heven hl]
            exact tCircuitF_additions_eq_tAdd_of_three_le
              (R := R) (fuel + 1) k l hkfuel (by omega)

/-- Exact addition count of the optimized retained-shift `T` compiler. -/
theorem compiler_additions_eq_tAdd {R : Type u} [CommRing R] (k l : ℕ)
    (hvalid : ValidTCall k l) :
    (compiler (R := R) k l).gates.additions = tAdd k l := by
  exact compilerF_additions_eq_tAdd k k l le_rfl hvalid

end RetainedShiftT

end FastPoly.Cost
