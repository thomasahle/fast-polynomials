import FastPoly.Height.ConstructionDepth
import Mathlib.Data.Nat.Log
import FastPoly.Cost.TCircuit

/-!
# Height ledger for the compiled `T` recursion

Depth analogues of the `TCircuit` gate-count layer, mirroring the paper's
tower/spine invariants (`thm:construction-height`): over a tower at
depths `dp i ≤ i` (and shifted power at depth `dps ≤ l`), the compiled
`T_{k,2^l}` pair has multiplicative depth at most `l + 2·log₂ k`.  The
recursion threads the tower invariant through `withPowerPair`: each branch
rebinds level `l+1` at depth `≤ l+1`, which is exactly the paper's
`h(H_{2^{ℓ+1}}) = ℓ+1` step, with the hanging blocks supplied at depth
`≤ ℓ` by `multDepth_peelCircuit`.
-/

namespace FastPoly.Height

open FastPoly.Cost

variable {R : Type*} [CommRing R]

/-- Depth-side analogue of `constructionEnv_withPowerPair`. -/
theorem denv_withPowerPair (dp : ℕ → ℕ) (dps : ℕ) {m : ℕ} (dvals : Fin m → ℕ)
    (level : ℕ) (parameterMap : ℕ → ℕ) (powerSlot shiftedSlot : Fin m) :
    Sum.elim (denv dp dps) dvals ∘
        ConstructionInput.withPowerPair level parameterMap powerSlot shiftedSlot =
      denv (Function.update dp level (dvals powerSlot)) (dvals shiftedSlot) := by
  funext input
  cases input
  · rfl
  · rename_i i
    by_cases hi : i = level
    · subst hi
      simp only [ConstructionInput.withPowerPair, if_true,
        Function.comp_apply, Sum.elim_inr, denv_power, Function.update_self]
    · simp only [ConstructionInput.withPowerPair, hi, if_false, Function.comp_apply,
        Sum.elim_inl, denv_power, Function.update_of_ne hi]
  · rfl
  · rfl
  · rfl

omit [CommRing R] in
/-- Depth of a recursive call after binding a new power pair. -/
theorem multDepth_recurseWithPowerPair {m : ℕ} (level : ℕ)
    (parameterMap : ℕ → ℕ) (powerSlot shiftedSlot : Fin m)
    (inner : Circuit R ConstructionInput 2)
    (dp : ℕ → ℕ) (dps : ℕ) (dvals : Fin m → ℕ) :
    (recurseWithPowerPair level parameterMap powerSlot shiftedSlot inner).multDepth
        (Sum.elim (denv dp dps) dvals) =
      inner.multDepth
        (denv (Function.update dp level (dvals powerSlot)) (dvals shiftedSlot)) := by
  rw [recurseWithPowerPair, Circuit.multDepth_relabel, denv_withPowerPair]

omit [CommRing R] in
/-- Depth of the bound square-difference shell. -/
theorem multDepth_diffSquareAdd {ι : Type*} (center shift tail : Circuit R ι 1)
    (env : ι → ℕ) :
    (Circuit.diffSquareAdd center shift tail).multDepth env 0 =
      max (max (center.multDepth env 0) (shift.multDepth env 0) + 1)
        (tail.multDepth env 0) := by
  show max (max
      (max (Fin.addCases (center.multDepth env) (shift.multDepth env) (0 : Fin 2))
        (Fin.addCases (center.multDepth env) (shift.multDepth env) (1 : Fin 2)))
      (max (Fin.addCases (center.multDepth env) (shift.multDepth env) (0 : Fin 2))
        (Fin.addCases (center.multDepth env) (shift.multDepth env) (1 : Fin 2)))
      + 1)
      (tail.liftLeft.multDepth (Sum.elim env _) 0) = _
  rw [Circuit.multDepth_liftLeft]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
    Fin.addCases_left, Fin.addCases_right]
  omega

omit [CommRing R] in
/-- Depth of the reindexed peeled block (`tmers` wrapper): at most its level. -/
theorem multDepth_tmers_le (k : ℕ) (parameterMap : ℕ → ℕ)
    (dp : ℕ → ℕ) (dps : ℕ) (hk : 1 ≤ k)
    (hdp : ∀ i, 1 ≤ i → i < k → dp i ≤ i) :
    ((peelCircuit (R := R) k).reindexConstructionParameters parameterMap).multDepth
        (denv dp dps) 0 ≤ k := by
  rw [multDepth_reindexConstructionParameters]
  exact multDepth_peelCircuit dp dps k hk hdp

section evenBranches

omit [CommRing R] in
/-- Depth of the shared even base's bound pair, first output (`H₄`). -/
theorem multDepth_tEvenBasePowerPair_zero (k : ℕ) (dp : ℕ → ℕ) (dps : ℕ) :
    (tEvenBasePowerPair (R := R) k).multDepth (denv dp dps) 0 = dp 1 + 1 := by
  unfold tEvenBasePowerPair
  rw [Circuit.multDepth_bind, Circuit.multDepth_fork,
    show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_left]
  rw [Circuit.multDepth_rightInput, multDepth_diffSquareAdd]
  show max (max (dp 1) (max (max 0 0) 0) + 1) 0 = dp 1 + 1
  omega

omit [CommRing R] in
/-- Depth of the shared even base's bound pair, second output (`H̃₄`). -/
theorem multDepth_tEvenBasePowerPair_one (k : ℕ) (dp : ℕ → ℕ) (dps : ℕ) :
    (tEvenBasePowerPair (R := R) k).multDepth (denv dp dps) 1
      = max (dp 1 + 1) (max dps (dp 1)) := by
  unfold tEvenBasePowerPair
  rw [Circuit.multDepth_bind, Circuit.multDepth_fork,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_right]
  rw [Circuit.multDepth_add, Circuit.multDepth_sub]
  rw [Circuit.multDepth_rightInput, Circuit.multDepth_liftLeft,
    Circuit.multDepth_liftLeft, multDepth_diffSquareAdd]
  simp only [Circuit.constructionPower, Circuit.constructionX,
    Circuit.constructionParameter, Circuit.constructionShiftedPower,
    Circuit.multDepth_input, Circuit.multDepth_add, denv_power, denv_variable,
    denv_parameter, denv_shiftedPower]
  omega

omit [CommRing R] in
/-- Depth of an ordinary even step's pair, first output (`H_{2^{l+1}}`):
the tower step `h(H_{2^{ℓ+1}}) ≤ ℓ+1`. -/
theorem multDepth_tEvenMainPowerPair_zero_le (k l : ℕ) (dp : ℕ → ℕ) (dps : ℕ)
    (hl : 2 ≤ l) (hdp : ∀ i, 1 ≤ i → i ≤ l → dp i ≤ i) :
    (tEvenMainPowerPair (R := R) k l).multDepth (denv dp dps) 0 ≤ l + 1 := by
  have hs1 := multDepth_tmers_le (R := R) (l - 1)
    (fun j => (k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j) dp dps (by omega)
    (fun i hi1 hik => hdp i hi1 (by omega))
  have hs2 := multDepth_tmers_le (R := R) (l - 1)
    (fun j => (k - 2) * 2 ^ l + 1 + j) dp dps (by omega)
    (fun i hi1 hik => hdp i hi1 (by omega))
  have hpl := hdp l (by omega) le_rfl
  have hpl1 := hdp (l - 1) (by omega) (by omega)
  unfold tEvenMainPowerPair
  rw [Circuit.multDepth_fork,
    show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_left]
  rw [multDepth_diffSquareAdd]
  show max (max (dp l)
      (max (dp (l - 1)) (((peelCircuit (R := R) (l - 1)).reindexConstructionParameters
        _).multDepth (denv dp dps) 0)) + 1)
      (((peelCircuit (R := R) (l - 1)).reindexConstructionParameters
        _).multDepth (denv dp dps) 0) ≤ l + 1
  omega

omit [CommRing R] in
/-- Depth of an ordinary even step's pair, second output (`H̃_{2^{l+1}}`). -/
theorem multDepth_tEvenMainPowerPair_one_le (k l : ℕ) (dp : ℕ → ℕ) (dps : ℕ)
    (hl : 2 ≤ l) (hdp : ∀ i, 1 ≤ i → i ≤ l → dp i ≤ i) (hdps : dps ≤ l) :
    (tEvenMainPowerPair (R := R) k l).multDepth (denv dp dps) 1 ≤ l + 1 := by
  have hpl1 := hdp (l - 1) (by omega) (by omega)
  unfold tEvenMainPowerPair
  rw [Circuit.multDepth_fork,
    show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_right]
  rw [multDepth_diffSquareAdd]
  show max (max dps (max (dp (l - 1)) 0) + 1) 0 ≤ l + 1
  omega

end evenBranches

section oddBranches

omit [CommRing R] in
/-- Depth of `finishOdd`, first output. -/
theorem multDepth_finishOdd_zero (level : ℕ) (parameterMap : ℕ → ℕ)
    (aux : Circuit R ConstructionInput 6) (inner : Circuit R ConstructionInput 2)
    (dp : ℕ → ℕ) (dps : ℕ) :
    (finishOdd level parameterMap aux inner).multDepth (denv dp dps) 0 =
      max (max (aux.multDepth (denv dp dps) 2)
          (inner.multDepth
            (denv (Function.update dp level (aux.multDepth (denv dp dps) 0))
              (aux.multDepth (denv dp dps) 1)) 0) + 1)
        (aux.multDepth (denv dp dps) 4) := by
  rw [finishOdd, Circuit.multDepth_bind, Circuit.multDepth_bind]
  rw [multDepth_recurseWithPowerPair]
  rw [Circuit.multDepth_fork]
  rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_left, Circuit.multDepth_add, Circuit.multDepth_mul,
    priorBound, Circuit.multDepth_input, Circuit.multDepth_rightInput,
    Sum.elim_inl, Sum.elim_inr]

omit [CommRing R] in
/-- Depth of `finishOdd`, second output. -/
theorem multDepth_finishOdd_one (level : ℕ) (parameterMap : ℕ → ℕ)
    (aux : Circuit R ConstructionInput 6) (inner : Circuit R ConstructionInput 2)
    (dp : ℕ → ℕ) (dps : ℕ) :
    (finishOdd level parameterMap aux inner).multDepth (denv dp dps) 1 =
      max (max (aux.multDepth (denv dp dps) 3)
          (inner.multDepth
            (denv (Function.update dp level (aux.multDepth (denv dp dps) 0))
              (aux.multDepth (denv dp dps) 1)) 1) + 1)
        (aux.multDepth (denv dp dps) 5) := by
  rw [finishOdd, Circuit.multDepth_bind, Circuit.multDepth_bind]
  rw [multDepth_recurseWithPowerPair]
  rw [Circuit.multDepth_fork]
  rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
  simp only [Fin.addCases_right, Circuit.multDepth_add, Circuit.multDepth_mul,
    priorBound, Circuit.multDepth_input, Circuit.multDepth_rightInput,
    Sum.elim_inl, Sum.elim_inr]

/-- Aux-output depths of the shared odd base: all six at once. -/
theorem multDepth_tOddBaseAux_le (k : ℕ) (dp : ℕ → ℕ) (dps : ℕ)
    (h1 : dp 1 ≤ 1) (h2 : dp 2 ≤ 2) (hdps : dps ≤ 2) :
    (tOddBaseAux (R := R) k).multDepth (denv dp dps) 0 ≤ 3 ∧
    (tOddBaseAux (R := R) k).multDepth (denv dp dps) 1 ≤ 3 ∧
    (tOddBaseAux (R := R) k).multDepth (denv dp dps) 2 ≤ 2 ∧
    (tOddBaseAux (R := R) k).multDepth (denv dp dps) 3 ≤ 2 ∧
    (tOddBaseAux (R := R) k).multDepth (denv dp dps) 4 ≤ 2 ∧
    (tOddBaseAux (R := R) k).multDepth (denv dp dps) 5 ≤ 2 := by
  have hq2 : (peelCircuit (R := R) 2).multDepth (denv dp dps) 0 ≤ 2 :=
    multDepth_peelCircuit dp dps 2 (by omega) (fun i hi1 hik => by
      match i, hi1, hik with
      | 1, _, _ => exact h1)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [tOddBaseAux, Circuit.multDepth_bind, Circuit.multDepth_fork,
      Circuit.multDepth_add, Circuit.multDepth_sub, Circuit.multDepth_scale,
      multDepth_diffSquareAdd, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Circuit.multDepth_input,
      multDepth_reindexConstructionParameters,
      Circuit.constructionPower, Circuit.constructionX,
      Circuit.constructionParameter, Circuit.constructionShiftedPower,
      Sum.elim_inl, Sum.elim_inr,
      denv_power, denv_variable, denv_parameter, denv_shiftedPower,
      Fin.isValue]
    try simp only [show (0 : Fin 6) = Fin.castAdd 4 (0 : Fin 2) from rfl,
      show (1 : Fin 6) = Fin.castAdd 4 (1 : Fin 2) from rfl,
      show (2 : Fin 6) = Fin.natAdd 2 (0 : Fin 4) from rfl,
      show (3 : Fin 6) = Fin.natAdd 2 (1 : Fin 4) from rfl,
      show (4 : Fin 6) = Fin.natAdd 2 (2 : Fin 4) from rfl,
      show (5 : Fin 6) = Fin.natAdd 2 (3 : Fin 4) from rfl,
      Fin.addCases_left, Fin.addCases_right]
    try simp only [show (0 : Fin 4) = Fin.castAdd 2 (0 : Fin 2) from rfl,
      show (1 : Fin 4) = Fin.castAdd 2 (1 : Fin 2) from rfl,
      show (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) from rfl,
      show (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) from rfl,
      Fin.addCases_left, Fin.addCases_right]
    try simp only [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
      show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
      Fin.addCases_left, Fin.addCases_right]
    try simp only [Circuit.multDepth_add, multDepth_diffSquareAdd,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Circuit.multDepth_input,
      denv_power, denv_variable, denv_parameter]
    omega

/-- Aux-output depths of an ordinary odd step: all six at once. -/
theorem multDepth_tOddMainAux_le (k l : ℕ) (dp : ℕ → ℕ) (dps : ℕ) (hl : 3 ≤ l)
    (hdp : ∀ i, 1 ≤ i → i ≤ l → dp i ≤ i) (hdps : dps ≤ l) :
    (tOddMainAux (R := R) k l).multDepth (denv dp dps) 0 ≤ l + 1 ∧
    (tOddMainAux (R := R) k l).multDepth (denv dp dps) 1 ≤ l + 1 ∧
    (tOddMainAux (R := R) k l).multDepth (denv dp dps) 2 ≤ l ∧
    (tOddMainAux (R := R) k l).multDepth (denv dp dps) 3 ≤ l ∧
    (tOddMainAux (R := R) k l).multDepth (denv dp dps) 4 ≤ l ∧
    (tOddMainAux (R := R) k l).multDepth (denv dp dps) 5 ≤ l := by
  have hq2 : (peelCircuit (R := R) (l - 2)).multDepth (denv dp dps) 0 ≤ l - 2 :=
    multDepth_peelCircuit dp dps (l - 2) (by omega)
      (fun i hi1 hik => hdp i hi1 (by omega))
  have hql : (peelCircuit (R := R) l).multDepth (denv dp dps) 0 ≤ l :=
    multDepth_peelCircuit dp dps l (by omega)
      (fun i hi1 hik => hdp i hi1 (by omega))
  have hql1 : (peelCircuit (R := R) (l - 1)).multDepth (denv dp dps) 0 ≤ l - 1 :=
    multDepth_peelCircuit dp dps (l - 1) (by omega)
      (fun i hi1 hik => hdp i hi1 (by omega))
  have hp1 := hdp 1 (by omega) (by omega)
  have hpl := hdp l (by omega) le_rfl
  have hpl1 := hdp (l - 1) (by omega) (by omega)
  have hpl2 := hdp (l - 2) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [tOddMainAux, tOddMainShiftPair, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Circuit.multDepth_add, Circuit.multDepth_sub,
      Circuit.multDepth_scale,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Circuit.multDepth_input, multDepth_reindexConstructionParameters,
      Circuit.constructionPower,
      Circuit.constructionParameter, Circuit.constructionShiftedPower,
      denv_power, denv_parameter, denv_shiftedPower,
      Fin.isValue]
    try simp only [show (0 : Fin 6) = Fin.castAdd 4 (0 : Fin 2) from rfl,
      show (1 : Fin 6) = Fin.castAdd 4 (1 : Fin 2) from rfl,
      show (2 : Fin 6) = Fin.natAdd 2 (0 : Fin 4) from rfl,
      show (3 : Fin 6) = Fin.natAdd 2 (1 : Fin 4) from rfl,
      show (4 : Fin 6) = Fin.natAdd 2 (2 : Fin 4) from rfl,
      show (5 : Fin 6) = Fin.natAdd 2 (3 : Fin 4) from rfl,
      Fin.addCases_left, Fin.addCases_right]
    try simp only [show (0 : Fin 4) = Fin.castAdd 2 (0 : Fin 2) from rfl,
      show (1 : Fin 4) = Fin.castAdd 2 (1 : Fin 2) from rfl,
      show (2 : Fin 4) = Fin.natAdd 2 (0 : Fin 2) from rfl,
      show (3 : Fin 4) = Fin.natAdd 2 (1 : Fin 2) from rfl,
      Fin.addCases_left, Fin.addCases_right]
    try simp only [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl,
      show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl,
      Fin.addCases_left, Fin.addCases_right]
    try simp only [Circuit.multDepth_add, multDepth_diffSquareAdd,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Circuit.multDepth_input, multDepth_reindexConstructionParameters,
      Fin.addCases_left, Fin.addCases_right,
      denv_power, denv_parameter, denv_shiftedPower]
    omega

end oddBranches

section master

/-- Updating one tower slot with a value below its index preserves the tower
invariant. -/
private theorem update_dp_le {dp : ℕ → ℕ} (hdp : ∀ i, 1 ≤ i → dp i ≤ i)
    {m v : ℕ} (hv : v ≤ m) : ∀ i, 1 ≤ i → Function.update dp m v i ≤ i := by
  intro i hi
  by_cases h : i = m
  · subst h
    rw [Function.update_self]
    exact hv
  · rw [Function.update_of_ne h]
    exact hdp i hi

omit [CommRing R] in
/-- The two `T` base cases return the bare power pair, at the tower depths. -/
private theorem multDepth_powerPairFork_le (l : ℕ) (dp : ℕ → ℕ) (dps : ℕ)
    (hpl : dp l ≤ l) (hdps : dps ≤ l) (j : Fin 2) :
    (Circuit.fork (Circuit.constructionPower l)
        (Circuit.constructionShiftedPower) :
      Circuit R ConstructionInput 2).multDepth (denv dp dps) j ≤ l := by
  rw [Circuit.multDepth_fork]
  match j with
  | 0 =>
    rw [show (0 : Fin 2) = Fin.castAdd 1 (0 : Fin 1) from rfl]
    simp only [Fin.addCases_left, Circuit.constructionPower,
      Circuit.multDepth_input, denv_power]
    omega
  | 1 =>
    rw [show (1 : Fin 2) = Fin.natAdd 1 (0 : Fin 1) from rfl]
    simp only [Fin.addCases_right, Circuit.constructionShiftedPower,
      Circuit.multDepth_input, denv_shiftedPower]
    omega

/-- Recursive depth bound mirroring `tCircuitF` branch for branch: the Lean
form of the paper's spine ledger (`≤ λ + s(k)` unrolled). -/
def tDB : ℕ → ℕ → ℕ → ℕ
  | 0, _, l => l
  | fuel + 1, k, l =>
      if k ≤ 1 then l
      else if k % 2 = 0 then
        if l ≤ 1 then tDB fuel (k / 2) 2
        else tDB fuel (k / 2) (l + 1)
      else if l ≤ 2 then max (max 2 (tDB fuel ((k - 1) / 2) 3) + 1) 2
      else max (max l (tDB fuel ((k - 1) / 2) (l + 1)) + 1) l

omit [CommRing R] in
/-- Depth composition of the shared even base. -/
theorem multDepth_tEvenBaseCircuit (k : ℕ) (inner : Circuit R ConstructionInput 2)
    (dp : ℕ → ℕ) (dps : ℕ) :
    (tEvenBaseCircuit k inner).multDepth (denv dp dps) =
      inner.multDepth
        (denv (Function.update dp 2
            ((tEvenBasePowerPair (R := R) k).multDepth (denv dp dps) 0))
          ((tEvenBasePowerPair (R := R) k).multDepth (denv dp dps) 1)) := by
  rw [tEvenBaseCircuit, Circuit.multDepth_bind, multDepth_recurseWithPowerPair]

omit [CommRing R] in
/-- Depth composition of an ordinary even step. -/
theorem multDepth_tEvenMainCircuit (k l : ℕ) (inner : Circuit R ConstructionInput 2)
    (dp : ℕ → ℕ) (dps : ℕ) :
    (tEvenMainCircuit k l inner).multDepth (denv dp dps) =
      inner.multDepth
        (denv (Function.update dp (l + 1)
            ((tEvenMainPowerPair (R := R) k l).multDepth (denv dp dps) 0))
          ((tEvenMainPowerPair (R := R) k l).multDepth (denv dp dps) 1)) := by
  rw [tEvenMainCircuit, Circuit.multDepth_bind, multDepth_recurseWithPowerPair]

/-- **Height ledger for the compiled `T` recursion**: over a full tower at
depths `dp i ≤ i` and shifted power at depth `≤ l`, both outputs of
`tCircuitF` are bounded by the spine ledger `tDB`. -/
theorem multDepth_tCircuitF_le :
    ∀ fuel k l (dp : ℕ → ℕ) (dps : ℕ), 1 ≤ l →
      (∀ i, 1 ≤ i → dp i ≤ i) → dps ≤ l → ∀ j,
      (tCircuitF (R := R) fuel k l).multDepth (denv dp dps) j ≤ tDB fuel k l := by
  intro fuel
  induction fuel with
  | zero =>
    intro k l dp dps hl hdp hdps j
    exact multDepth_powerPairFork_le l dp dps (hdp l (by omega)) hdps j
  | succ fuel ih =>
    intro k l dp dps hl hdp hdps j
    rcases Nat.lt_or_ge k 2 with hk1 | hk1
    · rw [tCircuitF_succ_le_one _ _ _ (by omega)]
      have hbound : tDB (fuel + 1) k l = l := by
        simp [tDB, if_pos (show k ≤ 1 by omega)]
      rw [hbound]
      exact multDepth_powerPairFork_le l dp dps (hdp l (by omega)) hdps j
    · by_cases heven : k % 2 = 0
      · rcases Nat.lt_or_ge l 2 with hll | hll
        -- shared even base
        · rw [tCircuitF_succ_even_base _ _ _ (by omega) heven (by omega),
            multDepth_tEvenBaseCircuit]
          have hp1 := hdp 1 (by omega)
          rw [multDepth_tEvenBasePowerPair_zero, multDepth_tEvenBasePowerPair_one]
          have hdp' : ∀ i, 1 ≤ i → Function.update dp 2 (dp 1 + 1) i ≤ i :=
            update_dp_le hdp (by omega)
          have hdps' : max (dp 1 + 1) (max dps (dp 1)) ≤ 2 := by omega
          have hbound : tDB (fuel + 1) k l = tDB fuel (k / 2) 2 := by
            simp [tDB, if_neg (by omega : ¬ k ≤ 1), heven, if_pos (show l ≤ 1 by omega)]
          rw [hbound]
          exact ih (k / 2) 2 _ _ (by omega) hdp' hdps' j
        -- ordinary even step
        · rw [tCircuitF_succ_even_main _ _ _ (by omega) heven (by omega),
            multDepth_tEvenMainCircuit]
          have hz := multDepth_tEvenMainPowerPair_zero_le (R := R) k l dp dps
            (by omega) (fun i hi1 hik => hdp i hi1)
          have ho := multDepth_tEvenMainPowerPair_one_le (R := R) k l dp dps
            (by omega) (fun i hi1 hik => hdp i hi1) hdps
          have hdp' : ∀ i, 1 ≤ i →
              Function.update dp (l + 1)
                ((tEvenMainPowerPair (R := R) k l).multDepth (denv dp dps) 0) i
                ≤ i :=
            update_dp_le hdp (by omega)
          have hbound : tDB (fuel + 1) k l = tDB fuel (k / 2) (l + 1) := by
            simp [tDB, if_neg (by omega : ¬ k ≤ 1), heven,
              if_neg (by omega : ¬ l ≤ 1)]
          rw [hbound]
          exact ih (k / 2) (l + 1) _ _ (by omega) hdp' (by omega) j
      · rcases Nat.lt_or_ge l 3 with hll | hll
        -- shared odd base
        · rw [tCircuitF_succ_odd_base _ _ _ (by omega) heven (by omega), tOddBaseCircuit]
          obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩ :=
            multDepth_tOddBaseAux_le (R := R) k dp dps
              (hdp 1 (by omega)) (hdp 2 (by omega)) (by omega)
          have hdp' : ∀ i, 1 ≤ i →
              Function.update dp 3
                ((tOddBaseAux (R := R) k).multDepth (denv dp dps) 0) i ≤ i :=
            update_dp_le hdp (by omega)
          have hinner := ih ((k - 1) / 2) 3 _ _ (by omega) hdp' (by omega)
          have hbound : tDB (fuel + 1) k l
              = max (max 2 (tDB fuel ((k - 1) / 2) 3) + 1) 2 := by
            simp [tDB, if_neg (by omega : ¬ k ≤ 1), heven, if_pos (show l ≤ 2 by omega)]
          rw [hbound]
          match j with
          | 0 =>
            rw [multDepth_finishOdd_zero]
            have h0 := hinner 0
            omega
          | 1 =>
            rw [multDepth_finishOdd_one]
            have h1 := hinner 1
            omega
        -- ordinary odd step
        · rw [tCircuitF_succ_odd_main _ _ _ (by omega) heven (by omega),
            tOddMainCircuit]
          obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5⟩ :=
            multDepth_tOddMainAux_le (R := R) k l dp dps (by omega)
              (fun i hi1 hik => hdp i hi1) hdps
          have hdp' : ∀ i, 1 ≤ i →
              Function.update dp (l + 1)
                ((tOddMainAux (R := R) k l).multDepth (denv dp dps) 0) i ≤ i :=
            update_dp_le hdp (by omega)
          have hinner := ih ((k - 1) / 2) (l + 1) _ _ (by omega) hdp' (by omega)
          have hbound : tDB (fuel + 1) k l
              = max (max l (tDB fuel ((k - 1) / 2) (l + 1)) + 1) l := by
            simp [tDB, if_neg (by omega : ¬ k ≤ 1), heven,
              if_neg (by omega : ¬ l ≤ 2)]
          rw [hbound]
          match j with
          | 0 =>
            rw [multDepth_finishOdd_zero]
            have h0 := hinner 0
            omega
          | 1 =>
            rw [multDepth_finishOdd_one]
            have h1 := hinner 1
            omega

/-- The packaged `tCircuit` form. -/
theorem multDepth_tCircuit_le (k l : ℕ) (dp : ℕ → ℕ) (dps : ℕ) (hl : 1 ≤ l)
    (hdp : ∀ i, 1 ≤ i → dp i ≤ i) (hdps : dps ≤ l) (j : Fin 2) :
    (tCircuit (R := R) k l).multDepth (denv dp dps) j ≤ tDB k k l :=
  multDepth_tCircuitF_le k k l dp dps hl hdp hdps j

/-- One doubling step of the ceiling logarithm. -/
theorem clog_two_double (m : ℕ) (hm : 1 ≤ m) :
    Nat.clog 2 (2 * m) = Nat.clog 2 m + 1 := by
  have harg : (2 * m + 2 - 1) / 2 = m := by omega
  rw [Nat.clog_of_two_le (by omega) (by omega), harg]

/-- Closed form for the spine ledger: `tDB ≤ l + 2⌈log₂ k⌉ + 1` — the Lean
form of the paper's `λ + s(k) ≤ 2λ` absorption. -/
theorem tDB_le :
    ∀ fuel k l, 1 ≤ l → tDB fuel k l ≤ max l 2 + 2 * Nat.clog 2 k + 1 := by
  intro fuel
  induction fuel with
  | zero => intro k l hl; simp only [tDB]; omega
  | succ fuel ih =>
    intro k l hl
    by_cases hk1 : k ≤ 1
    · simp only [tDB, if_pos hk1]
      omega
    · have hk2 : 2 ≤ k := by omega
      have hclog : Nat.clog 2 k = Nat.clog 2 ((k + 1) / 2) + 1 := by
        rw [Nat.clog_of_two_le (by omega) hk2, show k + 2 - 1 = k + 1 from rfl]
      have hhalf : Nat.clog 2 (k / 2) ≤ Nat.clog 2 ((k + 1) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      have hhalf' : Nat.clog 2 ((k - 1) / 2) ≤ Nat.clog 2 ((k + 1) / 2) :=
        Nat.clog_mono_right 2 (by omega)
      by_cases heven : k % 2 = 0
      · by_cases hll : l ≤ 1
        · have h := ih (k / 2) 2 (by omega)
          simp only [tDB, if_neg hk1, heven, if_pos hll, if_true]
          omega
        · have h := ih (k / 2) (l + 1) (by omega)
          simp only [tDB, if_neg hk1, heven, if_neg hll, if_true]
          omega
      · by_cases hll : l ≤ 2
        · have h := ih ((k - 1) / 2) 3 (by omega)
          simp only [tDB, if_neg hk1, heven, if_pos hll, if_false]
          omega
        · have h := ih ((k - 1) / 2) (l + 1) (by omega)
          simp only [tDB, if_neg hk1, heven, if_neg hll, if_false]
          omega

end master

end FastPoly.Height
