import Mathlib.Tactic.NormNum.NatLog
import FastPoly.Height.TCircuitDepth
import FastPoly.Cost.PowerTowerCircuit
import FastPoly.Cost.Instantiate

/-!
# Shared depth bounds for the quadratic--quartic towers

Both crown-style producers compute the recorded quadratic with one product and the
recorded quartic with one further difference-of-squares shell, so over inputs of
depth zero their outputs sit at depths `(1,2,2,0)`.  These are the base facts of
every realization-level height ledger.
-/

namespace FastPoly.Height

open FastPoly.Cost

variable {R : Type*} [CommRing R] {ι : Type*}

theorem multDepth_quadraticQuartic_le
    (x b c a e rho : Circuit R ι 1) (env : ι → ℕ)
    (hx : x.multDepth env 0 = 0) (hb : b.multDepth env 0 = 0)
    (hc : c.multDepth env 0 = 0) (ha : a.multDepth env 0 = 0)
    (he : e.multDepth env 0 = 0) (hrho : rho.multDepth env 0 = 0) :
    ((Circuit.quadraticQuartic x b c a e rho).multDepth env 0 ≤ 1) ∧
      ((Circuit.quadraticQuartic x b c a e rho).multDepth env 1 ≤ 2) ∧
      ((Circuit.quadraticQuartic x b c a e rho).multDepth env 2 ≤ 2) ∧
      ((Circuit.quadraticQuartic x b c a e rho).multDepth env 3 ≤ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 3 (0 : Fin 1) from rfl]
    simp only [Circuit.quadraticQuartic, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_left,
      Circuit.priorOutput, Circuit.multDepth_input, Circuit.multDepth_add,
      Circuit.multDepth_mul, Circuit.multDepth_liftLeft,
      Circuit.multDepth_rightInput, Sum.elim_inl, Sum.elim_inr, hx, hb, hc]
    omega
  · rw [show (1 : Fin 4) = Fin.natAdd 1 (Fin.castAdd 2 (0 : Fin 1)) from rfl]
    simp only [Circuit.quadraticQuartic, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_left, Fin.addCases_right,
      Height.multDepth_diffSquareAdd, Circuit.priorOutput,
      Circuit.multDepth_input, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Sum.elim_inl, Sum.elim_inr, hx, hb, hc, ha, he]
    omega
  · rw [show (2 : Fin 4) = Fin.natAdd 1 (Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1)))
      from rfl]
    simp only [Circuit.quadraticQuartic, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_left, Fin.addCases_right,
      Height.multDepth_diffSquareAdd, Circuit.priorOutput,
      Circuit.multDepth_input, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Sum.elim_inl, Sum.elim_inr, hx, hb, hc, ha, he, hrho]
    omega
  · rw [show (3 : Fin 4) = Fin.natAdd 1 (Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1)))
      from rfl]
    simp only [Circuit.quadraticQuartic, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_right,
      Circuit.multDepth_const]
    omega

theorem multDepth_quadraticQuarticUnshifted_le
    (x b c a e : Circuit R ι 1) (env : ι → ℕ)
    (hx : x.multDepth env 0 = 0) (hb : b.multDepth env 0 = 0)
    (hc : c.multDepth env 0 = 0) (ha : a.multDepth env 0 = 0)
    (he : e.multDepth env 0 = 0) :
    ((Circuit.quadraticQuarticUnshifted x b c a e).multDepth env 0 ≤ 1) ∧
      ((Circuit.quadraticQuarticUnshifted x b c a e).multDepth env 1 ≤ 2) ∧
      ((Circuit.quadraticQuarticUnshifted x b c a e).multDepth env 2 ≤ 2) ∧
      ((Circuit.quadraticQuarticUnshifted x b c a e).multDepth env 3 ≤ 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show (0 : Fin 4) = Fin.castAdd 3 (0 : Fin 1) from rfl]
    simp only [Circuit.quadraticQuarticUnshifted, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_left,
      Circuit.priorOutput, Circuit.multDepth_input, Circuit.multDepth_add,
      Circuit.multDepth_mul, Sum.elim_inl, Sum.elim_inr, hx, hb, hc]
    omega
  · rw [show (1 : Fin 4) = Fin.natAdd 1 (Fin.castAdd 2 (0 : Fin 1)) from rfl]
    simp only [Circuit.quadraticQuarticUnshifted, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_left, Fin.addCases_right,
      Height.multDepth_diffSquareAdd, Circuit.priorOutput,
      Circuit.multDepth_input, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Sum.elim_inl, Sum.elim_inr, hx, hb, hc, ha, he]
    omega
  · rw [show (2 : Fin 4) = Fin.natAdd 1 (Fin.natAdd 1 (Fin.castAdd 1 (0 : Fin 1)))
      from rfl]
    simp only [Circuit.quadraticQuarticUnshifted, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_left, Fin.addCases_right,
      Height.multDepth_diffSquareAdd, Circuit.priorOutput,
      Circuit.multDepth_input, Circuit.multDepth_add, Circuit.multDepth_mul,
      Circuit.multDepth_liftLeft, Circuit.multDepth_rightInput,
      Sum.elim_inl, Sum.elim_inr, hx, hb, hc, ha, he]
    omega
  · rw [show (3 : Fin 4) = Fin.natAdd 1 (Fin.natAdd 1 (Fin.natAdd 1 (0 : Fin 1)))
      from rfl]
    simp only [Circuit.quadraticQuarticUnshifted, Circuit.multDepth_bind,
      Circuit.multDepth_fork, Fin.addCases_right,
      Circuit.multDepth_const]
    omega

/-- Any construction wiring whose power slots respect the canonical gadget depths
yields a depth environment below `gadgetDepthEnv`; combined with
`Circuit.multDepth_mono` this prices every instantiated local compiler. -/
theorem wiringDepth_le {m : ℕ} (w : ConstructionWiring m) (dvals : Fin m → ℕ)
    (hpow : ∀ i, Sum.elim (fun _ => (0 : ℕ)) dvals (w.power i) ≤ gadgetDp i)
    (hshift : Sum.elim (fun _ => (0 : ℕ)) dvals w.shiftedPower ≤ 2)
    (hsrc : ∀ i : Fin 2, Sum.elim (fun _ => (0 : ℕ)) dvals (w.source i) ≤ 0) :
    ∀ input, (Sum.elim (fun _ => (0 : ℕ)) dvals ∘ w.label) input ≤
      gadgetDepthEnv input := by
  intro input
  cases input with
  | «variable» => exact le_rfl
  | power i => exact hpow i
  | shiftedPower => exact hshift
  | parameter i => exact le_rfl
  | source i => exact hsrc i

/-- Small ceiling-log values used by the special-degree height ledgers. -/
theorem clog_two_four : Nat.clog 2 4 = 2 := by norm_num

theorem clog_two_sixteen : Nat.clog 2 16 = 4 := by norm_num

theorem clog_two_seventeen : Nat.clog 2 17 = 5 := by norm_num

end FastPoly.Height
