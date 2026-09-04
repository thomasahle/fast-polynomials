import FastPoly.Cost.RealizationP27Optimized

/-!
# Height certificate for the addition-optimal degree-27 realization

The optimized realization replaces only the quadratic/quartic tower and the local
`T_{3,4}` producer.  Its two pair outputs are bounded by the circuit's thirteen
multiplications, while its recorded quadratic and quartic remain exposed at depths one
and two.  This is the height payload needed to select the 43-addition witness in the
master induction.
-/

namespace FastPoly.Cost

universe u

namespace TwentySevenOptimized

variable {R : Type u} [CommRing R]

/-- Height ledger of the addition-optimal degree-27 circuit. -/
theorem multDepth_circuit_le :
    ((circuit (R := R)).multDepth (fun _ => 0) 0 ≤ 2 * Nat.clog 2 27 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 1 ≤ 2 * Nat.clog 2 27 + 3) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((circuit (R := R)).multDepth (fun _ => 0) 3 ≤ 2) := by
  have hm : ∀ j, (circuit (R := R)).multDepth (fun _ => 0) j ≤ 13 := by
    intro j
    have h := Circuit.multDepth_le_multiplications (circuit (R := R))
      (env := fun _ => 0) (d := 0) (fun _ => le_rfl) j
    rwa [circuit_multiplications, Nat.add_zero] at h
  have hc : 5 ≤ Nat.clog 2 27 := by
    have h17 := Height.clog_two_seventeen
    have hmono := Nat.clog_mono_right 2 (show (17 : ℕ) ≤ 27 by omega)
    omega
  refine ⟨(hm 0).trans (by omega), (hm 1).trans (by omega), ?_, ?_⟩
  · change 1 ≤ 1
    exact le_rfl
  · change 2 ≤ 2
    exact le_rfl

end TwentySevenOptimized

end FastPoly.Cost
