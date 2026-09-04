import FastPoly.Cost.OddGadgetCrownBundle
import FastPoly.Cost.RealizationOuterSequential
import FastPoly.Cost.RealizedOddGadget

/-!
# Master-facing realized `8k+3` constructor

This wrapper packages the exact three-stage dataflow:

1. bind the smaller pair once;
2. compute and retain `(Q_{4k+1},H₄')`;
3. compute the final odd gadget from `(H₂,H₄')`;
4. apply the two outer square gates.

The resulting type is the interface consumed by the strong induction in `Main.lean`.
-/

namespace FastPoly.Cost.Outer

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

/-- Compose a smaller realized pair with the crown bundle and one gadget using the
crown's new quartic. -/
noncomputable def eightThreeFromGadget
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old : A[X]} {sourceM d : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (k : ℕ) (hk : 1 ≤ k) (secondOffset thirdOffset aIndex alphaIndex : ℕ)
    (third : RealizedOddGadget (R := R) H₂
      (OddGadget.q4BundleOutput H₂ (fun i => θ (secondOffset + i)) k 1)
      (fun i => θ (thirdOffset + i)) d) :
    JointPairRealization (R := R) θ
      ((OddGadget.q4BundleOutput H₂ (fun i => θ (secondOffset + i)) k 0) ^ 2 -
        S₁ ^ 2 + third.Q)
      (((OddGadget.q4BundleOutput H₂ (fun i => θ (secondOffset + i)) k 0) +
          C (θ aIndex)) ^ 2 - St₁ ^ 2 + C (θ alphaIndex))
      H₂ (OddGadget.q4BundleOutput H₂ (fun i => θ (secondOffset + i)) k 1)
      (sourceM + 2 * k + d / 2 + 2) :=
  let second := OddGadget.BundleRealization.relative source
    (OddGadget.q4BundleRealized (R := R) (H₄ := H₄old) hH₂m hH₂d
      (fun i => θ (secondOffset + i)) k hk)
  let stagedThird := OddGadget.Realization.afterBundle source second
    third.realization
  let realized := eightThreeSequentialRealized source second stagedThird
    aIndex alphaIndex
  { circuit := eightThreeSequentialCircuit source second stagedThird
      aIndex alphaIndex
    eval₁ := by
      have h := realized.eval₁
      simpa only [pow_two] using h
    eval₂ := by
      have h := realized.eval₂
      simpa only [pow_two] using h
    evalH₂ := realized.evalH₂
    evalH₄ := realized.evalH₄
    multiplication_count := realized.multiplication_count }

/-- Master-facing height ledger of the composed `8k+3` step. -/
theorem multDepth_eightThreeFromGadget_le
    {θ : ℕ → A} {S₁ St₁ H₂ H₄old : A[X]} {sourceM d : ℕ}
    (source : JointPairRealization (R := R) θ S₁ St₁ H₂ H₄old sourceM)
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (k : ℕ) (hk : 1 ≤ k) (secondOffset thirdOffset aIndex alphaIndex : ℕ)
    (third : RealizedOddGadget (R := R) H₂
      (OddGadget.q4BundleOutput H₂ (fun i => θ (secondOffset + i)) k 1)
      (fun i => θ (thirdOffset + i)) d)
    (hd : d % 2 = 1) (D : ℕ)
    (hs0 : source.circuit.multDepth (fun _ => 0) 0 ≤ D)
    (hs1 : source.circuit.multDepth (fun _ => 0) 1 ≤ D)
    (hs2 : source.circuit.multDepth (fun _ => 0) 2 ≤ 1)
    (hs3 : source.circuit.multDepth (fun _ => 0) 3 ≤ 2) :
    (((eightThreeFromGadget source hH₂m hH₂d k hk secondOffset thirdOffset
        aIndex alphaIndex third).circuit.multDepth (fun _ => 0) 0
      ≤ max (max (2 * Nat.clog 2 (2 * (2 * k) + 1) + 1) D + 1)
          (2 * Nat.clog 2 d + 1)) ∧
      ((eightThreeFromGadget source hH₂m hH₂d k hk secondOffset thirdOffset
        aIndex alphaIndex third).circuit.multDepth (fun _ => 0) 1
      ≤ max (max (2 * Nat.clog 2 (2 * (2 * k) + 1) + 1) D + 1)
          (2 * Nat.clog 2 d + 1)) ∧
      ((eightThreeFromGadget source hH₂m hH₂d k hk secondOffset thirdOffset
        aIndex alphaIndex third).circuit.multDepth (fun _ => 0) 2 ≤ 1) ∧
      ((eightThreeFromGadget source hH₂m hH₂d k hk secondOffset thirdOffset
        aIndex alphaIndex third).circuit.multDepth (fun _ => 0) 3 ≤ 2)) := by
  have hq := OddGadget.multDepth_q4BundleCircuit_le (R := R) k hk
  have hsecond0 : (OddGadget.relativeCircuit
      (OddGadget.q4BundleCircuit (R := R) k) secondOffset).multDepth
      (Sum.elim (fun _ : PolyInput => 0)
        (source.circuit.multDepth (fun _ => 0))) 0
      ≤ 2 * Nat.clog 2 (2 * (2 * k) + 1) + 1 :=
    (OddGadget.multDepth_relativeCircuit_le _ secondOffset
      (source.circuit.multDepth (fun _ => 0)) hs2 hs3 0).trans hq.1
  have hsecond1 : (OddGadget.relativeCircuit
      (OddGadget.q4BundleCircuit (R := R) k) secondOffset).multDepth
      (Sum.elim (fun _ : PolyInput => 0)
        (source.circuit.multDepth (fun _ => 0))) 1
      ≤ 2 :=
    (OddGadget.multDepth_relativeCircuit_le _ secondOffset
      (source.circuit.multDepth (fun _ => 0)) hs2 hs3 1).trans hq.2
  have hthird : (OddGadget.afterBundleCircuit third.realization.circuit
      thirdOffset).multDepth
      (Sum.elim (Sum.elim (fun _ : PolyInput => 0)
        (source.circuit.multDepth (fun _ => 0)))
        ((OddGadget.relativeCircuit (OddGadget.q4BundleCircuit (R := R) k)
          secondOffset).multDepth (Sum.elim (fun _ : PolyInput => 0)
            (source.circuit.multDepth (fun _ => 0))))) 0
      ≤ 2 * Nat.clog 2 d + 1 := by
    have h := (OddGadget.multDepth_afterBundleCircuit_le _ thirdOffset
      (source.circuit.multDepth (fun _ => 0)) _ hs2 hsecond1).trans
      third.realization.depth_le
    rwa [show 2 * (d / 2) + 1 = d from by omega] at h
  exact multDepth_eightThreeSequentialCircuit_le source _ _ aIndex alphaIndex
    _ _ _ hs0 hs1 hs2 hsecond0 hsecond1 hthird

end FastPoly.Cost.Outer
