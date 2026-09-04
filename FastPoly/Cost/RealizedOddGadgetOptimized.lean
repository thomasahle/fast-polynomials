import FastPoly.Cost.Additions.Gadgets
import FastPoly.Cost.OddGadgetBarredAdditions
import FastPoly.Cost.OddGadgetKnownOptimized
import FastPoly.Cost.RealizedOddGadgetKnown

/-!
# Addition-certified realized odd gadgets

The optimized crown and known-powers circuits compute the same polynomials as the
public decoder-facing odd gadgets.  This module joins those literal circuits to the
existing decoder theorems and records their additions on the very realization being
packaged.  The barred branch already has the selected sharing topology, so the same
package simply attaches its literal circuit count.
-/

namespace FastPoly.Cost

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

namespace OddGadget.Q4Optimized

/-- Forget the retained quartic output through a wire-only projection.  The producer
is still evaluated exactly once, so this does not alter either arithmetic ledger. -/
def singleCircuit (k : ℕ) : Circuit R ConstructionInput 1 :=
  .bind (circuit k)
    (Circuit.rightInput (R := R) (ι := ConstructionInput) (0 : Fin 2))

@[simp] theorem eval_singleCircuit {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (theta : ℕ → A) (k : ℕ) :
    (singleCircuit (R := R) k).eval (env H₂ H₄ theta) 0 =
      q4BundleOutput H₂ theta k 0 := by
  rw [singleCircuit, Circuit.eval_bind, Circuit.eval_rightInput,
    eval_circuit_zero hH₂m hH₂d theta k]

/-- The gate-free projection preserves the optimized bundle's addition count. -/
theorem singleCircuit_additions (k : ℕ) (hk : 1 ≤ k) :
    (singleCircuit (R := R) k).gates.additions = tAdd (2 * k) 1 + 3 := by
  simp only [singleCircuit, Circuit.gates_bind, Circuit.gates_rightInput,
    GateCount.add_additions, GateCount.zero_additions, Nat.add_zero]
  exact circuit_additions k hk

/-- The gate-free projection preserves the optimized bundle's multiplication count. -/
theorem singleCircuit_multiplications (k : ℕ) (hk : 1 ≤ k) :
    (singleCircuit (R := R) k).gates.multiplications = 2 * k := by
  simp only [singleCircuit, Circuit.gates_bind, Circuit.gates_rightInput,
    GateCount.add_multiplications, GateCount.zero_multiplications, Nat.add_zero]
  exact circuit_multiplications k hk

/-- The selected q4 output keeps the ordinary one-output gadget height bound. -/
theorem multDepth_singleCircuit_le (k : ℕ) (hk : 1 ≤ k) :
    (singleCircuit (R := R) k).multDepth Height.gadgetDepthEnv 0 ≤
      2 * Nat.clog 2 (2 * (2 * k) + 1) + 1 := by
  have h := (multDepth_circuit_le (R := R) k hk).1
  simpa only [singleCircuit, Circuit.multDepth_bind,
    Circuit.multDepth_rightInput] using h

/-- One-output realization obtained from the optimized retained-quartic bundle. -/
def singleRealized {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta (q4BundleOutput H₂ theta k 0) (2 * k) where
  circuit := singleCircuit k
  eval_eq := eval_singleCircuit hH₂m hH₂d theta k
  multiplication_count := singleCircuit_multiplications k hk
  depth_le := multDepth_singleCircuit_le k hk

/-- Decoder-facing form of the optimized one-output q4 realization. -/
def decoderRealized {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta
      (FastPoly.q4k1 H₂ (theta 1) (theta 4) (theta 2) (theta 3) (theta 0)
        k (fun i => theta (5 + i))) ((4 * k + 1) / 2) where
  circuit := singleCircuit k
  eval_eq := by
    simpa only [q4BundleOutput, twoOutputs_zero] using
      eval_singleCircuit (R := R) (H₄ := H₄) hH₂m hH₂d theta k
  multiplication_count := by
    rw [singleCircuit_multiplications k hk]
    omega
  depth_le := by
    simpa only [show (4 * k + 1) / 2 = 2 * k by omega] using
      multDepth_singleCircuit_le (R := R) k hk

/-- The q4 decoder-facing helper stores the projected optimized circuit literally. -/
@[simp] theorem decoderRealized_circuit {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    (decoderRealized (R := R) (H₄ := H₄) hH₂m hH₂d theta k hk).circuit =
      singleCircuit k := by
  simp only [decoderRealized]

end OddGadget.Q4Optimized

namespace OddGadget.KnownOptimized

/-- Decoder-facing form of the optimized known-powers realization. -/
def decoderRealized (H₂ H₄ : A[X]) (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta (FastPoly.knownGadget H₂ H₄ k theta)
      ((8 * k + 3) / 2) where
  circuit := circuit k
  eval_eq := (eval_circuit H₂ H₄ theta k).trans
    (OddGadget.knownValue_eq_knownGadget H₂ H₄ k theta)
  multiplication_count := by
    rw [circuit_multiplications k hk]
    omega
  depth_le := by
    simpa only [show (8 * k + 3) / 2 = 4 * k + 1 by omega] using
      multDepth_circuit_le (R := R) k hk

omit [Nontrivial A] in
/-- The known decoder-facing helper stores the optimized circuit literally. -/
@[simp] theorem decoderRealized_circuit (H₂ H₄ : A[X])
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    (decoderRealized (R := R) H₂ H₄ theta k hk).circuit = circuit k := by
  simp only [decoderRealized]

end OddGadget.KnownOptimized

namespace OddGadget.BarredAdditions

/-- Decoder-facing form of the existing exceptional degree-fifteen realization. -/
noncomputable def oneDecoderRealized {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (theta : ℕ → A) :
    Realization (R := R) H₂ H₄ theta
      (FastPoly.BarQ15.barQ15 (H₂.coeff 0) (H₂.coeff 1)
        (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) theta)
      (15 / 2) := by
  let source := OddGadget.barredOneRealized (R := R)
    hH₂m hH₂d hH₄m hH₄d theta
  exact
    { circuit := OddGadget.barredCircuit 1
      eval_eq := source.eval_eq
      multiplication_count := by
        rw [OddGadget.barredCircuit_multiplications 1 (by omega)]
      depth_le := by
        simpa only [show 15 / 2 = 7 by omega] using source.depth_le }

omit [Nontrivial A] in
/-- The exceptional decoder-facing helper stores the uniform barred circuit at one. -/
@[simp] theorem oneDecoderRealized_circuit {H₂ H₄ : A[X]}
    (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (theta : ℕ → A) :
    (oneDecoderRealized (R := R) hH₂m hH₂d hH₄m hH₄d theta).circuit =
      OddGadget.barredCircuit 1 := by
  rfl

/-- Decoder-facing form of the existing uniform barred realization. -/
def generalDecoderRealized (H₂ H₄ : A[X]) (theta : ℕ → A)
    (k : ℕ) (hk : 1 ≤ k) :
    Realization (R := R) H₂ H₄ theta (FastPoly.BarQGeneral.gadget H₂ H₄ k theta)
      ((8 * k + 7) / 2) := by
  let source := OddGadget.barredRealized (R := R) H₂ H₄ theta k hk
  exact
    { circuit := OddGadget.barredCircuit k
      eval_eq := source.eval_eq
      multiplication_count := by
        rw [OddGadget.barredCircuit_multiplications k hk]
        omega
      depth_le := by
        simpa only [show (8 * k + 7) / 2 = 4 * k + 3 by omega] using
          source.depth_le }

omit [Nontrivial A] in
/-- The uniform decoder-facing helper stores the existing barred circuit literally. -/
@[simp] theorem generalDecoderRealized_circuit (H₂ H₄ : A[X])
    (theta : ℕ → A) (k : ℕ) (hk : 1 ≤ k) :
    (generalDecoderRealized (R := R) H₂ H₄ theta k hk).circuit =
      OddGadget.barredCircuit k := by
  simp only [generalDecoderRealized]

end OddGadget.BarredAdditions

/-- A decoder-facing realized odd gadget whose selected addition ledger is proved for
the exact circuit stored in its realization. -/
structure AdditionRealizedOddGadget (H₂ H₄ : A[X]) (theta : ℕ → A)
    (d additions : ℕ) where
  Q : A[X]
  monic : Q.Monic
  natDegree : Q.natDegree = d
  recover : ∀ V : Subalgebra R A,
    (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
      (∀ j, Q.coeff j ∈ V) → ∀ t, t < d → theta t ∈ V
  realization : OddGadget.Realization (R := R) H₂ H₄ theta Q (d / 2)
  addition_count : realization.circuit.gates.additions = additions
  ledger : GadgetAddCost d additions

namespace AdditionRealizedOddGadget

/-- Forget only the addition certificate, retaining the exact decoder and circuit. -/
def toRealized {H₂ H₄ : A[X]} {theta : ℕ → A} {d additions : ℕ}
    (gadget : AdditionRealizedOddGadget (R := R) H₂ H₄ theta d additions) :
    RealizedOddGadget (R := R) H₂ H₄ theta d where
  Q := gadget.Q
  monic := gadget.monic
  natDegree := gadget.natDegree
  recover := gadget.recover
  realization := gadget.realization

omit [Nontrivial A] in
/-- The conversion to `RealizedOddGadget` preserves the certified literal circuit. -/
theorem toRealized_additions {H₂ H₄ : A[X]} {theta : ℕ → A} {d additions : ℕ}
    (gadget : AdditionRealizedOddGadget (R := R) H₂ H₄ theta d additions) :
    gadget.toRealized.realization.circuit.gates.additions = additions :=
  gadget.addition_count

/-- Addition-certified optimized `4k+1` branch. -/
noncomputable def q4 {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (k : ℕ) (hk : 1 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    (h2 : IsUnit (2 : R)) (theta : ℕ → A) :
    AdditionRealizedOddGadget (R := R) H₂ H₄ theta
      (4 * k + 1) (tAdd (2 * k) 1 + 3) := by
  obtain ⟨hQm, hQd⟩ := FastPoly.q4k1_good (α := fun t => theta (5 + t)) hk
    (theta 1) (theta 4) (theta 2) (theta 3) (theta 0)
  exact
    { Q := FastPoly.q4k1 H₂ (theta 1) (theta 4) (theta 2) (theta 3)
        (theta 0) k (fun t => theta (5 + t))
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V _ hQV t ht
        obtain ⟨⟨hbeta, hgamma, ha, he, hrho⟩, -, halpha⟩ :=
          FastPoly.q4k1_decodable (α := fun u => theta (5 + u)) hk hadm h2
            hH₂m hH₂d (theta 1) (theta 4) (theta 2) (theta 3) (theta 0)
            V hH₂V hQV
        rcases Nat.lt_or_ge t 5 with ht5 | h5
        · rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 from by omega)
            with rfl | rfl | rfl | rfl | rfl
          · exact hbeta
          · exact hgamma
          · exact ha
          · exact he
          · exact hrho
        · have h := halpha (t - 5) (by omega)
          rwa [show 5 + (t - 5) = t from by omega] at h
      realization := OddGadget.Q4Optimized.decoderRealized
        (R := R) (H₄ := H₄) hH₂m hH₂d theta k hk
      addition_count := by
        rw [OddGadget.Q4Optimized.decoderRealized_circuit]
        exact OddGadget.Q4Optimized.singleCircuit_additions k hk
      ledger := GadgetAddCost.fourKPlusOne k hk }

/-- Addition-certified optimized `8k+3` branch. -/
noncomputable def known {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (k : ℕ) (hk : 1 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    (theta : ℕ → A) :
    AdditionRealizedOddGadget (R := R) H₂ H₄ theta
      (8 * k + 3) (tAdd (2 * k) 2 + 9) := by
  obtain ⟨hQm, hQd⟩ := FastPoly.knownGadget_good
    hH₂m hH₂d hH₄m hH₄d hk theta
  exact
    { Q := FastPoly.knownGadget H₂ H₄ k theta
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V hH₄V hQV
        exact FastPoly.knownGadget_decodable hk hadm hH₂m hH₂d hH₄m hH₄d
          theta V hH₂V hH₄V hQV
      realization := OddGadget.KnownOptimized.decoderRealized
        (R := R) H₂ H₄ theta k hk
      addition_count := by
        rw [OddGadget.KnownOptimized.decoderRealized_circuit]
        exact OddGadget.KnownOptimized.circuit_additions k
      ledger := GadgetAddCost.eightKPlusThree k hk }

/-- Addition-certified exceptional degree-fifteen barred branch. -/
noncomputable def barredOne {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (theta : ℕ → A) :
    AdditionRealizedOddGadget (R := R) H₂ H₄ theta 15 (tAdd 1 3 + 19) := by
  let Q := FastPoly.BarQ15.barQ15 (H₂.coeff 0) (H₂.coeff 1)
    (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) theta
  obtain ⟨hQm, hQd⟩ := FastPoly.BarQ15.barQ15_good (A := A)
    (H₂.coeff 0) (H₂.coeff 1)
    (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) theta
  exact
    { Q := Q
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V hH₄V hQV
        have hraw := FastPoly.BarQ15.barQ15_recover (R := R) V
          (H₂.coeff 0) (H₂.coeff 1)
          (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) theta
          (hH₂V 0) (hH₂V 1) (hH₄V 0) (hH₄V 1) (hH₄V 2) (hH₄V 3)
        have hcollapse : FastPoly.BarQ15.barQ15Alg V
            (H₂.coeff 0) (H₂.coeff 1)
            (H₄.coeff 0) (H₄.coeff 1) (H₄.coeff 2) (H₄.coeff 3) theta ≤ V := by
          rw [FastPoly.BarQ15.barQ15Alg]
          exact sup_le le_rfl (adjoin_le (by
            rintro _ ⟨j, rfl⟩
            exact hQV j))
        exact fun t ht => hcollapse (hraw t ht)
      realization := by
        simpa only [Q] using OddGadget.BarredAdditions.oneDecoderRealized
          (R := R) hH₂m hH₂d hH₄m hH₄d theta
      addition_count := by
        simp only [id_eq]
        rw [OddGadget.BarredAdditions.oneDecoderRealized_circuit]
        exact OddGadget.BarredAdditions.circuit_additions 1
      ledger := by
        simpa only using GadgetAddCost.eightKPlusSeven 1 (by omega) }

/-- Addition-certified uniform `8k+7` barred branch. -/
noncomputable def barredGeneral {H₂ H₄ : A[X]} (hH₂m : H₂.Monic)
    (hH₂d : H₂.natDegree = 2) (hH₄m : H₄.Monic)
    (hH₄d : H₄.natDegree = 4) (k : ℕ) (hk : 2 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ k → IsUnit (((n : ℕ) : ℤ) : R))
    (theta : ℕ → A) :
    AdditionRealizedOddGadget (R := R) H₂ H₄ theta
      (8 * k + 7) (tAdd k 3 + 19) := by
  obtain ⟨hQm, hQd⟩ := FastPoly.BarQGeneral.gadget_good
    hH₂m hH₂d hH₄m hH₄d k (by omega) theta
  exact
    { Q := FastPoly.BarQGeneral.gadget H₂ H₄ k theta
      monic := hQm
      natDegree := hQd
      recover := by
        intro V hH₂V hH₄V hQV
        exact FastPoly.BarQGeneral.gadget_recover hH₂m hH₂d hH₄m hH₄d
          k hk theta hadm hH₂V hH₄V hQV
      realization := OddGadget.BarredAdditions.generalDecoderRealized
        (R := R) H₂ H₄ theta k (by omega)
      addition_count := by
        rw [OddGadget.BarredAdditions.generalDecoderRealized_circuit]
        exact OddGadget.BarredAdditions.circuit_additions k
      ledger := GadgetAddCost.eightKPlusSeven k (by omega) }

end AdditionRealizedOddGadget

end FastPoly.Cost
