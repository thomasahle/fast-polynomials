import FastPoly.Cost.AdditionPairEightThree
import FastPoly.Cost.AdditionPolynomialRealization
import FastPoly.Cost.RealizedOddGadgetAdditionDispatch
import FastPoly.Section5.FourKPlusOne
import FastPoly.Examples.P15
import FastPoly.Examples.P27Full
import FastPoly.Examples.P31Full

/-!
# Same-program addition capstone

`Cost.Additions.Final` proves the manuscript's addition ledgers as a recurrence over
`ℕ`.  The realization files attach that ledger to fixed circuits: the base pairs
(`AdditionJointPairProgram`), the recursive `8k+3`/`8k+7` steps
(`AdditionJointPairRealization.eightThree`/`.eightSeven`), the certified odd gadgets
(`AdditionRealizedOddGadget.dispatch`), and the complete-polynomial combinators
(`AdditionPolynomialRealization.ofJointPair`/`.evenLift`).  This file closes the loop:
for every odd degree there is one fixed pair program carrying its semantics and its
exact addition count (`additionJointPairRealization_exists`), for every positive degree
there is one fixed complete-polynomial program doing the same
(`additionPolynomialRealization_exists`), and `construction_additions_checked` states
the manuscript's two addition bounds — `A_n ≤ 2n` and
`A_n ≤ 5n/4 + 6⌈log₂ n⌉² + 1` — for the literal `additions` count of that program,
together with its multiplication count `⌊n/2⌋ + 1`.

The residue dispatch is the one of the master theorem `odd_realizable_pairs`
(`FastPoly/Main.lean`): base degrees `3, 15, 27, 31`, the `4k+1` crown, and the
recursive `8k+3` and `8k+7` steps whose source pair has degree `2k+1`.
-/

namespace FastPoly.Cost

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

/-- **Same-program pair existence.**  Every admissible odd degree `n ≥ 3`, `n ≠ 7`, has a
fixed addition-certified pair program realizing a pair `(T₁, T₂)` with its retained
quadratic `H₂` (monic of degree two) and, from degree five on, a retained quartic `H₄`
(monic of degree four).  The additions of that program are the selected `PairAddCost`
ledger by construction. -/
theorem additionJointPairRealization_exists : ∀ n : ℕ, n % 2 = 1 → 3 ≤ n → n ≠ 7 →
    (∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) →
    ∀ θ : ℕ → A,
    ∃ (T₁ T₂ H₂ H₄ : A[X]) (additions : ℕ),
      H₂.Monic ∧ H₂.natDegree = 2 ∧
      (5 ≤ n → H₄.Monic ∧ H₄.natDegree = 4) ∧
      Nonempty (AdditionJointPairRealization R θ T₁ T₂ H₂ H₄ n additions) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hodd hn3 hn7 hadm θ
  rcases (show n = 3 ∨ (n % 4 = 1 ∧ 5 ≤ n) ∨ n = 15 ∨ n = 27 ∨ n = 31
      ∨ (n % 8 = 3 ∧ 11 ≤ n ∧ n ≠ 27)
      ∨ (n % 8 = 7 ∧ 23 ≤ n ∧ n ≠ 31) from by omega)
    with rfl | ⟨h41, h5⟩ | rfl | rfl | rfl | ⟨h83, h11, h27⟩ | ⟨h87, h23, h31⟩
  -- ## base `n = 3`
  · exact ⟨Three.T₁ θ, Three.T₂ θ, Three.H₂ θ, 0, 3,
      (crownH2_monic (A := A) (b := θ 2) (c := θ 1)).1,
      (crownH2_monic (A := A) (b := θ 2) (c := θ 1)).2,
      fun h5 => absurd h5 (by omega),
      ⟨⟨AdditionJointPairProgram.three R, AdditionJointPairProgram.three_realizesAt θ⟩⟩⟩
  -- ## `n ≡ 1 (mod 4)`, `n ≥ 5`: the crown branch
  · obtain ⟨k, hk1, rfl⟩ : ∃ k, 1 ≤ k ∧ n = 4 * k + 1 := ⟨n / 4, by omega⟩
    exact ⟨_, _, crownH2 (θ 0) (θ 1), crownH4 (θ 0) (θ 1) (θ 2) (θ 3),
      tAdd (2 * k) 1 + 2,
      (crownH2_monic).1, (crownH2_monic).2,
      fun _ => ⟨(crownH4_monic).1, (crownH4_monic).2⟩,
      ⟨⟨AdditionJointPairProgram.crown R k hk1,
        AdditionJointPairProgram.crown_realizesAt θ k hk1⟩⟩⟩
  -- ## the special degree `15`
  · exact ⟨P15.T1 θ (P15.Q7 θ), P15.T2 θ (P15.Q7 θ), P15.H2 θ, P15.H4 θ, 23,
      (P15.H2_good θ).1, (P15.H2_good θ).2, fun _ => P15.H4_good θ,
      ⟨⟨AdditionJointPairProgram.fifteen R,
        AdditionJointPairProgram.fifteen_realizesAt θ⟩⟩⟩
  -- ## the special degree `27`
  · exact ⟨P27Full.T1 θ, P27Full.T2 θ, P27Full.H2 θ, P27Full.H4 θ, 43,
      (P27Composition.H2_good θ).1, (P27Composition.H2_good θ).2,
      fun _ => P27Full.H4_good θ,
      ⟨⟨AdditionJointPairProgram.twentySeven R,
        AdditionJointPairProgram.twentySeven_realizesAt θ⟩⟩⟩
  -- ## the special degree `31`
  · exact ⟨P31Full.T1 θ, P31Full.T2 θ, P31Full.H2 θ, P31Full.H4 θ, 43,
      (P31Full.H2_good θ).1, (P31Full.H2_good θ).2, fun _ => P31Full.H4_good θ,
      ⟨⟨AdditionJointPairProgram.thirtyOne R,
        AdditionJointPairProgram.thirtyOne_realizesAt θ⟩⟩⟩
  -- ## `n ≡ 3 (mod 8)`, `n ≥ 11`, `n ≠ 27`: the `8k+3` induction step
  · obtain ⟨k, hk1, hk3, rfl⟩ : ∃ k, 1 ≤ k ∧ k ≠ 3 ∧ n = 8 * k + 3 :=
      ⟨n / 8, by omega, by omega, by omega⟩
    obtain ⟨S₁, St₁, H₂s, H₄s, a, hH2sm, hH2sd, -, ⟨source⟩⟩ :=
      ih (2 * k + 1) (by omega) (by omega) (by omega) (by omega)
        (fun i h1 h2' => hadm i h1 (by omega)) θ
    -- the retained quartic produced by the optimized `4k+1` bundle
    have hi1 : 2 * k + 1 + 1 = 2 * k + 2 := by omega
    have hi2 : 2 * k + 1 + 2 = 2 * k + 3 := by omega
    have hi3 : 2 * k + 1 + 3 = 2 * k + 4 := by omega
    have hbundle1 : OddGadget.q4BundleOutput H₂s (fun i => θ (2 * k + 1 + i)) k 1
        = crownH4 (H₂s.coeff 1) (H₂s.coeff 0 + θ (2 * k + 2)) (θ (2 * k + 3))
          (θ (2 * k + 4)) := by
      simp only [OddGadget.q4BundleOutput, twoOutputs_one, hi1, hi2, hi3]
    obtain ⟨hH4bm, hH4bd⟩ := crownH4_monic (A := A) (b := H₂s.coeff 1)
      (c := H₂s.coeff 0 + θ (2 * k + 2)) (a := θ (2 * k + 3)) (e := θ (2 * k + 4))
    have hH4bm' : (OddGadget.q4BundleOutput H₂s
        (fun i => θ (2 * k + 1 + i)) k 1).Monic := by rw [hbundle1]; exact hH4bm
    have hH4bd' : (OddGadget.q4BundleOutput H₂s
        (fun i => θ (2 * k + 1 + i)) k 1).natDegree = 4 := by
      rw [hbundle1]; exact hH4bd
    -- the low slot: the scalar at degree one, an addition-certified gadget above
    obtain ⟨g₂, ⟨third⟩⟩ : ∃ g₂, Nonempty (AdditionRealizedLowGadget (R := R) H₂s
        (OddGadget.q4BundleOutput H₂s (fun i => θ (2 * k + 1 + i)) k 1)
        (fun i => θ (6 * k + 2 + i)) (2 * k - 1) g₂) := by
      rcases eq_or_lt_of_le hk1 with rfl | hk2
      · exact ⟨0, ⟨AdditionRealizedLowGadget.scalar (R := R) H₂s _ _⟩⟩
      · have hdeg : 3 ≤ 2 * k - 1 := by omega
        obtain ⟨g₂, ⟨gadget⟩⟩ := AdditionRealizedOddGadget.dispatch (R := R)
          (2 * k - 1) (by omega) (fun i h1 h2' => hadm i h1 (by omega))
          hH2sm hH2sd hH4bm' hH4bd' (fun t => θ (6 * k + 2 + t))
        exact ⟨g₂, ⟨AdditionRealizedLowGadget.ofGadget hdeg gadget⟩⟩
    refine ⟨_, _, H₂s, _, _, hH2sm, hH2sd, fun _ => ⟨hH4bm', hH4bd'⟩,
      ⟨AdditionJointPairRealization.eightThree (R := R) hk1 hk3 source hH2sm hH2sd
        (2 * k + 1) (6 * k + 2) (8 * k + 1) (8 * k + 2) third⟩⟩
  -- ## `n ≡ 7 (mod 8)`, `n ≥ 23`, `n ≠ 31`: the `8k+7` induction step
  · obtain ⟨k, hk2, hk3, rfl⟩ : ∃ k, 2 ≤ k ∧ k ≠ 3 ∧ n = 8 * k + 7 :=
      ⟨n / 8, by omega, by omega, by omega⟩
    obtain ⟨T₁', T₂', H₂s, H₄s, a, hH2sm, hH2sd, hH4sg, ⟨source⟩⟩ :=
      ih (2 * k + 1) (by omega) (by omega) (by omega) (by omega)
        (fun i h1 h2' => hadm i h1 (by omega)) θ
    obtain ⟨hH4sm, hH4sd⟩ := hH4sg (by omega)
    obtain ⟨g₁, ⟨second⟩⟩ := AdditionRealizedOddGadget.dispatch (R := R) (2 * k + 1)
      (by omega) (fun i h1 h2' => hadm i h1 (by omega)) hH2sm hH2sd hH4sm hH4sd
      (fun t => θ (2 * k + 1 + t))
    obtain ⟨g₂, ⟨third⟩⟩ := AdditionRealizedOddGadget.dispatch (R := R) (4 * k + 3)
      (by omega) (fun i h1 h2' => hadm i h1 (by omega)) hH2sm hH2sd hH4sm hH4sd
      (fun t => θ (4 * k + 2 + t))
    exact ⟨_, _, H₂s, H₄s, _, hH2sm, hH2sd, fun _ => ⟨hH4sm, hH4sd⟩,
      ⟨AdditionJointPairRealization.eightSeven (R := R) hk2 hk3 source
        (2 * k + 1) (4 * k + 2) (8 * k + 5) (8 * k + 6) second third⟩⟩

/-- Every admissible odd degree has a fixed complete-polynomial program carrying its
semantics and exact addition count, with at most `⌊n/2⌋ + 1` multiplications. -/
theorem additionPolynomialRealization_exists_odd (n : ℕ) (hodd : n % 2 = 1)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) (θ : ℕ → A) :
    ∃ (P : A[X]) (mult additions : ℕ), mult ≤ n / 2 + 1 ∧
      Nonempty (AdditionPolynomialRealization R θ P n mult additions) := by
  rcases eq_or_ne n 1 with rfl | hn1
  · exact ⟨_, 0, 1, by omega, ⟨AdditionPolynomialRealization.linear θ⟩⟩
  rcases eq_or_ne n 3 with rfl | hn3
  · exact ⟨_, 2, 3, by omega, ⟨AdditionPolynomialRealization.cubic θ⟩⟩
  rcases eq_or_ne n 7 with rfl | hn7
  · exact ⟨_, 4, 10, by omega, ⟨AdditionPolynomialRealization.septic θ⟩⟩
  obtain ⟨T₁, T₂, H₂, H₄, a, -, -, -, ⟨source⟩⟩ :=
    additionJointPairRealization_exists n hodd (by omega) hn7 hadm θ
  exact ⟨_, _, _, by omega, ⟨AdditionPolynomialRealization.ofJointPair source⟩⟩

/-- **Same-program complete-polynomial existence** for every positive admissible
degree: even degrees are the one-product, one-addition lift of the odd degree below. -/
theorem additionPolynomialRealization_exists (n : ℕ) (hn : 1 ≤ n)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) (θ : ℕ → A) :
    ∃ (P : A[X]) (mult additions : ℕ), mult ≤ n / 2 + 1 ∧
      Nonempty (AdditionPolynomialRealization R θ P n mult additions) := by
  by_cases hodd : n % 2 = 1
  · exact additionPolynomialRealization_exists_odd n hodd hadm θ
  rcases eq_or_ne n 2 with rfl | hn2
  · exact ⟨_, 1, 2, by omega, ⟨AdditionPolynomialRealization.quadratic θ⟩⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : m % 2 = 1 := by omega
  obtain ⟨P, mult, additions, hmult, ⟨source⟩⟩ :=
    additionPolynomialRealization_exists_odd m hm
      (fun i h1 h2' => hadm i h1 (by omega)) θ
  exact ⟨_, _, _, by omega,
    ⟨AdditionPolynomialRealization.evenLift source hm m⟩⟩

/-- **The addition bounds of the manuscript, on the literal program.**  For every
positive degree `n` over an `n`-admissible ring there is one fixed polynomial program
that realizes a degree-`n` member of the constructed family with at most
`⌊n/2⌋ + 1` nonscalar multiplications and whose literal addition count `additions`
satisfies both `additions ≤ 2n` and `4·additions ≤ 5n + 24⌈log₂ n⌉² + 4`
(the integer form of `A_n ≤ 5n/4 + 6⌈log₂ n⌉² + 1`). -/
theorem construction_additions_checked (n : ℕ) (hn : 1 ≤ n)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R)) (θ : ℕ → A) :
    ∃ (P : A[X]) (mult additions : ℕ) (program : PolynomialProgram R mult),
      mult ≤ n / 2 + 1 ∧ program.RealizesAt θ P ∧ program.additions = additions ∧
        additions ≤ 2 * n ∧
        4 * additions ≤ 5 * n + 24 * ceilLog2 n * ceilLog2 n + 4 := by
  obtain ⟨P, mult, additions, hmult, ⟨source⟩⟩ :=
    additionPolynomialRealization_exists n hn hadm θ
  exact ⟨P, mult, additions, source.program, hmult, source.realizesAt,
    source.addition_count, source.ledger.uniform_two, source.ledger.sharp⟩

end FastPoly.Cost
