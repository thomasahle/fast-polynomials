import FastPoly.Cost.RealizedOddGadgetKnown

/-!
# Canonical realized odd-gadget dispatch

The algebraic dispatcher and the circuit accounting now choose one object, not two
merely equicost witnesses.  Each residue branch returns a `RealizedOddGadget`, whose
decoder and semantic circuit refer to the same explicit polynomial.
-/

namespace FastPoly.Cost.RealizedOddGadget

open Polynomial Algebra

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
  [Nontrivial A]

/-- For every odd `d`, the paper's canonical degree-`d` auxiliary gadget has both its
conditional decoder and its actual `d / 2`-multiplication circuit. -/
theorem dispatch (d : ℕ) (hd : d % 2 = 1)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ d → IsUnit (((n : ℕ) : ℤ) : R))
    {H₂ H₄ : A[X]} (hH₂m : H₂.Monic) (hH₂d : H₂.natDegree = 2)
    (hH₄m : H₄.Monic) (hH₄d : H₄.natDegree = 4) (θ : ℕ → A) :
    Nonempty (RealizedOddGadget (R := R) H₂ H₄ θ d) := by
  rcases (show d = 1 ∨ d = 3 ∨ d = 7 ∨ (d % 4 = 1 ∧ 5 ≤ d) ∨
      (d % 8 = 3 ∧ 11 ≤ d) ∨ (d % 8 = 7 ∧ 15 ≤ d) from by omega)
    with rfl | rfl | rfl | ⟨h4, h5⟩ | ⟨h8, h11⟩ | ⟨h8, h15⟩
  · exact ⟨one H₂ H₄ θ⟩
  · exact ⟨three hH₂m hH₂d θ⟩
  · exact ⟨seven hH₂m hH₂d hH₄m hH₄d θ⟩
  · obtain ⟨m, hm, rfl⟩ : ∃ m, 1 ≤ m ∧ d = 4 * m + 1 :=
      ⟨d / 4, by omega⟩
    have hadm' : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * m → IsUnit (((n : ℕ) : ℤ) : R) :=
      fun n hn hnm => hadm n hn (by omega)
    have h2 : IsUnit (2 : R) := FastPoly.isUnit_two_of_cast hadm (by omega)
    exact ⟨q4 hH₂m hH₂d m hm hadm' h2 θ⟩
  · obtain ⟨m, hm, rfl⟩ : ∃ m, 1 ≤ m ∧ d = 8 * m + 3 :=
      ⟨d / 8, by omega⟩
    exact ⟨known hH₂m hH₂d hH₄m hH₄d m hm
      (fun n hn hnm => hadm n hn (by omega)) θ⟩
  · obtain ⟨m, hm, rfl⟩ : ∃ m, 1 ≤ m ∧ d = 8 * m + 7 :=
      ⟨d / 8, by omega⟩
    rcases eq_or_lt_of_le hm with rfl | hm2
    · exact ⟨barredOne hH₂m hH₂d hH₄m hH₄d θ⟩
    · exact ⟨barredGeneral hH₂m hH₂d hH₄m hH₄d m hm2
        (fun n hn hnm => hadm n hn (by omega)) θ⟩

end FastPoly.Cost.RealizedOddGadget
