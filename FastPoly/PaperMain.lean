import FastPoly.Cost.Additions.DecodedPolynomial

/-!
# Paper-level capstone

The main theorem has two scheduling clauses.  The decoder/coverage arrangement carries
the monic polynomial, the coefficient decoder, the exact multiplication count, and the
logarithmic multiplicative-height bound.  The addition-optimized arrangement carries a
literal circuit, its semantics, its multiplication count, and both advertised addition
bounds.  The theorem below now constructs both arrangements on one common semantic
polynomial `P`.  Their syntax trees need not be equal.

This is a packaging theorem, not a numerical ledger detached from circuit semantics:
both arrangements contain a `PolynomialProgram` and a `RealizesAt` proof.
-/

namespace FastPoly

open Polynomial

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- All circuit-level clauses of the paper's main upper bound, with the two advertised
arrangements made explicit.

The first arrangement is the decoder/height schedule.  The second is the
addition-optimized schedule.  Both use at most `⌊n/2⌋+1` nonscalar products and both
carry their semantics on the literal fixed program appearing in the witness. -/
structure MainArrangementsChecked (R : Type u) [CommRing R]
    {A : Type v} [CommRing A] [Algebra R A] (theta : ℕ → A) (n : ℕ) : Prop where
  sharedPolynomial : Nonempty (DecodedAdditionPolynomial R theta n)
  decodedHeight :
    ∃ (multiplications height : ℕ),
      multiplications ≤ n / 2 + 1 ∧
      height ≤ 2 * Nat.clog 2 n + 4 + (n + 1) % 2 ∧
      RealizedPolynomial R theta n multiplications height
  literalAdditions :
    ∃ (P : A[X]) (multiplications additions : ℕ)
      (program : Cost.PolynomialProgram R multiplications),
      multiplications ≤ n / 2 + 1 ∧
      program.RealizesAt theta P ∧
      program.additions = additions ∧
      additions ≤ 2 * n ∧
      4 * additions ≤
        5 * n + 24 * Cost.ceilLog2 n * Cost.ceilLog2 n + 4

namespace MainArrangementsChecked

variable [Nontrivial A]

/-- The paper-level upper-bound package over a base in which the displayed integer
pivots are units.  Both arrangements are projected from the same decoded polynomial
provided by `decodedAdditionPolynomial_exists`. -/
theorem of_units (n : ℕ) (hn : 1 ≤ n)
    (hadm : ∀ i : ℕ, 1 ≤ i → i ≤ n → IsUnit (((i : ℕ) : ℤ) : R))
    (theta : ℕ → A) : MainArrangementsChecked R theta n := by
  obtain ⟨source⟩ := decodedAdditionPolynomial_exists n hn hadm theta
  refine ⟨⟨source⟩, ?_, ?_⟩
  · exact ⟨source.multiplications, 2 * Nat.clog 2 n + 4 + (n + 1) % 2,
      source.multiplication_le, le_rfl,
      ⟨source.P, source.heightProgram, source.monic, source.natDegree,
        source.decode, source.heightRealizesAt, source.heightBounded⟩⟩
  · exact ⟨source.P, source.multiplications, source.additions,
      source.additionRealization.program, source.multiplication_le,
      source.additionRealization.realizesAt,
      source.additionRealization.addition_count,
      source.additionRealization.ledger.uniform_two,
      source.additionRealization.ledger.sharp⟩

/-- Field-facing characteristic-zero form of the paper-level package. -/
theorem of_charZero (F : Type u) [Field F] [CharZero F]
    {A : Type v} [CommRing A] [Algebra F A] [Nontrivial A]
    (n : ℕ) (hn : 1 ≤ n) (theta : ℕ → A) :
    MainArrangementsChecked F theta n :=
  of_units n hn (Admissible.intCast_units (admissible_of_charZero F n)) theta

/-- Field-facing characteristic-`p>n` form of the paper-level package. -/
theorem of_charP (F : Type u) [Field F] (p : ℕ) [CharP F p]
    {A : Type v} [CommRing A] [Algebra F A] [Nontrivial A]
    (n : ℕ) (hn : 1 ≤ n) (hp : n < p) (theta : ℕ → A) :
    MainArrangementsChecked F theta n :=
  of_units n hn (Admissible.intCast_units (admissible_of_charP F p hp)) theta

end MainArrangementsChecked

end FastPoly
