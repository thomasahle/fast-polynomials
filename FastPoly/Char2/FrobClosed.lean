import FastPoly.Recover.Context

/-!
# Frobenius-closed subalgebras

Subalgebras are closed under the Frobenius `a ↦ a²` but not under its inverse,
so the square-first characteristic-two decoders (whose pivots are rows of the
form `known + z^(2^e)`, `char2_static_patterns.md` §26) cannot be certified
against a plain visible algebra.  `FrobClosed` is the minimal closure property
that transports those pivots; the full field always satisfies it, and over a
perfect field so does any perfectly-closed intermediate algebra.
-/

namespace FastPoly.Char2

universe u v

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A subalgebra closed under square roots (inverse Frobenius). -/
def FrobClosed (V : Subalgebra R A) : Prop :=
  ∀ a : A, a ^ 2 ∈ V → a ∈ V

theorem frobClosed_top : FrobClosed (⊤ : Subalgebra R A) :=
  fun _ _ => trivial

/-- Iterated square roots stay available in a Frobenius-closed algebra. -/
theorem FrobClosed.pow_two_pow_mem {V : Subalgebra R A} (hV : FrobClosed V) :
    ∀ (e : ℕ) (a : A), a ^ 2 ^ e ∈ V → a ∈ V := by
  intro e
  induction e with
  | zero => intro a ha; simpa using ha
  | succ e ih =>
    intro a ha
    refine ih a (hV _ ?_)
    rw [← pow_mul, ← pow_succ]
    exact ha

/-- **The Frobenius pivot step**: a row `a^(2^e) + F` with `F` known recovers
`a` inside any Frobenius-closed algebra. -/
theorem FrobClosed.frob_pivot_mem {V : Subalgebra R A} (hV : FrobClosed V)
    {a F : A} (e : ℕ) (hrow : a ^ 2 ^ e + F ∈ V) (hF : F ∈ V) : a ∈ V := by
  refine hV.pow_two_pow_mem e a ?_
  have : a ^ 2 ^ e = (a ^ 2 ^ e + F) - F := by ring
  rw [this]
  exact sub_mem hrow hF

end FastPoly.Char2
