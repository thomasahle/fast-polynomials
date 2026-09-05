/-
The degree-six lower bound: transporting an everywhere-defined rational inverse along a
surjective polynomial map (the "transport" of the repaired remark).
-/
import FastPoly.LowerBound.General.Transversal
import FastPoly.LowerBound.Main

/-!
# Transport of rational inverses

The repaired remark (`sections/lower_char_p_draft.tex`, `rem:charp-lower-gap`, case (iv))
says that when `Q = ν ∘ H` is invertible the normal-form theorem "transfers after
transporting the everywhere-defined left inverse".  `RationalInverse.transport` is that
transport, for an arbitrary polynomial map `Q` that is *surjective* on `F`-points: an
everywhere-defined rational left inverse of `E ∘ Q` gives one of `E`.

The construction is explicit and recursive in the polynomial `Q j`
(`exists_rational_of_inverse`): substitute the rational functions `num i / den i` for the
variables, constants and sums and products of rational functions being formed with the
denominators multiplied.  Denominators stay nonvanishing because they are products of
nonvanishing ones.

`no_rationalInverse_general_of_transversal` is the case-(iv) branch of the main theorem
proved *this* way (transport from `no_rationalInverse` for the normal form), as a check
that the two routes agree; `Main.lean` itself pulls the singular point back through `Θ`
and does not use this file.
-/

namespace FastPoly.LowerBound.General

open MvPolynomial

section Transport

variable {F : Type*} [Field F] {n : ℕ}

theorem polyMap_bind₁ (E Q : Fin n → MvPolynomial (Fin n) F) (p : Fin n → F) :
    polyMap (fun k => bind₁ Q (E k)) p = polyMap E (polyMap Q p) := by
  funext k
  simp only [polyMap]
  exact eval_bind₁ Q p (E k)

/-- Substituting the rational left inverse of `E ∘ Q` into a polynomial `f`: a fraction
`num / den` with nonvanishing `den` such that `(num / den)(E (Q p)) = f(p)`. -/
theorem exists_rational_of_inverse (E Q : Fin n → MvPolynomial (Fin n) F)
    (inv : RationalInverse (fun k => bind₁ Q (E k))) (f : MvPolynomial (Fin n) F) :
    ∃ num den : MvPolynomial (Fin n) F, (∀ y, eval y den ≠ 0) ∧
      ∀ p, eval (polyMap E (polyMap Q p)) num
        = eval p f * eval (polyMap E (polyMap Q p)) den := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 1, fun y => by simp, fun p => by simp⟩
  | add f g hf hg =>
      obtain ⟨n1, d1, hd1, h1⟩ := hf
      obtain ⟨n2, d2, hd2, h2⟩ := hg
      refine ⟨n1 * d2 + n2 * d1, d1 * d2, fun y => ?_, fun p => ?_⟩
      · rw [map_mul]
        exact mul_ne_zero (hd1 y) (hd2 y)
      · simp only [map_add, map_mul, h1 p, h2 p]
        ring
  | mul_X f i hf =>
      obtain ⟨n1, d1, hd1, h1⟩ := hf
      refine ⟨n1 * inv.num i, d1 * inv.den i, fun y => ?_, fun p => ?_⟩
      · rw [map_mul]
        exact mul_ne_zero (hd1 y) (inv.den_ne_zero i y)
      · have hi := inv.inv_eq p i
        rw [polyMap_bind₁] at hi
        simp only [map_mul, eval_X, h1 p, hi]
        ring

/-- **Transport.**  If `Q` is surjective on `F`-points, an everywhere-defined rational left
inverse of `E ∘ Q` yields one of `E`. -/
theorem RationalInverse.transport (E Q : Fin n → MvPolynomial (Fin n) F)
    (hQ : Function.Surjective (polyMap Q))
    (inv : RationalInverse (fun k => bind₁ Q (E k))) : Nonempty (RationalInverse E) := by
  choose num den hden hnum using fun j => exists_rational_of_inverse E Q inv (Q j)
  refine ⟨⟨num, den, hden, fun q j => ?_⟩⟩
  obtain ⟨p, rfl⟩ := hQ q
  exact hnum j p

end Transport

section Application

variable {F : Type*} [Field F]

/-- `map_out` for an algebra homomorphism. -/
theorem algHom_out (f : MvPolynomial (Fin 6) F →ₐ[F] MvPolynomial (Fin 6) F)
    (c' : Circuit (MvPolynomial (Fin 6) F)) (x : MvPolynomial (Fin 6) F)
    (p : Fin 6 → MvPolynomial (Fin 6) F) :
    f (out c' x p) = out (c'.map f) (f x) (fun i => f (p i)) :=
  map_out (f : MvPolynomial (Fin 6) F →+* MvPolynomial (Fin 6) F) c' x p

/-- The general program is the substitution of `Q = ν ∘ H` into the normal-form polynomials. -/
theorem outPolyGeneral_eq_bind₁ (c : GCircuit F) {b : F} (hb : c.β₁ = c.α₁ * b)
    (xs : Fin 6 → F) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F) :
    outPolyGeneral c xs M h₀ = fun k => bind₁ (Qpoly b c M h₀) (outPoly c.toNormal xs k) := by
  rw [outPolyGeneral_eq_outPolyOf c hb]
  funext k
  simp only [outPolyOf, outPoly]
  rw [algHom_out (bind₁ (Qpoly b c M h₀))]
  have h1 : (c.toNormal.map (C : F → MvPolynomial (Fin 6) F)).map (bind₁ (Qpoly b c M h₀))
      = c.toNormal.map C := by
    rw [Circuit.map_map]
    exact Circuit.map_congr _ fun y => by simp
  have h2 : bind₁ (Qpoly b c M h₀) (C (xs k) : MvPolynomial (Fin 6) F) = C (xs k) := by simp
  have h3 : (fun i => bind₁ (Qpoly b c M h₀) (X i : MvPolynomial (Fin 6) F))
      = Qpoly b c M h₀ := by
    funext i
    simp
  rw [h1, h2, h3]

/-- In the transversal case `Q` is surjective on `F`-points (`Q ∘ Θ = id`). -/
theorem polyMap_Qpoly_surjective (b : F) (c : GCircuit F) (M : Matrix (Fin 7) (Fin 6) F)
    (h₀ : Fin 7 → F) {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (hκ : kappa c (lker M i₀) = 0)
    (hc : c1o b (lker M i₀) ≠ 0) : Function.Surjective (polyMap (Qpoly b c M h₀)) :=
  fun q => ⟨Theta b c M h₀ i₀ q, by rw [polyMap_Qpoly, Qval_Theta b c M h₀ hd hκ hc]⟩

/-- The case-(iv) branch of the main theorem, proved by transport from the normal-form
theorem `no_rationalInverse` instead of by pulling back the singular point. -/
theorem no_rationalInverse_general_of_transversal [Infinite F] (h2 : (2 : F) ≠ 0)
    (c : GCircuit F) {b : F} (hb : c.β₁ = c.α₁ * b) (xs : Fin 6 → F)
    (hxs : Function.Injective xs) (M : Matrix (Fin 7) (Fin 6) F) (h₀ : Fin 7 → F)
    {i₀ : Fin 7} (hd : (minor M i₀).det ≠ 0) (hκ : kappa c (lker M i₀) = 0)
    (hc : c1o b (lker M i₀) ≠ 0) : IsEmpty (RationalInverse (outPolyGeneral c xs M h₀)) := by
  constructor
  intro inv
  rw [outPolyGeneral_eq_bind₁ c hb] at inv
  obtain ⟨inv'⟩ := RationalInverse.transport (outPoly c.toNormal xs) (Qpoly b c M h₀)
    (polyMap_Qpoly_surjective b c M h₀ hd hκ hc) inv
  exact (no_rationalInverse h2 c.toNormal xs hxs).false inv'

end Application

end FastPoly.LowerBound.General
