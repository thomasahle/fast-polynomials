import FastPoly.Polynomial.MonicEvaluation

/-!
# The explicit inverse of monic polynomial evaluation

Subtract the prescribed leading monomial from the observed values, interpolate
the residual values by the Lagrange formula, and read its low coefficients.
Both compositions are checked below. The interpolant remains a named polynomial;
no expanded Vandermonde system or generic inverse solver is used.
-/

namespace FastPoly.ExplicitEvaluationInverse

open Polynomial

set_option maxHeartbeats 20000

variable {F : Type*} [Field F] {n : ℕ}

/-- The low-degree part, kept separate from the fixed leading monomial. -/
noncomputable def lowPolynomial (c : Fin n → F) : F[X] :=
  ∑ j ∈ Finset.range n, C (extendFin c j) * X ^ j

theorem monic_eq (c : Fin n → F) :
    monicOfCoefficients c = X ^ n + lowPolynomial c := rfl

theorem low_degree_lt (c : Fin n → F) :
    (lowPolynomial c).degree < n := by
  apply (degree_sum_le _ _).trans_lt
  exact (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun j hj =>
    (degree_C_mul_X_pow_le _ _).trans_lt
      (WithBot.coe_lt_coe.2 (Finset.mem_range.mp hj))

theorem low_coeff (c : Fin n → F) (j : Fin n) :
    (lowPolynomial c).coeff j = c j := by
  rw [lowPolynomial, finset_sum_coeff, Finset.sum_eq_single (j : ℕ)]
  · simp only [coeff_C_mul_X_pow, ite_true, extendFin, dif_pos j.isLt]
  · intro k _ hkj
    rw [coeff_C_mul_X_pow, if_neg (Ne.symm hkj)]
  · exact fun hj => absurd (Finset.mem_range.2 j.isLt) hj

/-- Reconstruct a bounded polynomial from its actual low coefficients. -/
theorem low_of_coefficients (P : F[X]) (hP : P.natDegree < n) :
    lowPolynomial (fun j : Fin n => P.coeff j) = P := by
  calc
    lowPolynomial (fun j : Fin n => P.coeff j) =
        ∑ j ∈ Finset.range n, C (P.coeff j) * X ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [extendFin, dif_pos (Finset.mem_range.mp hj)]
    _ = P := (P.as_sum_range_C_mul_X_pow' hP).symm

/-- The evaluation map on monic coefficient vectors. -/
noncomputable def encode (x : Fin n → F) (c : Fin n → F) : Fin n → F :=
  fun i => (monicOfCoefficients c).eval (x i)

/-- The explicit Lagrange formula for the residual evaluation data. -/
noncomputable def interpolant (x values : Fin n → F) : F[X] :=
  Lagrange.interpolate Finset.univ x (fun i => values i - x i ^ n)

/-- The named inverse: read the low coefficients of the residual interpolant. -/
noncomputable def decode (x values : Fin n → F) : Fin n → F :=
  fun j => (interpolant x values).coeff j

theorem encode_residual (x c : Fin n → F) (i : Fin n) :
    encode x c i - x i ^ n = (lowPolynomial c).eval (x i) := by
  simp only [encode, monic_eq, eval_add, eval_pow, eval_X, add_sub_cancel_left]

theorem interpolant_encode (x : Fin n → F) (hx : Function.Injective x)
    (c : Fin n → F) : interpolant x (encode x c) = lowPolynomial c := by
  have hInj : Set.InjOn x ↑(Finset.univ : Finset (Fin n)) :=
    fun _ _ _ _ h => hx h
  have hdeg : (lowPolynomial c).degree < (Finset.univ : Finset (Fin n)).card := by
    simpa only [Finset.card_univ, Fintype.card_fin] using low_degree_lt c
  simpa only [interpolant, encode_residual] using
    (Lagrange.eq_interpolate hInj hdeg).symm

/-- Decoding the evaluations of a monic coefficient vector returns that vector. -/
theorem decode_encode (x : Fin n → F) (hx : Function.Injective x)
    (c : Fin n → F) : decode x (encode x c) = c := by
  funext j
  rw [decode, interpolant_encode x hx, low_coeff]

theorem interpolant_natDegree_lt (hn : 1 ≤ n) (x : Fin n → F)
    (hx : Function.Injective x) (values : Fin n → F) :
    (interpolant x values).natDegree < n := by
  by_cases hzero : interpolant x values = 0
  · rw [hzero, natDegree_zero]
    exact hn
  · apply (natDegree_lt_iff_degree_lt hzero).2
    have hInj : Set.InjOn x ↑(Finset.univ : Finset (Fin n)) :=
      fun _ _ _ _ h => hx h
    simpa only [interpolant, Finset.card_univ, Fintype.card_fin] using
      (Lagrange.degree_interpolate_lt (r := fun i => values i - x i ^ n) hInj)

theorem low_decode (hn : 1 ≤ n) (x : Fin n → F)
    (hx : Function.Injective x) (values : Fin n → F) :
    lowPolynomial (decode x values) = interpolant x values :=
  low_of_coefficients _ (interpolant_natDegree_lt hn x hx values)

theorem interpolant_eval (x : Fin n → F) (hx : Function.Injective x)
    (values : Fin n → F) (i : Fin n) :
    (interpolant x values).eval (x i) = values i - x i ^ n := by
  have hInj : Set.InjOn x ↑(Finset.univ : Finset (Fin n)) :=
    fun _ _ _ _ h => hx h
  exact Lagrange.eval_interpolate_at_node (fun j => values j - x j ^ n)
    (hvs := hInj) (hi := Finset.mem_univ i)

/-- Evaluating the explicit decoder reproduces any prescribed value vector. -/
theorem encode_decode (hn : 1 ≤ n) (x : Fin n → F)
    (hx : Function.Injective x) (values : Fin n → F) :
    encode x (decode x values) = values := by
  funext i
  rw [encode, monic_eq, low_decode hn x hx, eval_add, eval_pow, eval_X,
    interpolant_eval x hx]
  rw [← add_sub_assoc, add_sub_cancel_left]

/-- Monic interpolation, with the displayed inverse and both compositions. -/
noncomputable def evaluationEquiv (hn : 1 ≤ n) (x : Fin n → F)
    (hx : Function.Injective x) : (Fin n → F) ≃ (Fin n → F) where
  toFun := encode x
  invFun := decode x
  left_inv := decode_encode x hx
  right_inv := encode_decode hn x hx

/-- Drop-in compatibility with the existing monic-evaluation theorem. -/
theorem evaluation_bijective (hn : 1 ≤ n) (x : Fin n → F)
    (hx : Function.Injective x) :
    Function.Bijective (fun c : Fin n → F => fun i : Fin n =>
      (monicOfCoefficients c).eval (x i)) :=
  (evaluationEquiv hn x hx).bijective

/-- A circuit's supplied coefficient inverse is followed by this interpolation
inverse; the composed inverse has no existentially chosen circuit parameters. -/
noncomputable def familyEvaluationEquiv {K : Type*} (coefficients : K ≃ (Fin n → F))
    (hn : 1 ≤ n) (x : Fin n → F) (hx : Function.Injective x) :
    K ≃ (Fin n → F) := coefficients.trans (evaluationEquiv hn x hx)

theorem familyEvaluationEquiv_inverse {K : Type*} (coefficients : K ≃ (Fin n → F))
    (hn : 1 ≤ n) (x : Fin n → F) (hx : Function.Injective x) (values : Fin n → F) :
    (familyEvaluationEquiv coefficients hn x hx).symm values =
      coefficients.symm (decode x values) := rfl

theorem familyEvaluationEquiv_apply {K : Type*} (coefficients : K ≃ (Fin n → F))
    (hn : 1 ≤ n) (x : Fin n → F) (hx : Function.Injective x)
    (P : K → F[X]) (hP : ∀ q, P q = monicOfCoefficients (coefficients q)) (q : K) :
    familyEvaluationEquiv coefficients hn x hx q = fun i => (P q).eval (x i) := by
  rw [hP q]
  rfl

end FastPoly.ExplicitEvaluationInverse
