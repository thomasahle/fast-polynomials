import Mathlib.LinearAlgebra.Lagrange

/-!
# Monic interpolation at an arbitrary number of points

This is the dimension-generic Vandermonde bridge used by the characteristic-two
appendix circuits: once their key-to-low-coefficient map is bijective, evaluation
at distinct points is bijective as well.
-/

namespace FastPoly

open Polynomial

universe u

variable {F : Type u} [Field F]

/-- Extend a finite coefficient vector by zero. -/
def extendFin {n : ℕ} (a : Fin n → F) : ℕ → F :=
  fun j => if h : j < n then a ⟨j, h⟩ else 0

/-- The monic degree-`n` polynomial with prescribed low coefficients. -/
noncomputable def monicOfCoefficients {n : ℕ} (p : Fin n → F) : F[X] :=
  X ^ n + ∑ j ∈ Finset.range n, C (extendFin p j) * X ^ j

private theorem low_natDegree_le {n : ℕ} (hn : 1 ≤ n) (v : ℕ → F) :
    (∑ j ∈ Finset.range n, C (v j) * X ^ j).natDegree ≤ n - 1 := by
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  simp only [Finset.fold_max_le]
  refine ⟨by omega, ?_⟩
  intro j hj
  exact le_trans (natDegree_C_mul_X_pow_le _ _) (by
    simp only [Finset.mem_range] at hj
    omega)

private theorem low_coeff {n : ℕ} (v : ℕ → F) {k : ℕ} (hk : k < n) :
    (∑ j ∈ Finset.range n, C (v j) * X ^ j).coeff k = v k := by
  rw [finset_sum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    simp only [coeff_C_mul, coeff_X_pow]
    rw [if_neg (fun h => hjk h.symm), mul_zero]
  · exact fun hk' => absurd (Finset.mem_range.2 hk) hk'

/-- Evaluation of monic degree-`n` polynomials at `n` distinct field points is
bijective on the vector of low coefficients. -/
theorem monicOfCoefficients_eval_bijective {n : ℕ} (hn : 1 ≤ n)
    (x : Fin n → F) (hx : Function.Injective x) :
    Function.Bijective (fun p : Fin n → F => fun i : Fin n =>
      (monicOfCoefficients p).eval (x i)) := by
  constructor
  · intro p q hpq
    have heval : ∀ i : Fin n,
        (∑ j ∈ Finset.range n, C (extendFin p j) * X ^ j).eval (x i) =
          (∑ j ∈ Finset.range n, C (extendFin q j) * X ^ j).eval (x i) := by
      intro i
      have h := congrFun hpq i
      simp only [monicOfCoefficients, eval_add, eval_pow, eval_X] at h
      exact add_left_cancel h
    have hlow : (∑ j ∈ Finset.range n, C (extendFin p j) * X ^ j) =
        ∑ j ∈ Finset.range n, C (extendFin q j) * X ^ j := by
      refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ hx heval ?_
      have hp := low_natDegree_le hn (extendFin p)
      have hq := low_natDegree_le hn (extendFin q)
      simp only [Fintype.card_fin]
      omega
    funext k
    have h := congrArg (fun P => P.coeff (k : ℕ)) hlow
    simp only [low_coeff _ k.isLt] at h
    simpa [extendFin, k.isLt] using h
  · intro v
    set L : F[X] := Lagrange.interpolate Finset.univ x
      (fun i => v i - x i ^ n) with hL
    have hInj : Set.InjOn x ↑(Finset.univ : Finset (Fin n)) :=
      fun i _ j _ h => hx h
    have hLdeg : L.natDegree < n := by
      rcases eq_or_ne L 0 with h0 | h0
      · rw [h0]
        simpa using hn
      · have hdeg := Lagrange.degree_interpolate_lt
          (r := fun i => v i - x i ^ n) hInj
        rw [← hL] at hdeg
        have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
        rw [hcard] at hdeg
        exact natDegree_lt_iff_degree_lt h0 |>.2 (by exact_mod_cast hdeg)
    refine ⟨fun j => L.coeff j, ?_⟩
    have hsum : (∑ j ∈ Finset.range n,
        C (extendFin (fun j : Fin n => L.coeff j) j) * X ^ j) = L := by
      have hrepr := Polynomial.as_sum_range_C_mul_X_pow' L hLdeg
      rw [hrepr]
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp only [Finset.mem_range] at hj
      simp [extendFin, hj]
    funext i
    simp only [monicOfCoefficients, hsum, eval_add, eval_pow, eval_X]
    rw [hL, Lagrange.eval_interpolate_at_node (hvs := hInj)
      (hi := Finset.mem_univ i)]
    ring

end FastPoly
