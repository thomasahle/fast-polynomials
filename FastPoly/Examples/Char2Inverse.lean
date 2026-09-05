import FastPoly.Examples.OptimizedCircuits
import FastPoly.Examples.ExplicitEvaluationInverse
import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.Lagrange

/-!
# `lem:first-char2-circuit-inverse`

Over a perfect field of characteristic `2`, the key-to-evaluations map of the first
characteristic-2 appendix circuit (4 products, degree 7) is a bijection `F⁷ → F⁷`.
The proof follows the paper: the circuit's coefficients are explicit polynomials in
the keys (`coeffMap`, via a `2·J` witness); the keys are recovered from the
coefficients by the displayed square-root formulas (`decodeKeys`); and monic
degree-7 interpolation at seven distinct points is bijective (Lagrange).
-/

namespace FastPoly.Char2Four

open Polynomial

section coeffs

variable {A : Type*} [CommRing A]

/-- `b = 1 + a₀ + a₁`. -/
def bK (a : ℕ → A) : A := 1 + a 0 + a 1

/-- `c = 1 + a₀ + a₂ + a₀a₁`. -/
def cK (a : ℕ → A) : A := 1 + a 0 + a 2 + a 0 * a 1

/-- `d = a₁a₂`. -/
def dK (a : ℕ → A) : A := a 1 * a 2

/-- The circuit's coefficient vector (paper display). -/
def coeffMap (a : ℕ → A) : ℕ → A
  | 0 => a 4 * (dK a ^ 2 + a 3 * dK a + a 5) + a 6
  | 1 => dK a ^ 2 + a 3 * dK a + a 5 + a 4 * (a 3 * cK a + a 0)
  | 2 => a 3 * cK a + a 0 + a 4 * (cK a ^ 2 + a 3 * bK a + 1)
  | 3 => cK a ^ 2 + a 3 * bK a + 1 + a 4 * a 3
  | 4 => a 3 + a 4 * bK a ^ 2
  | 5 => bK a ^ 2
  | 6 => a 4
  | _ + 7 => 0

/-- The characteristic-2 defect of the circuit against its coefficient normal form. -/
noncomputable def Jw (a : ℕ → A) : A[X] :=
  C (a 0 + a 1 + 1) * X ^ 6
    + C (a 0 * a 1 + a 0 * a 4 + a 0 + a 1 * a 4 + a 2 + a 4 + 1) * X ^ 5
    + C (a 0 ^ 2 * a 1 + a 0 ^ 2 + a 0 * a 1 ^ 2 + a 0 * a 1 * a 4 + 2 * (a 0 * a 1)
        + a 0 * a 2 + a 0 * a 4 + 2 * a 0 + 2 * (a 1 * a 2) + a 1 + a 2 * a 4 + a 2
        + a 4 + 1) * X ^ 4
    + C (a 0 ^ 2 * a 1 * a 4 + a 0 ^ 2 * a 4 + a 0 * a 1 ^ 2 * a 4
        + a 0 * a 1 * a 2 + 2 * (a 0 * a 1 * a 4) + a 0 * a 2 * a 4 + 2 * (a 0 * a 4)
        + a 1 ^ 2 * a 2 + 2 * (a 1 * a 2 * a 4) + a 1 * a 2 + a 1 * a 4 + a 2 * a 4
        + a 4) * X ^ 3
    + C (a 0 * a 1 ^ 2 * a 2 + a 0 * a 1 * a 2 * a 4 + a 0 * a 1 * a 2
        + a 1 ^ 2 * a 2 * a 4 + a 1 * a 2 ^ 2 + a 1 * a 2 * a 4 + a 1 * a 2) * X ^ 2
    + C (a 0 * a 1 ^ 2 * a 2 * a 4 + a 0 * a 1 * a 2 * a 4 + a 1 * a 2 ^ 2 * a 4
        + a 1 * a 2 * a 4) * X

/-- The circuit against its coefficient normal form, over any commutative ring:
the difference is exactly `2·J`. -/
theorem P_sub_normal (a : ℕ → A) :
    P a - (X ^ 7 + ∑ j ∈ Finset.range 7, C (coeffMap a j) * X ^ j)
      = 2 * Jw a := by
  simp only [P, uW, tW, zW, yW, coeffMap, bK, cK, dK, Jw, Finset.sum_range_succ,
    Finset.sum_range_zero, map_add, map_mul, map_one, map_pow, map_ofNat]
  ring

/-- Over characteristic 2, the circuit *is* its coefficient normal form. -/
theorem P_eq_normal [CharP A 2] (a : ℕ → A) :
    P a = X ^ 7 + ∑ j ∈ Finset.range 7, C (coeffMap a j) * X ^ j := by
  have h2 : (2 : A[X]) = 0 := by
    have hA : (2 : A) = 0 := by
      have := CharP.cast_eq_zero A 2
      simpa using this
    have : (2 : A[X]) = C (2 : A) := by
      rw [map_ofNat]
    rw [this, hA, map_zero]
  have h := P_sub_normal a
  rw [h2, zero_mul, sub_eq_zero] at h
  exact h

end coeffs

section decode

variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- The unique square root in a perfect field of characteristic 2. -/
noncomputable def sqrt (x : F) : F := (frobeniusEquiv F 2).symm x

theorem sqrt_sq (x : F) : sqrt (x ^ 2) = x := by
  rw [sqrt, show x ^ 2 = frobenius F 2 x from rfl,
    frobeniusEquiv_symm_apply_frobenius]

theorem sq_sqrt (x : F) : sqrt x ^ 2 = x := frobeniusEquiv_symm_pow_p F 2 x

omit [PerfectRing F 2] in
/-- The two-is-zero fact. -/
theorem two_eq_zero : (2 : F) = 0 := by
  have := CharP.cast_eq_zero F 2
  simpa using this

/-! The paper's recovery chain. -/

noncomputable def dA4 (p : ℕ → F) : F := p 6
noncomputable def dB (p : ℕ → F) : F := sqrt (p 5)
noncomputable def dA3 (p : ℕ → F) : F := p 4 + dA4 p * p 5
noncomputable def dC (p : ℕ → F) : F :=
  sqrt (p 3 + dA3 p * dB p + 1 + dA4 p * dA3 p)
noncomputable def dA0 (p : ℕ → F) : F :=
  p 2 + dA3 p * dC p + dA4 p * (dC p ^ 2 + dA3 p * dB p + 1)
noncomputable def dA1 (p : ℕ → F) : F := dB p + 1 + dA0 p
noncomputable def dA2 (p : ℕ → F) : F := dC p + 1 + dA0 p + dA0 p * dA1 p
noncomputable def dD (p : ℕ → F) : F := dA1 p * dA2 p
noncomputable def dA5 (p : ℕ → F) : F :=
  p 1 + dD p ^ 2 + dA3 p * dD p + dA4 p * (dA3 p * dC p + dA0 p)
noncomputable def dA6 (p : ℕ → F) : F :=
  p 0 + dA4 p * (dD p ^ 2 + dA3 p * dD p + dA5 p)

/-- The paper's key-recovery map. -/
noncomputable def decodeKeys (p : ℕ → F) : ℕ → F
  | 0 => dA0 p
  | 1 => dA1 p
  | 2 => dA2 p
  | 3 => dA3 p
  | 4 => dA4 p
  | 5 => dA5 p
  | 6 => dA6 p
  | _ + 7 => 0

/-- The recovery procedure inverts the coefficient map. -/
theorem decode_coeffMap (a : ℕ → F) :
    ∀ i, i < 7 → decodeKeys (coeffMap a) i = a i := by
  have h2 : (2 : F) = 0 := two_eq_zero
  have hb : dB (coeffMap a) = bK a := by
    rw [dB, show coeffMap a 5 = bK a ^ 2 from rfl, sqrt_sq]
  have ha4 : dA4 (coeffMap a) = a 4 := rfl
  have ha3 : dA3 (coeffMap a) = a 3 := by
    rw [dA3, ha4, show coeffMap a 4 = a 3 + a 4 * bK a ^ 2 from rfl,
      show coeffMap a 5 = bK a ^ 2 from rfl]
    linear_combination (a 4 * bK a ^ 2) * h2
  have hcarg : coeffMap a 3 + dA3 (coeffMap a) * dB (coeffMap a) + 1
      + dA4 (coeffMap a) * dA3 (coeffMap a) = cK a ^ 2 := by
    rw [ha3, ha4, hb, show coeffMap a 3
        = cK a ^ 2 + a 3 * bK a + 1 + a 4 * a 3 from rfl]
    linear_combination (a 3 * bK a + 1 + a 4 * a 3) * h2
  have hc : dC (coeffMap a) = cK a := by
    rw [dC, hcarg, sqrt_sq]
  have ha0 : dA0 (coeffMap a) = a 0 := by
    rw [dA0, ha3, ha4, hb, hc, show coeffMap a 2
        = a 3 * cK a + a 0 + a 4 * (cK a ^ 2 + a 3 * bK a + 1) from rfl]
    linear_combination (a 3 * cK a + a 4 * (cK a ^ 2 + a 3 * bK a + 1)) * h2
  have ha1 : dA1 (coeffMap a) = a 1 := by
    rw [dA1, hb, ha0, bK]
    linear_combination (1 + a 0) * h2
  have ha2 : dA2 (coeffMap a) = a 2 := by
    rw [dA2, hc, ha0, ha1, cK]
    linear_combination (1 + a 0 + a 0 * a 1) * h2
  have hd : dD (coeffMap a) = dK a := by
    rw [dD, ha1, ha2, dK]
  have ha5 : dA5 (coeffMap a) = a 5 := by
    rw [dA5, hd, ha3, ha4, hc, ha0, show coeffMap a 1
        = dK a ^ 2 + a 3 * dK a + a 5 + a 4 * (a 3 * cK a + a 0) from rfl]
    linear_combination (dK a ^ 2 + a 3 * dK a + a 4 * (a 3 * cK a + a 0)) * h2
  have ha6 : dA6 (coeffMap a) = a 6 := by
    rw [dA6, hd, ha3, ha4, ha5, show coeffMap a 0
        = a 4 * (dK a ^ 2 + a 3 * dK a + a 5) + a 6 from rfl]
    linear_combination (a 4 * (dK a ^ 2 + a 3 * dK a + a 5)) * h2
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6
      from by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ha0
  · exact ha1
  · exact ha2
  · exact ha3
  · exact ha4
  · exact ha5
  · exact ha6

/-- The coefficient map inverts the recovery procedure. -/
theorem coeffMap_decode (p : ℕ → F) :
    ∀ j, j < 7 → coeffMap (decodeKeys p) j = p j := by
  have h2 : (2 : F) = 0 := two_eq_zero
  have hb2 : dB p ^ 2 = p 5 := sq_sqrt _
  have hc2 : dC p ^ 2 = p 3 + dA3 p * dB p + 1 + dA4 p * dA3 p := sq_sqrt _
  have hbk : bK (decodeKeys p) = dB p := by
    simp only [bK, decodeKeys, dA1]
    linear_combination (1 + dA0 p) * h2
  have hck : cK (decodeKeys p) = dC p := by
    simp only [cK, decodeKeys, dA2, dA1]
    linear_combination (1 + dA0 p + dA0 p * (dB p + 1 + dA0 p)) * h2
  have hdk : dK (decodeKeys p) = dD p := by
    simp only [dK, decodeKeys, dD]
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6
      from by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · show coeffMap (decodeKeys p) 0 = p 0
    simp only [coeffMap, hdk, decodeKeys, dA6]
    linear_combination (dA4 p * (dD p ^ 2 + dA3 p * dD p + dA5 p)) * h2
  · show coeffMap (decodeKeys p) 1 = p 1
    simp only [coeffMap, hdk, hck, decodeKeys, dA5]
    linear_combination (dD p ^ 2 + dA3 p * dD p + dA4 p * (dA3 p * dC p + dA0 p))
      * h2
  · show coeffMap (decodeKeys p) 2 = p 2
    simp only [coeffMap, hck, hbk, decodeKeys, dA0]
    linear_combination (dA3 p * dC p + dA4 p * (dC p ^ 2 + dA3 p * dB p + 1)) * h2
  · show coeffMap (decodeKeys p) 3 = p 3
    simp only [coeffMap, hck, hbk, decodeKeys]
    linear_combination hc2 + (dA3 p * dB p + 1 + dA4 p * dA3 p) * h2
  · show coeffMap (decodeKeys p) 4 = p 4
    simp only [coeffMap, hbk, decodeKeys, dA3]
    linear_combination (dA4 p * p 5) * h2 + dA4 p * hb2
  · show coeffMap (decodeKeys p) 5 = p 5
    simp only [coeffMap, hbk]
    exact hb2
  · show coeffMap (decodeKeys p) 6 = p 6
    rfl

end decode

section vandermonde

variable {F : Type*} [Field F]

/-- Extension of a `Fin 7`-tuple by zero. -/
def ext7 (a : Fin 7 → F) : ℕ → F := fun j => if h : j < 7 then a ⟨j, h⟩ else 0

/-- The monic degree-7 polynomial with the given low coefficients. -/
noncomputable def monicOf (p : Fin 7 → F) : F[X] :=
  X ^ 7 + ∑ j ∈ Finset.range 7, C (ext7 p j) * X ^ j

theorem low_natDegree_le (v : ℕ → F) :
    (∑ j ∈ Finset.range 7, C (v j) * X ^ j).natDegree ≤ 6 := by
  refine le_trans (Polynomial.natDegree_sum_le _ _) ?_
  simp only [Finset.fold_max_le]
  refine ⟨by omega, ?_⟩
  intro j hj
  exact le_trans (natDegree_C_mul_X_pow_le _ _) (by
    simp only [Finset.mem_range] at hj
    omega)

theorem low_coeff (v : ℕ → F) {k : ℕ} (hk : k < 7) :
    (∑ j ∈ Finset.range 7, C (v j) * X ^ j).coeff k = v k := by
  rw [finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j _ hjk
    simp only [coeff_C_mul, coeff_X_pow]
    rw [if_neg (fun h => hjk h.symm), mul_zero]
  · intro hk'
    exact absurd (Finset.mem_range.2 hk) hk'

/-- **Monic interpolation is bijective**: at seven distinct points, the map from
the seven low coefficients to the seven values of the monic degree-7 polynomial
is a bijection. -/
theorem monicOf_eval_bijective (x : Fin 7 → F) (hx : Function.Injective x) :
    Function.Bijective (fun p : Fin 7 → F => fun i : Fin 7 =>
      (monicOf p).eval (x i)) :=
  ExplicitEvaluationInverse.evaluation_bijective (by omega) x hx

end vandermonde

section main

variable {F : Type*} [Field F] [CharP F 2] [PerfectRing F 2]

/-- The circuit's key-to-coefficient map on seven-tuples. -/
noncomputable def coeffMap7 (a : Fin 7 → F) : Fin 7 → F :=
  fun j => coeffMap (ext7 a) (j : ℕ)

theorem coeffMap7_bijective : Function.Bijective (coeffMap7 (F := F)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun p => fun i => decodeKeys (ext7 p) (i : ℕ), ?_, ?_⟩
  · intro a
    funext i
    show decodeKeys (ext7 (coeffMap7 a)) (i : ℕ) = a i
    have hcm : ext7 (coeffMap7 a) = fun j =>
        if j < 7 then coeffMap (ext7 a) j else 0 := by
      funext j
      by_cases h : j < 7
      · simp [ext7, coeffMap7, h]
      · simp [ext7, h]
    have hsame : decodeKeys (ext7 (coeffMap7 a)) (i : ℕ)
        = decodeKeys (coeffMap (ext7 a)) (i : ℕ) := by
      rw [hcm]
      have hfun : (fun j => if j < 7 then coeffMap (ext7 a) j else 0)
          = coeffMap (ext7 a) := by
        funext j
        by_cases h : j < 7
        · simp [h]
        · obtain ⟨m, rfl⟩ : ∃ m, j = m + 7 := ⟨j - 7, by omega⟩
          simp [coeffMap]
      rw [hfun]
    rw [hsame, decode_coeffMap (ext7 a) (i : ℕ) i.isLt]
    simp [ext7, i.isLt]
  · intro p
    funext j
    show coeffMap7 (fun i : Fin 7 => decodeKeys (ext7 p) (i : ℕ)) j = p j
    have hdm : ext7 (fun i : Fin 7 => decodeKeys (ext7 p) (i : ℕ))
        = decodeKeys (ext7 p) := by
      funext i
      by_cases h : i < 7
      · simp [ext7, h]
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 7 := ⟨i - 7, by omega⟩
        simp [ext7, decodeKeys]
    rw [coeffMap7, hdm, coeffMap_decode (ext7 p) (j : ℕ) j.isLt]
    simp [ext7, j.isLt]

/-- **`lem:first-char2-circuit-inverse`**: over a perfect field of characteristic 2,
the map from the seven keys of the first characteristic-2 appendix circuit to its
evaluations at seven distinct points is a bijection `F⁷ → F⁷`. -/
theorem circuit_eval_bijective (x : Fin 7 → F) (hx : Function.Injective x) :
    Function.Bijective (fun a : Fin 7 → F => fun i : Fin 7 =>
      (P (ext7 a)).eval (x i)) := by
  have hfe : (fun a : Fin 7 → F => fun i : Fin 7 => (P (ext7 a)).eval (x i))
      = (fun p : Fin 7 → F => fun i : Fin 7 => (monicOf p).eval (x i))
        ∘ coeffMap7 := by
    funext a i
    simp only [Function.comp_apply, monicOf]
    rw [P_eq_normal (ext7 a)]
    have hs : (∑ j ∈ Finset.range 7, C (coeffMap (ext7 a) j) * X ^ j)
        = ∑ j ∈ Finset.range 7, C (ext7 (coeffMap7 a) j) * X ^ j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      simp only [Finset.mem_range] at hj
      simp [coeffMap7, ext7, hj]
    rw [hs]
  rw [hfe]
  exact (monicOf_eval_bijective x hx).comp coeffMap7_bijective

end main

end FastPoly.Char2Four
