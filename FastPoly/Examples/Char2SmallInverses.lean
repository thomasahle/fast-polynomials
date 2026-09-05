import FastPoly.Polynomial.MonicEvaluation

/-!
# Explicit characteristic-two inverse in degree 9

The definitions here transcribe the separately optimized circuits in display (A.0)
of the manuscript.  Decoder proofs follow the displayed recovery chains.
-/

namespace FastPoly.Char2Small

open Polynomial

universe u

section Nine

variable {F : Type u} [Field F] [CharP F 2]

/-- The five-product degree-nine circuit in display (A.0). -/
noncomputable def P9 (a : ℕ → F) : F[X] :=
  let y := X * (X + C (a 0))
  let z := X * (y + C (a 1))
  let t := (y + z + C (a 2)) * (z + C (a 3))
  let u := (X + z + C (a 4)) * (t + C (a 5))
  let v := (y + C (a 6)) * (z + C (a 7))
  u + v + C (a 8)

omit [CharP F 2] in
theorem P9_monic_normal (a : ℕ → F) :
    P9 a = X ^ 9 + (P9 a - X ^ 9) := by ring

private theorem two_eq_zero : (2 : F) = 0 := by
  simpa using (CharP.cast_eq_zero F 2)

/-- Low coefficients of the degree-nine circuit, reduced in characteristic two. -/
def coeffMap9 (a : ℕ → F) : ℕ → F
  | 0 => a 2 * a 3 * a 4 + a 4 * a 5 + a 6 * a 7 + a 8
  | 1 => a 0 * a 3 * a 4 + a 0 * a 7 + a 1 * a 2 * a 3 +
      a 1 * a 2 * a 4 + a 1 * a 3 * a 4 + a 1 * a 5 + a 1 * a 6 +
      a 2 * a 3 + a 5
  | 2 => a 0 * a 1 * a 3 + a 0 * a 1 * a 4 + a 0 * a 1 +
      a 0 * a 2 * a 3 + a 0 * a 2 * a 4 + a 0 * a 3 * a 4 +
      a 0 * a 3 + a 0 * a 5 + a 0 * a 6 + a 1 ^ 2 * a 2 +
      a 1 ^ 2 * a 3 + a 1 ^ 2 * a 4 + a 1 * a 2 + a 1 * a 3 +
      a 3 * a 4 + a 7
  | 3 => a 0 ^ 2 * a 3 + a 0 ^ 2 * a 4 + a 0 ^ 2 + a 0 * a 1 ^ 2 +
      a 0 * a 1 + a 0 * a 2 + a 0 * a 3 + a 1 ^ 3 + a 1 ^ 2 +
      a 1 * a 3 + a 1 * a 4 + a 1 + a 2 * a 3 + a 2 * a 4 +
      a 3 * a 4 + a 3 + a 5 + a 6
  | 4 => a 0 ^ 2 * a 2 + a 0 ^ 2 * a 3 + a 0 ^ 2 * a 4 + a 0 ^ 2 +
      a 0 * a 1 ^ 2 + a 1 ^ 2 + a 1 + a 2 + a 3
  | 5 => a 0 ^ 3 + a 0 ^ 2 * a 1 + a 0 ^ 2 + a 1 ^ 2 + a 3 + a 4 + 1
  | 6 => a 0 ^ 3 + a 0 ^ 2 + a 2 + a 3 + a 4 + 1
  | 7 => a 0 ^ 2 + a 0 + a 1 + 1
  | 8 => a 0 + 1
  | _ + 9 => 0

/-- Characteristic-two defect of `P9` against `coeffMap9`. -/
noncomputable def J9 (a : ℕ → F) : F[X] :=
  C (a 0) * X ^ 8 +
  C (a 0 ^ 2 + a 0 + a 1) * X ^ 7 +
  C (a 0 ^ 2 + 3 * (a 0 * a 1) + a 0 + a 1) * X ^ 6 +
  C (a 0 ^ 2 * a 1 + 2 * (a 0 * a 1) + a 0 * a 2 + a 0 * a 3 +
      a 0 * a 4 + a 0 + a 1 ^ 2 + a 1) * X ^ 5 +
  C (a 0 ^ 2 * a 1 + a 0 * a 1 ^ 2 + a 0 * a 1 + a 0 * a 3 +
      a 0 * a 4 + a 0 + a 1 * a 2 + a 1 * a 3 + a 1 * a 4) * X ^ 4 +
  C (a 0 * a 1 * a 2 + a 0 * a 1 * a 3 + a 0 * a 1 * a 4) * X ^ 3

omit [CharP F 2] in
/-- Exact polynomial certificate: all discarded integer coefficients are twice
the explicit defect `J9`. -/
theorem P9_sub_normal (a : ℕ → F) :
    P9 a - (X ^ 9 + ∑ j ∈ Finset.range 9, C (coeffMap9 a j) * X ^ j) =
      2 * J9 a := by
  simp only [P9, coeffMap9, J9, Finset.sum_range_succ, Finset.sum_range_zero,
    map_add, map_mul, map_one, map_pow, map_ofNat]
  ring

/-- In characteristic two the displayed circuit has exactly `coeffMap9`. -/
theorem P9_eq_normal (a : ℕ → F) :
    P9 a = X ^ 9 + ∑ j ∈ Finset.range 9, C (coeffMap9 a j) * X ^ j := by
  have h2F : (2 : F[X]) = 0 := by
    rw [show (2 : F[X]) = C (2 : F) by rw [map_ofNat], two_eq_zero, map_zero]
  have h := P9_sub_normal a
  rw [h2F, zero_mul, sub_eq_zero] at h
  exact h

/-! The explicit unit-pivot decoder (9.1)--(9.3). -/

noncomputable def d9a0 (p : ℕ → F) : F := p 8 + 1
noncomputable def d9a1 (p : ℕ → F) : F := p 7 + 1 + d9a0 p + d9a0 p ^ 2
noncomputable def d9r (p : ℕ → F) : F := p 6 + 1 + d9a0 p ^ 2 + d9a0 p ^ 3
noncomputable def d9s (p : ℕ → F) : F :=
  p 5 + 1 + d9a0 p ^ 2 + d9a0 p ^ 3 + d9a0 p ^ 2 * d9a1 p + d9a1 p ^ 2
noncomputable def d9q (p : ℕ → F) : F :=
  p 4 + d9a0 p ^ 2 + d9a0 p ^ 2 * d9r p + d9a0 p * d9a1 p ^ 2 +
    d9a1 p + d9a1 p ^ 2
noncomputable def d9a2 (p : ℕ → F) : F := d9r p + d9s p
noncomputable def d9a3 (p : ℕ → F) : F := d9q p + d9a2 p
noncomputable def d9a4 (p : ℕ → F) : F := d9s p + d9a3 p

noncomputable def d9baseKeys (p : ℕ → F) : ℕ → F
  | 0 => d9a0 p
  | 1 => d9a1 p
  | 2 => d9a2 p
  | 3 => d9a3 p
  | 4 => d9a4 p
  | _ + 5 => 0

noncomputable def d9b (p : ℕ → F) (j : ℕ) : F := coeffMap9 (d9baseKeys p) j
noncomputable def d9h (p : ℕ → F) : F := p 3 + d9b p 3
noncomputable def d9a7 (p : ℕ → F) : F := p 2 + d9b p 2 + d9a0 p * d9h p
noncomputable def d9a5 (p : ℕ → F) : F :=
  p 1 + d9b p 1 + d9a1 p * d9h p + d9a0 p * d9a7 p
noncomputable def d9a6 (p : ℕ → F) : F := d9h p + d9a5 p
noncomputable def d9a8 (p : ℕ → F) : F :=
  p 0 + d9b p 0 + d9a4 p * d9a5 p + d9a6 p * d9a7 p

/-- The paper's degree-nine key decoder. -/
noncomputable def decodeKeys9 (p : ℕ → F) : ℕ → F
  | 0 => d9a0 p
  | 1 => d9a1 p
  | 2 => d9a2 p
  | 3 => d9a3 p
  | 4 => d9a4 p
  | 5 => d9a5 p
  | 6 => d9a6 p
  | 7 => d9a7 p
  | 8 => d9a8 p
  | _ + 9 => 0

private theorem coeffMap9_residual_three (a : ℕ → F) :
    coeffMap9 a 3 + coeffMap9 (fun i => if i < 5 then a i else 0) 3 = a 5 + a 6 := by
  have h2 : (2 : F) = 0 := two_eq_zero
  simp only [coeffMap9]
  simp
  ring_nf
  simp [h2]

private theorem coeffMap9_residual_two (a : ℕ → F) :
    coeffMap9 a 2 + coeffMap9 (fun i => if i < 5 then a i else 0) 2 =
      a 7 + a 0 * (a 5 + a 6) := by
  have h2 : (2 : F) = 0 := two_eq_zero
  simp only [coeffMap9]
  simp
  ring_nf
  simp [h2]

private theorem coeffMap9_residual_one (a : ℕ → F) :
    coeffMap9 a 1 + coeffMap9 (fun i => if i < 5 then a i else 0) 1 =
      a 5 + a 1 * (a 5 + a 6) + a 0 * a 7 := by
  have h2 : (2 : F) = 0 := two_eq_zero
  simp only [coeffMap9]
  simp
  ring_nf
  simp [h2]

private theorem coeffMap9_residual_zero (a : ℕ → F) :
    coeffMap9 a 0 + coeffMap9 (fun i => if i < 5 then a i else 0) 0 =
      a 8 + a 4 * a 5 + a 6 * a 7 := by
  have h2 : (2 : F) = 0 := two_eq_zero
  simp only [coeffMap9]
  simp
  ring_nf
  simp [h2]

/-- Equations (9.1)--(9.3) recover every key of the displayed circuit. -/
theorem decodeKeys9_coeffMap9 (a : ℕ → F) :
    ∀ i, i < 9 → decodeKeys9 (coeffMap9 a) i = a i := by
  have h2 : (2 : F) = 0 := two_eq_zero
  have ha0 : d9a0 (coeffMap9 a) = a 0 := by
    simp only [d9a0, coeffMap9]
    ring_nf
    simp [h2]
  have ha1 : d9a1 (coeffMap9 a) = a 1 := by
    simp only [d9a1, ha0, coeffMap9]
    ring_nf
    simp [h2]
  have hr : d9r (coeffMap9 a) = a 2 + a 3 + a 4 := by
    simp only [d9r, ha0, coeffMap9]
    ring_nf
    simp [h2]
  have hs : d9s (coeffMap9 a) = a 3 + a 4 := by
    simp only [d9s, ha0, ha1, coeffMap9]
    ring_nf
    simp [h2]
  have hq : d9q (coeffMap9 a) = a 2 + a 3 := by
    simp only [d9q, ha0, ha1, hr, coeffMap9]
    ring_nf
    simp [h2]
  have ha2 : d9a2 (coeffMap9 a) = a 2 := by
    simp only [d9a2, hr, hs]
    ring_nf
    simp [h2]
  have ha3 : d9a3 (coeffMap9 a) = a 3 := by
    simp only [d9a3, hq, ha2]
    ring_nf
    simp [h2]
  have ha4 : d9a4 (coeffMap9 a) = a 4 := by
    simp only [d9a4, hs, ha3]
    ring_nf
    simp [h2]
  have hbase : d9baseKeys (coeffMap9 a) = fun i => if i < 5 then a i else 0 := by
    funext i
    by_cases hi : i < 5
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 from by omega)
        with rfl | rfl | rfl | rfl | rfl
      all_goals simp [d9baseKeys, ha0, ha1, ha2, ha3, ha4]
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 5 := ⟨i - 5, by omega⟩
      simp [d9baseKeys]
  have hb (j : ℕ) : d9b (coeffMap9 a) j =
      coeffMap9 (fun i => if i < 5 then a i else 0) j := by
    rw [d9b, hbase]
  have hh : d9h (coeffMap9 a) = a 5 + a 6 := by
    rw [d9h, hb, coeffMap9_residual_three]
  have ha7 : d9a7 (coeffMap9 a) = a 7 := by
    rw [d9a7, hb, ha0, hh, coeffMap9_residual_two]
    ring_nf
    simp [h2]
  have ha5 : d9a5 (coeffMap9 a) = a 5 := by
    rw [d9a5, hb, ha0, ha1, hh, ha7, coeffMap9_residual_one]
    ring_nf
    simp [h2]
  have ha6 : d9a6 (coeffMap9 a) = a 6 := by
    rw [d9a6, hh, ha5]
    ring_nf
    simp [h2]
  have ha8 : d9a8 (coeffMap9 a) = a 8 := by
    rw [d9a8, hb, ha4, ha5, ha6, ha7, coeffMap9_residual_zero]
    ring_nf
    simp [h2]
  intro i hi
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨
      i = 7 ∨ i = 8 from by omega) with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
  all_goals simp only [decodeKeys9, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8]

/-- Conversely, the same explicit recurrence realizes every low-coefficient
vector; this is the encode-after-decode half of bijectivity. -/
theorem coeffMap9_decodeKeys9 (p : ℕ → F) :
    ∀ j, j < 9 → coeffMap9 (decodeKeys9 p) j = p j := by
  have h2 : (2 : F) = 0 := two_eq_zero
  have hdouble (x : F) : x * 2 = 0 := by rw [h2, mul_zero]
  have hrsum : d9a2 p + d9a3 p + d9a4 p = d9r p := by
    simp only [d9a2, d9a3, d9a4]
    linear_combination (d9s p + d9q p + d9r p + d9s p) * h2
  have hssum : d9a3 p + d9a4 p = d9s p := by
    simp only [d9a3, d9a4]
    linear_combination (d9q p + d9a2 p) * h2
  have hqsum : d9a2 p + d9a3 p = d9q p := by
    simp only [d9a3]
    linear_combination (d9a2 p) * h2
  have hrdef : d9r p = p 6 + 1 + d9a0 p ^ 2 + d9a0 p ^ 3 := rfl
  have hsdef : d9s p = p 5 + 1 + d9a0 p ^ 2 + d9a0 p ^ 3 +
      d9a0 p ^ 2 * d9a1 p + d9a1 p ^ 2 := rfl
  have hqdef : d9q p = p 4 + d9a0 p ^ 2 + d9a0 p ^ 2 * d9r p +
      d9a0 p * d9a1 p ^ 2 + d9a1 p + d9a1 p ^ 2 := rfl
  have h8 : coeffMap9 (decodeKeys9 p) 8 = p 8 := by
    simp only [coeffMap9, decodeKeys9, d9a0]
    linear_combination h2
  have h7 : coeffMap9 (decodeKeys9 p) 7 = p 7 := by
    simp only [coeffMap9, decodeKeys9]
    rw [d9a1]
    linear_combination (1 + d9a0 p + d9a0 p ^ 2) * h2
  have h6 : coeffMap9 (decodeKeys9 p) 6 = p 6 := by
    simp only [coeffMap9, decodeKeys9]
    linear_combination hrsum +
      (1 + d9a0 p ^ 2 + d9a0 p ^ 3) * h2 + hrdef
  have h5 : coeffMap9 (decodeKeys9 p) 5 = p 5 := by
    simp only [coeffMap9, decodeKeys9]
    linear_combination hssum +
      (1 + d9a0 p ^ 2 + d9a0 p ^ 3 + d9a0 p ^ 2 * d9a1 p +
        d9a1 p ^ 2) * h2 + hsdef
  have h4 : coeffMap9 (decodeKeys9 p) 4 = p 4 := by
    simp only [coeffMap9, decodeKeys9]
    linear_combination d9a0 p ^ 2 * hrsum + hqsum +
      (d9a0 p ^ 2 + d9a0 p ^ 2 * d9r p + d9a0 p * d9a1 p ^ 2 +
        d9a1 p + d9a1 p ^ 2) * h2 + hqdef
  have htrunc : (fun i => if i < 5 then decodeKeys9 p i else 0) = d9baseKeys p := by
    funext i
    by_cases hi : i < 5
    · rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 from by omega)
        with rfl | rfl | rfl | rfl | rfl
      all_goals simp [decodeKeys9, d9baseKeys]
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 5 := ⟨i - 5, by omega⟩
      simp [d9baseKeys]
  have hb (j : ℕ) :
      coeffMap9 (fun i => if i < 5 then decodeKeys9 p i else 0) j = d9b p j := by
    rw [htrunc, d9b]
  have h3 : coeffMap9 (decodeKeys9 p) 3 = p 3 := by
    have hres := coeffMap9_residual_three (decodeKeys9 p)
    rw [hb 3] at hres
    simp only [decodeKeys9] at hres
    rw [d9a6, d9h] at hres
    linear_combination hres + hdouble (d9a5 p)
  have hh : d9a5 p + d9a6 p = d9h p := by
    rw [d9a6]
    linear_combination (d9a5 p) * h2
  have h2c : coeffMap9 (decodeKeys9 p) 2 = p 2 := by
    have hres := coeffMap9_residual_two (decodeKeys9 p)
    rw [hb 2] at hres
    simp only [decodeKeys9] at hres
    rw [hh, d9a7] at hres
    linear_combination hres + hdouble (d9a0 p * d9h p)
  have h1 : coeffMap9 (decodeKeys9 p) 1 = p 1 := by
    have hres := coeffMap9_residual_one (decodeKeys9 p)
    rw [hb 1] at hres
    simp only [decodeKeys9] at hres
    rw [hh, d9a5] at hres
    linear_combination hres + hdouble (d9a1 p * d9h p + d9a0 p * d9a7 p)
  have h0 : coeffMap9 (decodeKeys9 p) 0 = p 0 := by
    have hres := coeffMap9_residual_zero (decodeKeys9 p)
    rw [hb 0] at hres
    simp only [decodeKeys9] at hres
    rw [d9a8] at hres
    linear_combination hres + hdouble (d9a4 p * d9a5 p + d9a6 p * d9a7 p)
  intro j hj
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨
      j = 7 ∨ j = 8 from by omega) with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
  all_goals assumption

/-- Coefficient map on finite vectors. -/
noncomputable def coeffMap9Fin (a : Fin 9 → F) : Fin 9 → F :=
  fun j => coeffMap9 (extendFin a) (j : ℕ)

/-- **Degree-nine coefficient bijection** from the explicit inverse (9.1)--(9.3). -/
theorem coeffMap9Fin_bijective : Function.Bijective (coeffMap9Fin (F := F)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun p => fun i => decodeKeys9 (extendFin p) (i : ℕ), ?_, ?_⟩
  · intro a
    funext i
    have hext : extendFin (coeffMap9Fin a) = coeffMap9 (extendFin a) := by
      funext j
      by_cases hj : j < 9
      · simp [extendFin, coeffMap9Fin, hj]
      · obtain ⟨m, rfl⟩ : ∃ m, j = m + 9 := ⟨j - 9, by omega⟩
        simp [extendFin, coeffMap9]
    change decodeKeys9 (extendFin (coeffMap9Fin a)) (i : ℕ) = a i
    rw [hext, decodeKeys9_coeffMap9 (extendFin a) (i : ℕ) i.isLt]
    simp [extendFin, i.isLt]
  · intro p
    funext j
    have hext : extendFin (fun i : Fin 9 => decodeKeys9 (extendFin p) (i : ℕ)) =
        decodeKeys9 (extendFin p) := by
      funext i
      by_cases hi : i < 9
      · simp [extendFin, hi]
      · obtain ⟨m, rfl⟩ : ∃ m, i = m + 9 := ⟨i - 9, by omega⟩
        simp [extendFin, decodeKeys9]
    rw [coeffMap9Fin, hext, coeffMap9_decodeKeys9 (extendFin p) (j : ℕ) j.isLt]
    simp [extendFin, j.isLt]

/-- **Degree-nine evaluation bijection.**  At nine distinct points, the five-product
circuit is a bijective parametrisation of the evaluation vector. -/
theorem P9_eval_bijective (x : Fin 9 → F) (hx : Function.Injective x) :
    Function.Bijective (fun a : Fin 9 → F => fun i : Fin 9 =>
      (P9 (extendFin a)).eval (x i)) := by
  have hfactor : (fun a : Fin 9 → F => fun i : Fin 9 =>
      (P9 (extendFin a)).eval (x i)) =
      (fun p : Fin 9 → F => fun i : Fin 9 =>
        (monicOfCoefficients p).eval (x i)) ∘ coeffMap9Fin := by
    funext a i
    simp only [Function.comp_apply, monicOfCoefficients]
    rw [P9_eq_normal]
    congr 2
  rw [hfactor]
  exact (monicOfCoefficients_eval_bijective (F := F) (by omega) x hx).comp
    coeffMap9Fin_bijective

end Nine

end FastPoly.Char2Small
