import FastPoly.Polynomial.SquareGadget

/-!
# Scalar shift from a square boundary coefficient

`lem:scalar-shift-square` of the paper: if `P = λ·(H+δ)²·M + E` with `H, M` monic and known,
`λ` a known unit, and `deg E ≤ d + e - 1` (`d = deg H ≥ 1`, `e = deg M`), then the single
coefficient `[x^{d+e}]P` determines the scalar shift `δ` (dividing by `2λ`).

This is the pivot used to recover the scalar shifts of the second branch (`S⁽²⁾`-side) in
the `T_{k,2^l}` remainder recursion.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The boundary coefficient of `(H+δ)²·M` at degree `d+e` is `[x^{d+e}](H²M) + 2δ`. -/
theorem coeff_shift_sq_mul (H M : A[X]) (δ : A) {d e : ℕ}
    (hH : H.Monic) (hd : H.natDegree = d) (hd1 : 1 ≤ d)
    (hM : M.Monic) (he : M.natDegree = e) :
    ((H + C δ) ^ 2 * M).coeff (d + e) = (H ^ 2 * M).coeff (d + e) + (1 + 1) * δ := by
  have hdiff : (H + C δ) ^ 2 * M = H ^ 2 * M + ((1 + 1) * (C δ) * (H * M) + C δ * C δ * M) := by
    rw [add_sq]; ring
  have hHM : (H * M).Monic := hH.mul hM
  have hHMdeg : (H * M).natDegree = d + e := by
    rw [hH.natDegree_mul hM, hd, he]
  have h1 : ((1 + 1) * C δ * (H * M)).coeff (d + e) = (1 + 1) * δ := by
    have : (1 + 1) * C δ * (H * M) = C δ * (H * M) + C δ * (H * M) := by ring
    rw [this, coeff_add, coeff_C_mul, ← hHMdeg, hHM.coeff_natDegree]
    ring
  have h2 : (C δ * C δ * M).coeff (d + e) = 0 := by
    rw [← map_mul, coeff_C_mul]
    rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  rw [hdiff, coeff_add, coeff_add, h1, h2, add_zero]

/-- **Scalar shift from a square boundary coefficient** (`lem:scalar-shift-square`).
If `P = C λ · (H+δ)² · M + E` with `H, M` monic whose coefficients lie in the known context
`K`, `λ` the image of a unit of `R`, and `natDegree E ≤ d + e - 1`, then `δ` is recoverable
from `K`, the single coefficient `[x^{d+e}]P`, and invertibility of `2`. -/
theorem scalar_shift_mem (K : Subalgebra R A) {H M P E : A[X]} {δ : A} {d e : ℕ}
    (hH : H.Monic) (hd : H.natDegree = d) (hd1 : 1 ≤ d)
    (hM : M.Monic) (he : M.natDegree = e)
    (hHK : ∀ j, H.coeff j ∈ K) (hMK : ∀ j, M.coeff j ∈ K)
    (lam : R) (hlam : IsUnit lam) (h2 : IsUnit (2 : R))
    (hE : E.natDegree ≤ d + e - 1)
    (hP : P = C (algebraMap R A lam) * ((H + C δ) ^ 2 * M) + E) :
    δ ∈ K ⊔ adjoin R {P.coeff (d + e)} := by
  set V := K ⊔ adjoin R {P.coeff (d + e)} with hV
  have hKV : K ≤ V := le_sup_left
  have hPmem : P.coeff (d + e) ∈ V :=
    (le_sup_right : adjoin R {P.coeff (d + e)} ≤ V) (subset_adjoin rfl)
  have hEz : E.coeff (d + e) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
  -- the coefficient identity
  have hcoeff : P.coeff (d + e) =
      algebraMap R A lam * ((H ^ 2 * M).coeff (d + e) + (1 + 1) * δ) := by
    rw [hP, coeff_add, hEz, add_zero, coeff_C_mul,
      coeff_shift_sq_mul H M δ hH hd hd1 hM he]
  -- the known part: [x^{d+e}](H²M)
  have hknown : (H ^ 2 * M).coeff (d + e) ∈ K := by
    have := coeff_mul_mem K (p := H ^ 2) (q := M)
      (fun j => by rw [sq]; exact coeff_mul_mem K hHK hHK j) hMK (d + e)
    exact this
  -- solve: δ = (2λ)⁻¹ (P_{d+e} - λ·[x^{d+e}](H²M))
  obtain ⟨u, hu⟩ := hlam
  obtain ⟨v, hv⟩ := h2
  have hlam2 : algebraMap R A ↑u⁻¹ * algebraMap R A lam = 1 := by
    rw [← map_mul, ← hu, Units.inv_mul, map_one]
  have h2A : algebraMap R A ↑v⁻¹ * (1 + 1 : A) = 1 := by
    have : ((1 : A) + 1) = algebraMap R A 2 := by rw [map_ofNat]; norm_num
    rw [this, ← map_mul, ← hv, Units.inv_mul, map_one]
  have hkey : δ = algebraMap R A ↑v⁻¹ *
      (algebraMap R A ↑u⁻¹ * P.coeff (d + e) - (H ^ 2 * M).coeff (d + e)) := by
    rw [hcoeff, ← mul_assoc, hlam2, one_mul, add_sub_cancel_left, ← mul_assoc,
      mul_comm (algebraMap R A ↑v⁻¹) (1 + 1 : A), mul_assoc]
    rw [show (1 + 1 : A) * (algebraMap R A ↑v⁻¹ * δ) =
      (algebraMap R A ↑v⁻¹ * (1 + 1 : A)) * δ by ring, h2A, one_mul]
  rw [hkey]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.sub_mem _
      (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hPmem)
      (hKV hknown))

end FastPoly
