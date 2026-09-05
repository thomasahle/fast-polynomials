import FastPoly.Polynomial.CausalShell
import FastPoly.Section4.FillRec
import FastPoly.Section4.Peeled

/-!
# The degree-15 special construction

The causal proof is deliberately parametric in an opaque monic septic `Q`.  It first
recovers the *outer shell* (`Q`, `H₂`, `H₄`, and the eight outer scalars) by the paper's
descending decoder.  Compatibility then follows from coefficient schedules via the generic
Cauchy-product lemma in `SpecialTopDown`.  Only the final specialization instantiates `Q`
with the conditionally decodable Mersenne gadget `Q₇`.
-/

namespace FastPoly.P15

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

noncomputable def H2 (a : ℕ → A) : A[X] :=
  (X + C (a 7)) * X + C (a 6)

noncomputable def H4 (a : ℕ → A) : A[X] :=
  (H2 a + (X + C (a 5))) * (H2 a - (X + C (a 5))) + C (a 4)

noncomputable def U (a : ℕ → A) : A[X] := H2 a + C (a 3)
noncomputable def W (a : ℕ → A) : A[X] := H2 a + C (a 2)

noncomputable def T1 (a : ℕ → A) (Q : A[X]) : A[X] :=
  Q ^ 2 - U a ^ 2 + C (a 1)

noncomputable def T2 (a : ℕ → A) (Q : A[X]) : A[X] :=
  T1 a Q + H4 a ^ 2 - W a ^ 2 + C (a 0)

noncomputable def Phi (a : ℕ → A) (Q : A[X]) : A[X] := combined (T1 a Q) (T2 a Q)

noncomputable def V (K : Subalgebra R A) (a : ℕ → A) (Q : A[X]) (t : ℕ) :
    Subalgebra R A := Vis R K (Phi a Q) (range 15) t

/-- The error below the leading `(X+1)Q²` block. -/
noncomputable def E (a : ℕ → A) : A[X] :=
  H4 a ^ 2 - (X + 1) * U a ^ 2 - W a ^ 2 + (X + 1) * C (a 1) + C (a 0)

/-- The bottom residual after the `H₄²` block is removed. -/
noncomputable def L (a : ℕ → A) : A[X] :=
  -(X + 1) * U a ^ 2 - W a ^ 2 + (X + 1) * C (a 1) + C (a 0)

def h3 (a : ℕ → A) : A := 2 * a 7
def h2 (a : ℕ → A) : A := a 7 ^ 2 + 2 * a 6 - 1
def h1 (a : ℕ → A) : A := 2 * a 7 * a 6 - 2 * a 5
def h0 (a : ℕ → A) : A := a 6 ^ 2 - a 5 ^ 2 + a 4
def d3 (a : ℕ → A) : A := a 6 + a 3
def d2 (a : ℕ → A) : A := a 6 + a 2

theorem H2_eq (a : ℕ → A) :
    H2 a = X ^ 2 + C (a 7) * X + C (a 6) := by
  simp only [H2]
  ring

theorem H4_eq (a : ℕ → A) :
    H4 a = X ^ 4 + C (h3 a) * X ^ 3 + C (h2 a) * X ^ 2 +
      C (h1 a) * X + C (h0 a) := by
  simp only [H4, H2, h3, h2, h1, h0, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat]
  ring

theorem U_eq (a : ℕ → A) :
    U a = X ^ 2 + C (a 7) * X + C (d3 a) := by
  simp only [U, H2, d3, map_add]
  ring

theorem W_eq (a : ℕ → A) :
    W a = X ^ 2 + C (a 7) * X + C (d2 a) := by
  simp only [W, H2, d2, map_add]
  ring

theorem H2_natDegree_le (a : ℕ → A) : (H2 a).natDegree ≤ 2 := by
  have hlin : (X + C (a 7) : A[X]).natDegree ≤ 1 :=
    le_trans (natDegree_add_le _ _)
      (max_le natDegree_X_le (by rw [natDegree_C]; omega))
  rw [H2]
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans natDegree_mul_le (by have := natDegree_X_le (R := A); omega)
  · rw [natDegree_C]
    omega

theorem U_natDegree_le (a : ℕ → A) : (U a).natDegree ≤ 2 := by
  rw [U]
  exact le_trans (natDegree_add_le _ _)
    (max_le (H2_natDegree_le a) (by rw [natDegree_C]; omega))

theorem W_natDegree_le (a : ℕ → A) : (W a).natDegree ≤ 2 := by
  rw [W]
  exact le_trans (natDegree_add_le _ _)
    (max_le (H2_natDegree_le a) (by rw [natDegree_C]; omega))

theorem H4_natDegree_le (a : ℕ → A) : (H4 a).natDegree ≤ 4 := by
  have hlin : (X + C (a 5) : A[X]).natDegree ≤ 1 :=
    le_trans (natDegree_add_le _ _)
      (max_le natDegree_X_le (by rw [natDegree_C]; omega))
  have hp : (H2 a + (X + C (a 5))).natDegree ≤ 2 :=
    le_trans (natDegree_add_le _ _) (max_le (H2_natDegree_le a) (by omega))
  have hm : (H2 a - (X + C (a 5))).natDegree ≤ 2 :=
    le_trans (natDegree_sub_le _ _) (max_le (H2_natDegree_le a) (by omega))
  rw [H4]
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · exact le_trans natDegree_mul_le (by omega)
  · rw [natDegree_C]
    omega

theorem Phi_eq (a : ℕ → A) (Q : A[X]) :
    Phi a Q = (X + 1) * Q ^ 2 + E a := by
  simp only [Phi, T1, T2, E, combined]
  ring

theorem L_eq_E_sub (a : ℕ → A) : L a = E a - H4 a ^ 2 := by
  simp only [L, E]
  ring

/-- Full expansion used only to certify the finite seam rows. -/
theorem E_eq (a : ℕ → A) :
    E a =
      X ^ 8
      + C (2 * h3 a) * X ^ 7
      + C (h3 a ^ 2 + 2 * h2 a) * X ^ 6
      + C (2 * h1 a + 2 * h3 a * h2 a - 1) * X ^ 5
      + C (2 * h0 a + 2 * h3 a * h1 a + h2 a ^ 2 - 2 * a 7 - 2) * X ^ 4
      + C (2 * h3 a * h0 a + 2 * h2 a * h1 a - a 7 ^ 2 - 4 * a 7 - 2 * d3 a) * X ^ 3
      + C (2 * h2 a * h0 a + h1 a ^ 2 - 2 * a 7 ^ 2 - 2 * d3 a
          - 2 * a 7 * d3 a - 2 * d2 a) * X ^ 2
      + C (2 * h1 a * h0 a + a 1 - 2 * a 7 * d3 a - d3 a ^ 2
          - 2 * a 7 * d2 a) * X
      + C (h0 a ^ 2 + a 1 + a 0 - d3 a ^ 2 - d2 a ^ 2) := by
  simp only [E, H4_eq, U_eq, W_eq, map_add, map_sub, map_mul, map_pow, map_one,
    map_ofNat]
  ring

theorem L_eq (a : ℕ → A) :
    L a =
      -X ^ 5
      + C (-2 * a 7 - 2) * X ^ 4
      + C (-a 7 ^ 2 - 4 * a 7 - 2 * d3 a) * X ^ 3
      + C (-2 * a 7 ^ 2 - 2 * d3 a - 2 * a 7 * d3 a - 2 * d2 a) * X ^ 2
      + C (a 1 - 2 * a 7 * d3 a - d3 a ^ 2 - 2 * a 7 * d2 a) * X
      + C (a 1 + a 0 - d3 a ^ 2 - d2 a ^ 2) := by
  simp only [L, U_eq, W_eq, map_add, map_sub, map_neg, map_mul, map_pow,
    map_ofNat]
  ring

theorem E_coeff_8 (a : ℕ → A) : (E a).coeff 8 = 1 := by
  rw [E_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E_coeff_7 (a : ℕ → A) : (E a).coeff 7 = 2 * h3 a := by
  rw [E_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E_coeff_6 (a : ℕ → A) : (E a).coeff 6 = h3 a ^ 2 + 2 * h2 a := by
  rw [E_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E_coeff_5 (a : ℕ → A) :
    (E a).coeff 5 = 2 * h1 a + 2 * h3 a * h2 a - 1 := by
  rw [E_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E_coeff_4 (a : ℕ → A) :
    (E a).coeff 4 = 2 * h0 a + 2 * h3 a * h1 a + h2 a ^ 2 - 2 * a 7 - 2 := by
  rw [E_eq]
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem E_natDegree_le (a : ℕ → A) : (E a).natDegree ≤ 8 := by
  have hHsq : (H4 a ^ 2).natDegree ≤ 8 :=
    le_trans natDegree_pow_le (by have := H4_natDegree_le a; omega)
  have hX1 : (X + 1 : A[X]).natDegree ≤ 1 :=
    le_trans (natDegree_add_le _ _)
      (max_le natDegree_X_le (by rw [natDegree_one]; omega))
  have hUsq : (U a ^ 2).natDegree ≤ 4 :=
    le_trans natDegree_pow_le (by have := U_natDegree_le a; omega)
  have hWsq : (W a ^ 2).natDegree ≤ 4 :=
    le_trans natDegree_pow_le (by have := W_natDegree_le a; omega)
  have hXU : ((X + 1) * U a ^ 2).natDegree ≤ 5 :=
    le_trans natDegree_mul_le (by omega)
  have hXa : ((X + 1) * C (a 1)).natDegree ≤ 1 := by
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C]
    omega
  have h1 : (H4 a ^ 2 - (X + 1) * U a ^ 2).natDegree ≤ 8 :=
    le_trans (natDegree_sub_le _ _) (max_le hHsq (by omega))
  have h2' : (H4 a ^ 2 - (X + 1) * U a ^ 2 - W a ^ 2).natDegree ≤ 8 :=
    le_trans (natDegree_sub_le _ _) (max_le h1 (by omega))
  have h3' : (H4 a ^ 2 - (X + 1) * U a ^ 2 - W a ^ 2 +
      (X + 1) * C (a 1)).natDegree ≤ 8 :=
    le_trans (natDegree_add_le _ _) (max_le h2' (by omega))
  rw [E]
  exact le_trans (natDegree_add_le _ _)
    (max_le h3' (by rw [natDegree_C]; omega))

theorem E_coeff_zero_above (a : ℕ → A) (i : ℕ) (hi : 8 < i) : (E a).coeff i = 0 := by
  exact coeff_eq_zero_of_natDegree_lt (by have := E_natDegree_le a; omega)

theorem L_coeff_3 (a : ℕ → A) :
    (L a).coeff 3 = -a 7 ^ 2 - 4 * a 7 - 2 * d3 a := by
  rw [L_eq]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem L_coeff_2 (a : ℕ → A) :
    (L a).coeff 2 = -2 * a 7 ^ 2 - 2 * d3 a - 2 * a 7 * d3 a - 2 * d2 a := by
  rw [L_eq]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem L_coeff_1 (a : ℕ → A) :
    (L a).coeff 1 = a 1 - 2 * a 7 * d3 a - d3 a ^ 2 - 2 * a 7 * d2 a := by
  rw [L_eq]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

theorem L_coeff_0 (a : ℕ → A) :
    (L a).coeff 0 = a 1 + a 0 - d3 a ^ 2 - d2 a ^ 2 := by
  rw [L_eq]
  simp only [coeff_add, coeff_neg, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- The compact output of the outer-shell decoder. -/
structure OuterCert (K : Subalgebra R A) (a : ℕ → A) (Q : A[X]) : Prop where
  low : ∀ i, i < 8 → a i ∈ V K a Q i
  qcoeff : ∀ j, Q.coeff j ∈ V K a Q (j + 8)
  h2coeff : ∀ j, (H2 a).coeff j ∈ V K a Q (j + 6)
  h4coeff : ∀ j, (H4 a).coeff j ∈ V K a Q (j + 4)

theorem V_antitone (K : Subalgebra R A) (a : ℕ → A) (Q : A[X]) :
    Antitone (V K a Q) := by
  intro i j hij
  exact Vis_antitone_cutoff hij

/-- The explicit descending outer-shell decoder for degree 15. -/
theorem outer_recover [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A) (Q : A[X])
    (htwo : IsUnit (2 : R)) (hQm : Q.Monic) (hQd : Q.natDegree = 7) :
    OuterCert K a Q := by
  have hq : ∀ j, Q.coeff j ∈ V K a Q (j + 8) := by
    intro j
    have hh := coeff_mem_of_X_add_one_mul_sq K hQm hQd htwo
      (fun i hi => E_coeff_zero_above a i (by omega))
      (show (E a).coeff 8 ∈ K by rw [E_coeff_8]; exact Subalgebra.one_mem _)
      (Phi_eq a Q) j
    simpa only [show 7 + j + 1 = j + 8 by omega] using hh
  have hanti := V_antitone K a Q
  have lower : ∀ {x : A} {s t : ℕ}, t ≤ s → x ∈ V K a Q s → x ∈ V K a Q t :=
    by
      intro x s t hst hx
      exact hanti hst hx
  have hQsq : ∀ j, (Q ^ 2).coeff j ∈ V K a Q (j + 1) := by
    refine coeff_sq_mem_of_schedule (V K a Q) hanti (le_of_eq hQd) ?_
    intro i
    simpa only [show i + 7 + 1 = i + 8 by omega] using hq i
  have hXQsq : ∀ j, ((X + 1) * Q ^ 2).coeff j ∈ V K a Q j :=
    coeff_X_add_one_mul_mem_of_schedule (V K a Q) hanti hQsq
  have hEvis : ∀ i, i < 15 → (E a).coeff i ∈ V K a Q i := by
    intro i hi
    have hphi : (Phi a Q).coeff i ∈ V K a Q i :=
      coeff_mem_Vis (mem_range.2 hi) le_rfl
    have hkey : (E a).coeff i = (Phi a Q).coeff i - ((X + 1) * Q ^ 2).coeff i := by
      rw [Phi_eq, coeff_add]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ hphi (hXQsq i)
  -- Upper four rows: H₄, then the parameters used to construct H₂ and H₄.
  have hh3 : h3 a ∈ V K a Q 7 :=
    mem_of_two_mul_eq htwo (hEvis 7 (by omega)) (by rw [E_coeff_7])
  have ha7 : a 7 ∈ V K a Q 7 :=
    mem_of_two_mul_eq htwo hh3 (by rw [h3])
  have hh3_6 : h3 a ∈ V K a Q 6 := lower (by omega) hh3
  have htwoh2 : 2 * h2 a ∈ V K a Q 6 := by
    have hkey : 2 * h2 a = (E a).coeff 6 - h3 a * h3 a := by
      rw [E_coeff_6]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hEvis 6 (by omega))
      (Subalgebra.mul_mem _ hh3_6 hh3_6)
  have hh2 : h2 a ∈ V K a Q 6 :=
    mem_of_two_mul_eq htwo htwoh2 rfl
  have ha7_6 : a 7 ∈ V K a Q 6 := lower (by omega) ha7
  have htwoa6 : 2 * a 6 ∈ V K a Q 6 := by
    have hkey : 2 * a 6 = h2 a - a 7 * a 7 + 1 := by
      rw [h2]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _
      (Subalgebra.sub_mem _ hh2 (Subalgebra.mul_mem _ ha7_6 ha7_6))
      (Subalgebra.one_mem _)
  have ha6 : a 6 ∈ V K a Q 6 :=
    mem_of_two_mul_eq htwo htwoa6 rfl
  have hh3_5 : h3 a ∈ V K a Q 5 := lower (by omega) hh3
  have hh2_5 : h2 a ∈ V K a Q 5 := lower (by omega) hh2
  have hprod32 : h3 a * h2 a ∈ V K a Q 5 := Subalgebra.mul_mem _ hh3_5 hh2_5
  have htwoh1 : 2 * h1 a ∈ V K a Q 5 := by
    have hkey : 2 * h1 a = (E a).coeff 5 -
        (h3 a * h2 a + h3 a * h2 a) + 1 := by
      rw [E_coeff_5]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _
      (Subalgebra.sub_mem _ (hEvis 5 (by omega))
        (Subalgebra.add_mem _ hprod32 hprod32))
      (Subalgebra.one_mem _)
  have hh1 : h1 a ∈ V K a Q 5 :=
    mem_of_two_mul_eq htwo htwoh1 rfl
  have ha7_5 : a 7 ∈ V K a Q 5 := lower (by omega) ha7
  have ha6_5 : a 6 ∈ V K a Q 5 := lower (by omega) ha6
  have hprod76 : a 7 * a 6 ∈ V K a Q 5 := Subalgebra.mul_mem _ ha7_5 ha6_5
  have htwoa5 : 2 * a 5 ∈ V K a Q 5 := by
    have hkey : 2 * a 5 = (a 7 * a 6 + a 7 * a 6) - h1 a := by
      rw [h1]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (Subalgebra.add_mem _ hprod76 hprod76) hh1
  have ha5 : a 5 ∈ V K a Q 5 :=
    mem_of_two_mul_eq htwo htwoa5 rfl
  have hh3_4 : h3 a ∈ V K a Q 4 := lower (by omega) hh3
  have hh2_4 : h2 a ∈ V K a Q 4 := lower (by omega) hh2
  have hh1_4 : h1 a ∈ V K a Q 4 := lower (by omega) hh1
  have ha7_4 : a 7 ∈ V K a Q 4 := lower (by omega) ha7
  have hp31 : h3 a * h1 a ∈ V K a Q 4 := Subalgebra.mul_mem _ hh3_4 hh1_4
  have htwoh0 : 2 * h0 a ∈ V K a Q 4 := by
    have hkey : 2 * h0 a = (E a).coeff 4 -
        (h3 a * h1 a + h3 a * h1 a) - h2 a * h2 a +
        (a 7 + a 7) + (1 + 1) := by
      rw [E_coeff_4]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _
      (Subalgebra.add_mem _
        (Subalgebra.sub_mem _
          (Subalgebra.sub_mem _ (hEvis 4 (by omega))
            (Subalgebra.add_mem _ hp31 hp31))
          (Subalgebra.mul_mem _ hh2_4 hh2_4))
        (Subalgebra.add_mem _ ha7_4 ha7_4))
      (Subalgebra.add_mem _ (Subalgebra.one_mem _) (Subalgebra.one_mem _))
  have hh0 : h0 a ∈ V K a Q 4 :=
    mem_of_two_mul_eq htwo htwoh0 rfl
  have ha6_4 : a 6 ∈ V K a Q 4 := lower (by omega) ha6
  have ha5_4 : a 5 ∈ V K a Q 4 := lower (by omega) ha5
  have ha4 : a 4 ∈ V K a Q 4 := by
    have hkey : a 4 = h0 a - a 6 * a 6 + a 5 * a 5 := by
      rw [h0]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _
      (Subalgebra.sub_mem _ hh0 (Subalgebra.mul_mem _ ha6_4 ha6_4))
      (Subalgebra.mul_mem _ ha5_4 ha5_4)
  -- Package the quartic coefficient schedule before entering the bottom rows.
  have hH4coeff : ∀ j, (H4 a).coeff j ∈ V K a Q (j + 4) := by
    intro j
    match j with
    | 0 =>
        rw [H4_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact hh0
    | 1 =>
        rw [H4_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact hh1
    | 2 =>
        rw [H4_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact hh2
    | 3 =>
        rw [H4_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact hh3
    | 4 =>
        rw [H4_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
    | m + 5 =>
        have hz : (H4 a).coeff (m + 5) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by have := H4_natDegree_le a; omega)
        rw [hz]
        exact Subalgebra.zero_mem _
  have hH4sq : ∀ j, (H4 a ^ 2).coeff j ∈ V K a Q j := by
    refine coeff_sq_mem_of_schedule (V K a Q) hanti (P := H4 a) (d := 4) (e := 0)
      (H4_natDegree_le a) ?_
    intro i
    simpa only [Nat.add_zero] using hH4coeff i
  have hLvis : ∀ i, i < 15 → (L a).coeff i ∈ V K a Q i := by
    intro i hi
    have hkey : (L a).coeff i = (E a).coeff i - (H4 a ^ 2).coeff i := by
      rw [L_eq_E_sub, coeff_sub]
    rw [hkey]
    exact Subalgebra.sub_mem _ (hEvis i hi) (hH4sq i)
  -- Bottom four rows: the two shifted quadratics and the final two scalars.
  have ha7_3 : a 7 ∈ V K a Q 3 := lower (by omega) ha7
  have htwod3 : 2 * d3 a ∈ V K a Q 3 := by
    have hkey : 2 * d3 a = -((L a).coeff 3 + a 7 * a 7 +
        (a 7 + a 7 + a 7 + a 7)) := by
      rw [L_coeff_3]
      ring
    rw [hkey]
    exact Subalgebra.neg_mem _
      (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (hLvis 3 (by omega))
          (Subalgebra.mul_mem _ ha7_3 ha7_3))
        (Subalgebra.add_mem _
          (Subalgebra.add_mem _ (Subalgebra.add_mem _ ha7_3 ha7_3) ha7_3) ha7_3))
  have hd3 : d3 a ∈ V K a Q 3 :=
    mem_of_two_mul_eq htwo htwod3 rfl
  have ha6_3 : a 6 ∈ V K a Q 3 := lower (by omega) ha6
  have ha3 : a 3 ∈ V K a Q 3 := by
    have hkey : a 3 = d3 a - a 6 := by rw [d3]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ hd3 ha6_3
  have ha7_2 : a 7 ∈ V K a Q 2 := lower (by omega) ha7
  have hd3_2 : d3 a ∈ V K a Q 2 := lower (by omega) hd3
  have hp7d3 : a 7 * d3 a ∈ V K a Q 2 := Subalgebra.mul_mem _ ha7_2 hd3_2
  have htwod2 : 2 * d2 a ∈ V K a Q 2 := by
    have hkey : 2 * d2 a = -((L a).coeff 2 +
        (a 7 * a 7 + a 7 * a 7) + (d3 a + d3 a) +
        (a 7 * d3 a + a 7 * d3 a)) := by
      rw [L_coeff_2]
      ring
    rw [hkey]
    exact Subalgebra.neg_mem _
      (Subalgebra.add_mem _
        (Subalgebra.add_mem _
          (Subalgebra.add_mem _ (hLvis 2 (by omega))
            (Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha7_2 ha7_2)
              (Subalgebra.mul_mem _ ha7_2 ha7_2)))
          (Subalgebra.add_mem _ hd3_2 hd3_2))
        (Subalgebra.add_mem _ hp7d3 hp7d3))
  have hd2 : d2 a ∈ V K a Q 2 :=
    mem_of_two_mul_eq htwo htwod2 rfl
  have ha6_2 : a 6 ∈ V K a Q 2 := lower (by omega) ha6
  have ha2 : a 2 ∈ V K a Q 2 := by
    have hkey : a 2 = d2 a - a 6 := by rw [d2]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ hd2 ha6_2
  have ha7_1 : a 7 ∈ V K a Q 1 := lower (by omega) ha7
  have hd3_1 : d3 a ∈ V K a Q 1 := lower (by omega) hd3
  have hd2_1 : d2 a ∈ V K a Q 1 := lower (by omega) hd2
  have ha1 : a 1 ∈ V K a Q 1 := by
    have hkey : a 1 = (L a).coeff 1 +
        (a 7 * d3 a + a 7 * d3 a) + d3 a * d3 a +
        (a 7 * d2 a + a 7 * d2 a) := by
      rw [L_coeff_1]
      ring
    rw [hkey]
    exact Subalgebra.add_mem _
      (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (hLvis 1 (by omega))
          (Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha7_1 hd3_1)
            (Subalgebra.mul_mem _ ha7_1 hd3_1)))
        (Subalgebra.mul_mem _ hd3_1 hd3_1))
      (Subalgebra.add_mem _ (Subalgebra.mul_mem _ ha7_1 hd2_1)
        (Subalgebra.mul_mem _ ha7_1 hd2_1))
  have ha1_0 : a 1 ∈ V K a Q 0 := lower (by omega) ha1
  have hd3_0 : d3 a ∈ V K a Q 0 := lower (by omega) hd3
  have hd2_0 : d2 a ∈ V K a Q 0 := lower (by omega) hd2
  have ha0 : a 0 ∈ V K a Q 0 := by
    have hkey : a 0 = (L a).coeff 0 + d3 a * d3 a + d2 a * d2 a - a 1 := by
      rw [L_coeff_0]
      ring
    rw [hkey]
    exact Subalgebra.sub_mem _
      (Subalgebra.add_mem _
        (Subalgebra.add_mem _ (hLvis 0 (by omega))
          (Subalgebra.mul_mem _ hd3_0 hd3_0))
        (Subalgebra.mul_mem _ hd2_0 hd2_0)) ha1_0
  have hH2coeff : ∀ j, (H2 a).coeff j ∈ V K a Q (j + 6) := by
    intro j
    match j with
    | 0 =>
        rw [H2_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact ha6
    | 1 =>
        rw [H2_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
        exact ha7
    | 2 =>
        rw [H2_eq]
        simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
        norm_num
    | m + 3 =>
        have hz : (H2 a).coeff (m + 3) = 0 :=
          coeff_eq_zero_of_natDegree_lt (by have := H2_natDegree_le a; omega)
        rw [hz]
        exact Subalgebra.zero_mem _
  refine
    { low := ?_
      qcoeff := hq
      h2coeff := hH2coeff
      h4coeff := hH4coeff }
  intro i hi
  match i with
  | 0 => exact ha0
  | 1 => exact ha1
  | 2 => exact ha2
  | 3 => exact ha3
  | 4 => exact ha4
  | 5 => exact ha5
  | 6 => exact ha6
  | 7 => exact ha7
  | m + 8 => omega

section structural

variable [Nontrivial A]

theorem H2_good (a : ℕ → A) : (H2 a).Monic ∧ (H2 a).natDegree = 2 := by
  have hm : ((X + C (a 7)) * X : A[X]).Monic := (monic_X_add_C (a 7)).mul monic_X
  have hd : ((X + C (a 7)) * X : A[X]).natDegree = 2 := by
    rw [(monic_X_add_C (a 7)).natDegree_mul monic_X, natDegree_X_add_C, natDegree_X]
  obtain ⟨hm', hd'⟩ := monic_add_low (e := C (a 6)) hm
    (Or.inr (by rw [natDegree_C, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

theorem U_good (a : ℕ → A) : (U a).Monic ∧ (U a).natDegree = 2 := by
  obtain ⟨hm, hd⟩ := H2_good a
  rw [U]
  obtain ⟨hm', hd'⟩ := monic_add_low (e := C (a 3)) hm
    (Or.inr (by rw [natDegree_C, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

theorem W_good (a : ℕ → A) : (W a).Monic ∧ (W a).natDegree = 2 := by
  obtain ⟨hm, hd⟩ := H2_good a
  rw [W]
  obtain ⟨hm', hd'⟩ := monic_add_low (e := C (a 2)) hm
    (Or.inr (by rw [natDegree_C, hd]; omega))
  exact ⟨hm', hd'.trans hd⟩

theorem H4_good (a : ℕ → A) : (H4 a).Monic ∧ (H4 a).natDegree = 4 := by
  obtain ⟨h2m, h2d⟩ := H2_good a
  have hlm : (X + C (a 5) : A[X]).Monic := monic_X_add_C (a 5)
  have hld : (X + C (a 5) : A[X]).natDegree = 1 := natDegree_X_add_C (a 5)
  obtain ⟨hpm, hpd⟩ := monic_add_low (P := H2 a) (e := X + C (a 5)) h2m
    (Or.inr (by rw [hld, h2d]; omega))
  have hminus : H2 a - (X + C (a 5)) = H2 a + -(X + C (a 5)) := by ring
  obtain ⟨hmm, hmd⟩ := monic_add_low (P := H2 a) (e := -(X + C (a 5))) h2m
    (Or.inr (by rw [natDegree_neg, hld, h2d]; omega))
  rw [← hminus] at hmm hmd
  have hprodm : ((H2 a + (X + C (a 5))) * (H2 a - (X + C (a 5)))).Monic :=
    hpm.mul hmm
  have hprodd : ((H2 a + (X + C (a 5))) *
      (H2 a - (X + C (a 5)))).natDegree = 4 := by
    rw [hpm.natDegree_mul hmm, hpd, hmd, h2d]
  rw [H4]
  obtain ⟨hm, hd⟩ := monic_add_low (e := C (a 4)) hprodm
    (Or.inr (by rw [natDegree_C, hprodd]; omega))
  exact ⟨hm, hd.trans hprodd⟩

theorem T1_good (a : ℕ → A) (Q : A[X]) (hQm : Q.Monic) (hQd : Q.natDegree = 7) :
    (T1 a Q).Monic ∧ (T1 a Q).natDegree = 14 := by
  have hqm : (Q ^ 2).Monic := hQm.pow 2
  have hqd : (Q ^ 2).natDegree = 14 := by rw [hQm.natDegree_pow, hQd]
  have hud : (U a ^ 2).natDegree = 4 := by
    obtain ⟨hum, hud⟩ := U_good a
    rw [hum.natDegree_pow, hud]
  have he : (-U a ^ 2 + C (a 1)).natDegree < 14 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · rw [natDegree_neg, hud]
      norm_num
    · rw [natDegree_C]
      norm_num
  have hform : T1 a Q = Q ^ 2 + (-U a ^ 2 + C (a 1)) := by
    rw [T1]
    ring
  rw [hform]
  have he' : (-U a ^ 2 + C (a 1)).natDegree < (Q ^ 2).natDegree := by
    rw [hqd]
    exact he
  obtain ⟨hm, hd⟩ := monic_add_low hqm (Or.inr he')
  exact ⟨hm, hd.trans hqd⟩

theorem T2_good (a : ℕ → A) (Q : A[X]) (hQm : Q.Monic) (hQd : Q.natDegree = 7) :
    (T2 a Q).Monic ∧ (T2 a Q).natDegree = 14 := by
  obtain ⟨htm, htd⟩ := T1_good a Q hQm hQd
  obtain ⟨h4m, h4d⟩ := H4_good a
  obtain ⟨hwm, hwd⟩ := W_good a
  have h4sq : (H4 a ^ 2).natDegree = 8 := by rw [h4m.natDegree_pow, h4d]
  have hwsq : (W a ^ 2).natDegree = 4 := by rw [hwm.natDegree_pow, hwd]
  have he : (H4 a ^ 2 - W a ^ 2 + C (a 0)).natDegree < 14 := by
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (natDegree_sub_le _ _) (max_lt (by omega) (by omega))
    · rw [natDegree_C]
      norm_num
  have hform : T2 a Q = T1 a Q + (H4 a ^ 2 - W a ^ 2 + C (a 0)) := by
    rw [T2]
    ring
  rw [hform]
  have he' : (H4 a ^ 2 - W a ^ 2 + C (a 0)).natDegree < (T1 a Q).natDegree := by
    rw [htd]
    exact he
  obtain ⟨hm, hd⟩ := monic_add_low htm (Or.inr he')
  exact ⟨hm, hd.trans htd⟩

end structural

namespace OuterCert

/-- The schedules returned by `outer_recover` imply the two exact causal cutoffs. -/
theorem causal {K : Subalgebra R A} {a : ℕ → A} {Q : A[X]}
    (h : OuterCert K a Q) (hQd : Q.natDegree = 7) :
    CausalPair K (T1 a Q) (T2 a Q) (range 15) := by
  have hanti := V_antitone K a Q
  have lower : ∀ {x : A} {s t : ℕ}, t ≤ s → x ∈ V K a Q s → x ∈ V K a Q t := by
    intro x s t hst hx
    exact hanti hst hx
  have hQsq : ∀ j, (Q ^ 2).coeff j ∈ V K a Q (j + 1) := by
    refine coeff_sq_mem_of_schedule (V K a Q) hanti (P := Q) (d := 7) (e := 1)
      (le_of_eq hQd) ?_
    intro i
    simpa only [show i + 7 + 1 = i + 8 by omega] using h.qcoeff i
  have hUcoeff : ∀ i, (U a).coeff i ∈ V K a Q (i + 3) := by
    intro i
    rw [U, coeff_add, coeff_C]
    have hbase := lower (show i + 3 ≤ i + 6 by omega) (h.h2coeff i)
    split
    · subst i
      exact Subalgebra.add_mem _ hbase (h.low 3 (by omega))
    · exact Subalgebra.add_mem _ hbase (Subalgebra.zero_mem _)
  have hUsq : ∀ j, (U a ^ 2).coeff j ∈ V K a Q (j + 1) :=
    coeff_sq_mem_of_schedule (V K a Q) hanti (P := U a) (d := 2) (e := 1)
      (U_natDegree_le a) hUcoeff
  have hH4sq : ∀ j, (H4 a ^ 2).coeff j ∈ V K a Q j := by
    refine coeff_sq_mem_of_schedule (V K a Q) hanti (P := H4 a) (d := 4) (e := 0)
      (H4_natDegree_le a) ?_
    intro i
    simpa only [Nat.add_zero] using h.h4coeff i
  have hWcoeff : ∀ i, (W a).coeff i ∈ V K a Q (i + 2) := by
    intro i
    rw [W, coeff_add, coeff_C]
    have hbase := lower (show i + 2 ≤ i + 6 by omega) (h.h2coeff i)
    split
    · subst i
      exact Subalgebra.add_mem _ hbase (h.low 2 (by omega))
    · exact Subalgebra.add_mem _ hbase (Subalgebra.zero_mem _)
  have hWsq : ∀ j, (W a ^ 2).coeff j ∈ V K a Q j := by
    refine coeff_sq_mem_of_schedule (V K a Q) hanti (P := W a) (d := 2) (e := 0)
      (W_natDegree_le a) ?_
    intro i
    simpa only [Nat.add_zero] using hWcoeff i
  have ht1 : ∀ j, (T1 a Q).coeff j ∈ V K a Q (j + 1) := by
    intro j
    rw [T1, coeff_add, coeff_sub, coeff_C]
    have hmain := Subalgebra.sub_mem _ (hQsq j) (hUsq j)
    split
    · subst j
      exact Subalgebra.add_mem _ hmain (h.low 1 (by omega))
    · exact Subalgebra.add_mem _ hmain (Subalgebra.zero_mem _)
  have ht2 : ∀ j, (T2 a Q).coeff j ∈ V K a Q j := by
    intro j
    rw [T2, coeff_add, coeff_sub, coeff_add, coeff_C]
    have hmain := Subalgebra.sub_mem _
      (Subalgebra.add_mem _ (lower (by omega) (ht1 j)) (hH4sq j)) (hWsq j)
    split
    · subst j
      exact Subalgebra.add_mem _ hmain (h.low 0 (by omega))
    · exact Subalgebra.add_mem _ hmain (Subalgebra.zero_mem _)
  exact ⟨ht1, ht2⟩

end OuterCert

/-- The generic opaque-septic shell is a compatible pair. -/
theorem shell_compatible [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A) (Q : A[X])
    (htwo : IsUnit (2 : R)) (hQm : Q.Monic) (hQd : Q.natDegree = 7) :
    CompatiblePair K (T1 a Q) (T2 a Q) 14 (range 15) := by
  obtain ⟨ht1m, ht1d⟩ := T1_good a Q hQm hQd
  obtain ⟨ht2m, ht2d⟩ := T2_good a Q hQm hQd
  exact
    { toCausalPair := (outer_recover K a Q htwo hQm hQd).causal hQd
      monic₁ := ht1m
      monic₂ := ht2m
      natDegree₁ := ht1d
      natDegree₂ := ht2d
      window := by intro i hi; simpa only using hi }

/-! ## Specialization to the paper's `Q₇` block -/

noncomputable def Hp (a : ℕ → A) : ℕ → A[X]
  | 1 => H2 a
  | 2 => H4 a
  | _ => 0

noncomputable def Q7 (a : ℕ → A) : A[X] :=
  peel (Hp a) 3 (fun t => a (8 + t))

theorem Hp_good [Nontrivial A] (a : ℕ → A) :
    ∀ i, 1 ≤ i → i < 3 → (Hp a i).Monic ∧ (Hp a i).natDegree = 2 ^ i := by
  intro i hi1 hi3
  match i with
  | 0 => omega
  | 1 =>
      simpa only [Hp, pow_one] using H2_good a
  | 2 =>
      simpa only [Hp] using H4_good a
  | i + 3 => omega

theorem Q7_good [Nontrivial A] (a : ℕ → A) :
    (Q7 a).Monic ∧ (Q7 a).natDegree = 7 := by
  have h := peel_monic (Hp a) 3 (Hp_good a) (by omega) (fun t => a (8 + t))
  simpa only [Q7] using h

/-- The actual degree-15 special construction is compatible. -/
theorem compatible [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A)
    (htwo : IsUnit (2 : R)) :
    CompatiblePair K (T1 a (Q7 a)) (T2 a (Q7 a)) 14 (range 15) := by
  obtain ⟨hqm, hqd⟩ := Q7_good a
  exact shell_compatible K a (Q7 a) htwo hqm hqd

/-- Context generated by the two recovered powers used by `Q₇`. -/
noncomputable def powerContext (K : Subalgebra R A) (a : ℕ → A) : Subalgebra R A :=
  K ⊔ adjoin R (Set.range (fun j => (H2 a).coeff j) ∪
    Set.range (fun j => (H4 a).coeff j))

theorem H2_coeff_mem_powerContext (K : Subalgebra R A) (a : ℕ → A) (j : ℕ) :
    (H2 a).coeff j ∈ powerContext K a := by
  rw [powerContext]
  exact (le_sup_right : adjoin R (Set.range (fun j => (H2 a).coeff j) ∪
      Set.range (fun j => (H4 a).coeff j)) ≤ _)
    (subset_adjoin (Set.mem_union_left _ ⟨j, rfl⟩))

theorem H4_coeff_mem_powerContext (K : Subalgebra R A) (a : ℕ → A) (j : ℕ) :
    (H4 a).coeff j ∈ powerContext K a := by
  rw [powerContext]
  exact (le_sup_right : adjoin R (Set.range (fun j => (H2 a).coeff j) ∪
      Set.range (fun j => (H4 a).coeff j)) ≤ _)
    (subset_adjoin (Set.mem_union_right _ ⟨j, rfl⟩))

/-- Full parameter decoder for the degree-15 construction.  The proof first runs the
unconditional outer decoder, then invokes `peel_correct` relative to the generated power
context and discharges that context using the recovered `H₂,H₄` schedules. -/
theorem decodable [Nontrivial A] (K : Subalgebra R A) (a : ℕ → A)
    (htwo : IsUnit (2 : R)) :
    ∀ i, i < 15 → a i ∈ V K a (Q7 a) 0 := by
  obtain ⟨hqm, hqd⟩ := Q7_good a
  let cert := outer_recover K a (Q7 a) htwo hqm hqd
  have hanti := V_antitone K a (Q7 a)
  have hctx : powerContext K a ≤ V K a (Q7 a) 0 := by
    rw [powerContext]
    refine sup_le known_le_Vis (adjoin_le ?_)
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨j, rfl⟩ := hx
      exact hanti (Nat.zero_le _) (cert.h2coeff j)
    · obtain ⟨j, rfl⟩ := hx
      exact hanti (Nat.zero_le _) (cert.h4coeff j)
  have hpKnown : ∀ i, 1 ≤ i → i < 3 →
      (Hp a i).Monic ∧ (Hp a i).natDegree = 2 ^ i ∧
        ∀ j, (Hp a i).coeff j ∈ powerContext K a := by
    intro i hi1 hi3
    match i with
    | 0 => omega
    | 1 =>
        obtain ⟨hm, hd⟩ := H2_good a
        exact ⟨hm, hd.trans (by norm_num), H2_coeff_mem_powerContext K a⟩
    | 2 =>
        obtain ⟨hm, hd⟩ := H4_good a
        exact ⟨hm, hd.trans (by norm_num), H4_coeff_mem_powerContext K a⟩
    | i + 3 => omega
  have hQcoeff : ∀ j, (Q7 a).coeff j ∈ V K a (Q7 a) 0 :=
    fun j => hanti (Nat.zero_le _) (cert.qcoeff j)
  intro i hi
  by_cases hilow : i < 8
  · exact hanti (Nat.zero_le _) (cert.low i hilow)
  · have ht : i - 8 < 2 ^ 3 - 1 := by norm_num; omega
    have hdec := peel_correct (K := powerContext K a) (Hp a) 3 hpKnown (by omega)
      (fun t => a (8 + t)) (V K a (Q7 a) 0) hctx
      (by intro j; simpa only [Q7] using hQcoeff j) (i - 8) ht
    simpa only [show 8 + (i - 8) = i by omega] using hdec

end FastPoly.P15
