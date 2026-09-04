import FastPoly.Section4.FillRec
import FastPoly.Examples.Q3

/-!
# The known-powers (Mersenne) construction `Q_{2^k - 1}`

Definitional layer for `alg:constr-known-2n-1`, instantiating the fill chain with concrete
per-level data whose head and additive parts are smaller Mersenne instances.  The recursion
is fuel-indexed (with a fuel-irrelevance lemma) to avoid well-founded recursion plumbing.

Parameter layout for `k ≥ 4` (our own; decodability does not depend on matching the paper's
α-numbering): slots `0..4` = head `(β₀, β₁, β₂, a₀, a₁)`; slot `5` = the scalar shift of the
second input branch; `6..6+2^{k-2}-2` = the `Q_{2^{k-2}-1}` block of the first input branch;
level `i` (`2 ≤ i ≤ k-2`) occupies slots starting at `doff k i`: `b, ah`, the `q`-block
(`2^{i-1}-1` slots), the `qh`-block (`2^i - 1` slots).
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Start of the level-`i` parameter block inside `Q_{2^k-1}`. -/
def doff (k i : ℕ) : ℕ := 5 + 2 ^ (k - 2) + 3 * (2 ^ (i - 1) - 2)

/-- The per-level data of the Mersenne fill at fuel `g`. -/
noncomputable def mersD (_Hp : ℕ → A[X])
    (rec : ℕ → (ℕ → A) → A[X]) (k : ℕ) (α : ℕ → A) (i : ℕ) : FillData A :=
  { q := rec (i - 1) (fun j => α (doff k i + 2 + j))
    qh := rec i (fun j => α (doff k i + 2 + (2 ^ (i - 1) - 1) + j))
    b := α (doff k i)
    ah := α (doff k i + 1) }

/-- Fuel-indexed Mersenne construction. -/
noncomputable def mersF (Hp : ℕ → A[X]) : ℕ → ℕ → (ℕ → A) → A[X]
  | 0, _, α => X + C (α 0)
  | f + 1, k, α =>
    match k with
    | 0 => X + C (α 0)
    | 1 => X + C (α 0)
    | 2 => (X + C (α 2)) * (Hp 1 + C (α 1)) + C (α 0)
    | 3 =>
      (X + C (α 0)) * ((Hp 1 + C (α 1)) * (Hp 2 + C (α 5)) + C (α 4))
        + ((Hp 1 + C (α 2)) * (Hp 2 + C (α 6)) + C (α 3))
    | (kk + 4) =>
      let SP : A[X] × A[X] :=
        (Hp (kk + 3) + mersF Hp f (kk + 2) (fun j => α (6 + j)),
         Hp (kk + 3) + C (α 5))
      let D := mersD Hp (mersF Hp f) (kk + 4) α
      (X + C (α 0)) * ((Hp 1 + C (α 1)) * (fillChain Hp D (kk + 2) SP).1 + C (α 4))
        + ((Hp 1 + C (α 2)) * (fillChain Hp D (kk + 2) SP).2 + C (α 3))

/-- The Mersenne polynomial `Q_{2^k-1}` over the known powers `Hp` (with `Hp i` playing
`H_{2^i}`) and parameters `α`. -/
noncomputable def mers (Hp : ℕ → A[X]) (k : ℕ) (α : ℕ → A) : A[X] := mersF Hp k k α

/-- Fuel irrelevance: any fuel at least `k` computes the same polynomial. -/
theorem mersF_fuel (Hp : ℕ → A[X]) :
    ∀ k, ∀ f f', k ≤ f → k ≤ f' → ∀ α : ℕ → A, mersF Hp f k α = mersF Hp f' k α := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' hf hf' α
    match k, f, f' with
    | 0, 0, 0 => rfl
    | 0, 0, _ + 1 => rfl
    | 0, _ + 1, 0 => rfl
    | 0, _ + 1, _ + 1 => rfl
    | k + 1, f + 1, f' + 1 =>
      match k with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
      | (kk + 3) =>
        show mersF Hp (f + 1) (kk + 4) α = mersF Hp (f' + 1) (kk + 4) α
        have hbody : ∀ g : ℕ,
            mersF Hp (g + 1) (kk + 4) α
            = (X + C (α 0)) * ((Hp 1 + C (α 1)) *
                (fillChain Hp (mersD Hp (mersF Hp g) (kk + 4) α) (kk + 2)
                  (Hp (kk + 3) + mersF Hp g (kk + 2) (fun j => α (6 + j)),
                   Hp (kk + 3) + C (α 5))).1 + C (α 4))
              + ((Hp 1 + C (α 2)) *
                (fillChain Hp (mersD Hp (mersF Hp g) (kk + 4) α) (kk + 2)
                  (Hp (kk + 3) + mersF Hp g (kk + 2) (fun j => α (6 + j)),
                   Hp (kk + 3) + C (α 5))).2 + C (α 3)) := fun g => rfl
        rw [hbody f, hbody f']
        have hSP : mersF Hp f (kk + 2) (fun j => α (6 + j))
            = mersF Hp f' (kk + 2) (fun j => α (6 + j)) :=
          ih (kk + 2) (by omega) f f' (by omega) (by omega) _
        have hchain : fillChain Hp (mersD Hp (mersF Hp f) (kk + 4) α) (kk + 2)
              (Hp (kk + 3) + mersF Hp f (kk + 2) (fun j => α (6 + j)),
               Hp (kk + 3) + C (α 5))
            = fillChain Hp (mersD Hp (mersF Hp f') (kk + 4) α) (kk + 2)
              (Hp (kk + 3) + mersF Hp f' (kk + 2) (fun j => α (6 + j)),
               Hp (kk + 3) + C (α 5)) := by
          rw [hSP]
          exact fillChain_congr Hp (kk + 2) _ (fun i h2 hi => by
            show mersD Hp (mersF Hp f) (kk + 4) α i = mersD Hp (mersF Hp f') (kk + 4) α i
            unfold mersD
            rw [ih (i - 1) (by omega) f f' (by omega) (by omega),
              ih i (by omega) f f' (by omega) (by omega)])
        rw [hchain]


/-- Unfolding `mers` at `k = kk + 4`, with the recursive occurrences expressed through
`mers` itself (via fuel irrelevance). -/
theorem mers_unfold (Hp : ℕ → A[X]) (kk : ℕ) (α : ℕ → A) :
    mers Hp (kk + 4) α
      = (X + C (α 0)) * ((Hp 1 + C (α 1)) *
          (fillChain Hp (mersD Hp (mers Hp) (kk + 4) α) (kk + 2)
            (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)),
             Hp (kk + 3) + C (α 5))).1 + C (α 4))
        + ((Hp 1 + C (α 2)) *
          (fillChain Hp (mersD Hp (mers Hp) (kk + 4) α) (kk + 2)
            (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)),
             Hp (kk + 3) + C (α 5))).2 + C (α 3)) := by
  have hbody :
      mers Hp (kk + 4) α
      = (X + C (α 0)) * ((Hp 1 + C (α 1)) *
          (fillChain Hp (mersD Hp (mersF Hp (kk + 3)) (kk + 4) α) (kk + 2)
            (Hp (kk + 3) + mersF Hp (kk + 3) (kk + 2) (fun j => α (6 + j)),
             Hp (kk + 3) + C (α 5))).1 + C (α 4))
        + ((Hp 1 + C (α 2)) *
          (fillChain Hp (mersD Hp (mersF Hp (kk + 3)) (kk + 4) α) (kk + 2)
            (Hp (kk + 3) + mersF Hp (kk + 3) (kk + 2) (fun j => α (6 + j)),
             Hp (kk + 3) + C (α 5))).2 + C (α 3)) := rfl
  rw [hbody]
  have hSP : mersF Hp (kk + 3) (kk + 2) (fun j => α (6 + j))
      = mers Hp (kk + 2) (fun j => α (6 + j)) :=
    mersF_fuel Hp (kk + 2) (kk + 3) (kk + 2) (by omega) (by omega) _
  rw [hSP]
  have hD : fillChain Hp (mersD Hp (mersF Hp (kk + 3)) (kk + 4) α) (kk + 2)
        (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)), Hp (kk + 3) + C (α 5))
      = fillChain Hp (mersD Hp (mers Hp) (kk + 4) α) (kk + 2)
        (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)), Hp (kk + 3) + C (α 5)) :=
    fillChain_congr Hp (kk + 2) _ (fun i h2 hi => by
      show mersD Hp (mersF Hp (kk + 3)) (kk + 4) α i = mersD Hp (mers Hp) (kk + 4) α i
      unfold mersD
      rw [mersF_fuel Hp (i - 1) (kk + 3) (i - 1) (by omega) (by omega),
        mersF_fuel Hp i (kk + 3) i (by omega) (by omega)]
      rfl)
  rw [hD]

/-- **Monicity and degree of the Mersenne construction**: `Q_{2^k-1}` is monic of degree
`2^k - 1`, for every `k ≥ 1` and every parameter assignment. -/
theorem mers_monic [Nontrivial A] (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i) →
      1 ≤ k → ∀ α : ℕ → A,
      (mers Hp k α).Monic ∧ (mers Hp k α).natDegree = 2 ^ k - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α
    match k with
    | 0 => omega
    | 1 =>
      exact ⟨monic_X_add_C (α 0), (natDegree_X_add_C (α 0)).trans (by norm_num)⟩
    | 2 =>
      obtain ⟨h1m, h1d⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨hbm, hbd⟩ := monic_add_low (e := C (α 1)) h1m (Or.inr (by
        rw [natDegree_C, h1d]; norm_num))
      have hXm : (X + C (α 2) : A[X]).Monic := monic_X_add_C (α 2)
      have hmul : ((X + C (α 2)) * (Hp 1 + C (α 1))).Monic := hXm.mul hbm
      have hmuld : ((X + C (α 2)) * (Hp 1 + C (α 1))).natDegree = 3 := by
        rw [hXm.natDegree_mul hbm, natDegree_X_add_C, hbd, h1d]
        norm_num
      obtain ⟨hm, hd⟩ := monic_add_low (e := C (α 0)) hmul (Or.inr (by
        rw [natDegree_C, hmuld]; norm_num))
      exact ⟨hm, (hd.trans hmuld).trans (by norm_num)⟩
    | 3 =>
      obtain ⟨h1m, h1d⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨h2m, h2d⟩ := hHp 2 (by omega) (by omega)
      obtain ⟨hs₁m, hs₁d⟩ := monic_add_low (e := C (α 5)) h2m (Or.inr (by
        rw [natDegree_C, h2d]; norm_num))
      obtain ⟨hs₂m, hs₂d⟩ := monic_add_low (e := C (α 6)) h2m (Or.inr (by
        rw [natDegree_C, h2d]; norm_num))
      obtain ⟨hm, hd⟩ := fill_output_monic (m := 4) (β₀ := α 0) (β₁ := α 1) (β₂ := α 2)
        (α₀ := α 3) (α₁ := α 4) h1m (h1d.trans (by norm_num)) hs₁m
        ((hs₁d.trans h2d).trans (by norm_num)) hs₂m ((hs₂d.trans h2d).trans (by norm_num))
      exact ⟨hm, hd.trans (by norm_num)⟩
    | kk + 4 =>
      show (mers Hp (kk + 4) α).Monic ∧ (mers Hp (kk + 4) α).natDegree = 2 ^ (kk + 4) - 1
      rw [mers_unfold]
      obtain ⟨h1m, h1d⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨h3m, h3d⟩ := hHp (kk + 3) (by omega) (by omega)
      obtain ⟨-, hqd⟩ := ih (kk + 2) (by omega)
        (fun i' h1 hik => hHp i' h1 (by omega)) (by omega) (fun j => α (6 + j))
      obtain ⟨hSP₁m, hSP₁d⟩ := monic_add_low
        (e := mers Hp (kk + 2) (fun j => α (6 + j))) h3m (Or.inr (by
          rw [hqd, h3d]
          have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
          have hle : (2:ℕ) ^ (kk + 2) ≤ 2 ^ (kk + 3) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega))
      obtain ⟨hSP₂m, hSP₂d⟩ := monic_add_low (e := C (α 5)) h3m (Or.inr (by
        rw [natDegree_C, h3d]
        exact Nat.one_le_pow _ _ (by omega)))
      rw [h3d] at hSP₁d hSP₂d
      have hlev : ∀ i, 2 ≤ i → i ≤ kk + 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
          (mersD Hp (mers Hp) (kk + 4) α i).q.natDegree < 2 ^ i ∧
          (mersD Hp (mers Hp) (kk + 4) α i).qh.natDegree < 2 ^ i := by
        intro i h2 hi
        obtain ⟨him, hid⟩ := hHp i (by omega) (by omega)
        obtain ⟨-, hqd'⟩ := ih (i - 1) (by omega)
          (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
          (fun j => α (doff (kk + 4) i + 2 + j))
        obtain ⟨-, hqhd'⟩ := ih i (by omega)
          (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
          (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))
        refine ⟨him, hid, ?_, ?_⟩
        · show (mers Hp (i - 1) (fun j => α (doff (kk + 4) i + 2 + j))).natDegree < 2 ^ i
          rw [hqd']
          have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
          have hle : (2:ℕ) ^ (i - 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
          omega
        · show (mers Hp i
              (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))).natDegree < 2 ^ i
          rw [hqhd']
          have h1p : (1:ℕ) ≤ 2 ^ i := Nat.one_le_pow _ _ (by omega)
          omega
      obtain ⟨⟨hc₁m, hc₁d⟩, ⟨hc₂m, hc₂d⟩⟩ := fillChain_monic (kk + 2)
        (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)), Hp (kk + 3) + C (α 5))
        (2 ^ (kk + 3)) hSP₁m hSP₁d hSP₂m hSP₂d hlev
      obtain ⟨hPm, hPd⟩ := fill_output_monic (β₀ := α 0) (β₁ := α 1) (β₂ := α 2)
        (α₀ := α 3) (α₁ := α 4) h1m (h1d.trans (by norm_num)) hc₁m hc₁d hc₂m hc₂d
      have harith : 2 ^ (kk + 3) + (2 ^ (kk + 2 + 1) - 4) + 3 = 2 ^ (kk + 4) - 1 := by
        have h4 : (4:ℕ) ≤ 2 ^ (kk + 3) := by
          calc (4:ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (kk + 3) := Nat.pow_le_pow_right (by omega) (by omega)
        have h5 : (2:ℕ) ^ (kk + 2 + 1) = 2 ^ (kk + 3) := by ring
        have h6 : (2:ℕ) ^ (kk + 4) = 2 ^ (kk + 3) + 2 ^ (kk + 3) := by ring
        omega
      exact ⟨hPm, hPd.trans harith⟩

/-- Dyadic interval location: every `2 ≤ v < 2^m` lies in `[2^i, 2^{i+1})` for a unique
`1 ≤ i < m` (we only need existence). -/
theorem exists_pow_interval : ∀ m v : ℕ, 2 ≤ v → v < 2 ^ m →
    ∃ i, 1 ≤ i ∧ i + 1 ≤ m ∧ 2 ^ i ≤ v ∧ v < 2 ^ (i + 1) := by
  intro m
  induction m with
  | zero =>
    intro v h2 hv
    have h0 : (2:ℕ) ^ 0 = 1 := by norm_num
    omega
  | succ m ih =>
    intro v h2 hv
    rcases Nat.lt_or_ge v (2 ^ m) with hlt | hge
    · obtain ⟨i, h1, hm, hle, hlt2⟩ := ih v h2 hlt
      exact ⟨i, h1, by omega, hle, hlt2⟩
    · refine ⟨m, ?_, by omega, hge, hv⟩
      rcases Nat.lt_or_ge m 1 with h0 | h1
      · have hm0 : m = 0 := by omega
        subst hm0
        have h2p : (2:ℕ) ^ (0 + 1) = 2 := by norm_num
        omega
      · exact h1

/-- Peeling a known summand: if all coefficients of `H + Q` and of `H` lie in `V`, so do
those of `Q` (each is the explicit difference). -/
theorem add_known_coeff_mem {V : Subalgebra R A} {H Q : A[X]}
    (h : ∀ j, (H + Q).coeff j ∈ V) (hH : ∀ j, H.coeff j ∈ V) : ∀ j, Q.coeff j ∈ V := by
  intro j
  have hkey : Q.coeff j = (H + Q).coeff j - H.coeff j := by
    rw [coeff_add]; ring
  rw [hkey]
  exact Subalgebra.sub_mem _ (h j) (hH j)

/-- Transport out of the canonical output algebra `K ⊔ adjoin R {coeffs of P}`. -/
theorem sup_adjoin_range_le {K V : Subalgebra R A} {P : A[X]} (hKV : K ≤ V)
    (hV : ∀ j, P.coeff j ∈ V) :
    K ⊔ adjoin R (Set.range fun i => P.coeff i) ≤ V :=
  sup_le hKV (Algebra.adjoin_le (Set.range_subset_iff.mpr hV))

/-- **Decodability of the Mersenne construction** (paper `lem:fill-correctness`,
"in particular" clause, for `Q_{2^k-1}`): over known powers `Hp i = H_{2^i}` (monic, right
degree, coefficients in `K`), every parameter `α t`, `t < 2^k - 1`, of `Q_{2^k-1}` lies in
any subalgebra `V ⊇ K` containing the coefficients of `Q_{2^k-1}`.  The statement is
`V`-relative so that instances at different offsets compose in the induction. -/
theorem mers_correct [Nontrivial A] {K : Subalgebra R A} (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k →
        (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧ ∀ j, (Hp i).coeff j ∈ K) →
      1 ≤ k → ∀ α : ℕ → A, ∀ V : Subalgebra R A, K ≤ V →
      (∀ j, (mers Hp k α).coeff j ∈ V) → ∀ t, t < 2 ^ k - 1 → α t ∈ V := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α V hKV hV
    match k with
    | 0 => exact absurd hk (by omega)
    | 1 =>
      intro t ht
      have h1 : (2:ℕ) ^ 1 - 1 = 1 := by norm_num
      have ht0 : t = 0 := by omega
      subst ht0
      have hkey : α 0 = (mers Hp 1 α).coeff 0 := by
        show α 0 = (X + C (α 0) : A[X]).coeff 0
        rw [coeff_add, coeff_X_zero, coeff_C_zero, zero_add]
      rw [hkey]
      exact hV 0
    | 2 =>
      obtain ⟨h1m, h1d2, h1K⟩ := hHp 1 (by omega) (by omega)
      have h1d : (Hp 1).natDegree = 2 := h1d2.trans (by norm_num)
      have hQ : ∀ j, (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff j ∈ V := fun j => hV j
      have hα2 : α 2 ∈ V := by
        have hkey : α 2 = (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff 2 - (Hp 1).coeff 1 := by
          rw [Q₃_coeff_two (α 0) (α 1) (α 2) h1m h1d]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hQ 2) (hKV (h1K 1))
      have hα1 : α 1 ∈ V := by
        have hkey : α 1 = (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff 1
            - ((Hp 1).coeff 0 + α 2 * (Hp 1).coeff 1) := by
          rw [Q₃_coeff_one (α 0) (α 1) (α 2)]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hQ 1) (Subalgebra.add_mem _ (hKV (h1K 0))
          (Subalgebra.mul_mem _ hα2 (hKV (h1K 1))))
      have hα0 : α 0 ∈ V := by
        have hkey : α 0 = (Q₃ (Hp 1) (α 0) (α 1) (α 2)).coeff 0
            - α 2 * ((Hp 1).coeff 0 + α 1) := by
          rw [Q₃_coeff_zero (α 0) (α 1) (α 2)]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ (hQ 0) (Subalgebra.mul_mem _ hα2
          (Subalgebra.add_mem _ (hKV (h1K 0)) hα1))
      intro t ht
      have h3 : (2:ℕ) ^ 2 - 1 = 3 := by norm_num
      match t with
      | 0 => exact hα0
      | 1 => exact hα1
      | 2 => exact hα2
      | (s + 3) => omega
    | 3 =>
      obtain ⟨h1m, h1d2, h1K⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨h2m, h2d4, h2K⟩ := hHp 2 (by omega) (by omega)
      have hpair := compatiblePair_shifts (h := 4) h2m (h2d4.trans (by norm_num))
        (by omega) h2K (α 5) (α 6)
      obtain ⟨hβ₀, hβ₁, hβ₂, hα₀', hα₁', hC₁, hC₂⟩ := fill_two_mem K
        (β₀ := α 0) (β₁ := α 1) (β₂ := α 2) (α₀ := α 3) (α₁ := α 4)
        (P := mers Hp 3 α) hpair
        (by intro i hi
            rcases Finset.mem_insert.1 hi with rfl | hi
            · omega
            · rw [Finset.mem_singleton.1 hi]; omega)
        (by omega) h1m (h1d2.trans (by norm_num)) h1K rfl rfl rfl
      have hle : K ⊔ adjoin R (Set.range fun i => (mers Hp 3 α).coeff i) ≤ V :=
        sup_adjoin_range_le hKV hV
      have hα5 : α 5 ∈ V := by
        have hc0 : (Hp 2 + C (α 5)).coeff 0 ∈ V := hle (hC₁ 0)
        have hkey : α 5 = (Hp 2 + C (α 5)).coeff 0 - (Hp 2).coeff 0 := by
          rw [coeff_add, coeff_C_zero]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ hc0 (hKV (h2K 0))
      have hα6 : α 6 ∈ V := by
        have hc0 : (Hp 2 + C (α 6)).coeff 0 ∈ V := hle (hC₂ 0)
        have hkey : α 6 = (Hp 2 + C (α 6)).coeff 0 - (Hp 2).coeff 0 := by
          rw [coeff_add, coeff_C_zero]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ hc0 (hKV (h2K 0))
      intro t ht
      have h7 : (2:ℕ) ^ 3 - 1 = 7 := by norm_num
      match t with
      | 0 => exact hle hβ₀
      | 1 => exact hle hβ₁
      | 2 => exact hle hβ₂
      | 3 => exact hle hα₀'
      | 4 => exact hle hα₁'
      | 5 => exact hα5
      | 6 => exact hα6
      | (s + 7) => omega
    | kk + 4 =>
      obtain ⟨h1m, h1d2, h1K⟩ := hHp 1 (by omega) (by omega)
      obtain ⟨h3m, h3d, h3K⟩ := hHp (kk + 3) (by omega) (by omega)
      obtain ⟨hQm, hQd⟩ := mers_monic Hp (kk + 2)
        (fun i' h1 hik => ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
        (by omega) (fun j => α (6 + j))
      have hSpair := compatiblePair_aux_add_left h3m h3d h3K hQm hQd (by
        have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
        have hle2 : (2:ℕ) ^ (kk + 2) ≤ 2 ^ (kk + 3) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega) (α 5)
      have hgood : ∀ i, 2 ≤ i → i ≤ kk + 2 →
          GoodLevel K (Hp i) (mersD Hp (mers Hp) (kk + 4) α i) i
            (Finset.range (2 ^ (i - 1) - 1 + 1)) := by
        intro i h2i hi
        obtain ⟨him, hid, hiK⟩ := hHp i (by omega) (by omega)
        obtain ⟨hqm, hqd⟩ := mers_monic Hp (i - 1)
          (fun i' h1 hik => ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
          (by omega) (fun j => α (doff (kk + 4) i + 2 + j))
        obtain ⟨hqhm, hqhd⟩ := mers_monic Hp i
          (fun i' h1 hik => ⟨(hHp i' h1 (by omega)).1, (hHp i' h1 (by omega)).2.1⟩)
          (by omega) (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))
        refine { pair := ?_, wlt := ?_, qh_monic := hqhm, qh_deg := hqhd, HK := hiK }
        · exact compatiblePair_aux_add_left him hid hiK hqm hqd (by
            have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
            have hle2 : (2:ℕ) ^ (i - 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
            omega) (α (doff (kk + 4) i))
        · intro j hj
          have hjr := Finset.mem_range.1 hj
          have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
          omega
      obtain ⟨hβ₀, hβ₁, hβ₂, hα₀', hα₁', hS₁, hS₂, hlev⟩ :=
        fill_correct (K := K)
          (S := (Hp (kk + 3) + mers Hp (kk + 2) (fun j => α (6 + j)),
                 Hp (kk + 3) + C (α 5)))
          (H := Hp) (D := mersD Hp (mers Hp) (kk + 4) α)
          (Wh := fun i => Finset.range (2 ^ (i - 1) - 1 + 1))
          (n := 2 ^ (kk + 3)) (l := kk + 2) (G := Finset.range (2 ^ (kk + 2) - 1 + 1))
          (β₀ := α 0) (β₁ := α 1) (β₂ := α 2) (α₀ := α 3) (α₁ := α 4)
          (P := mers Hp (kk + 4) α)
          (by omega) hSpair
          (by intro i hi
              have hir := Finset.mem_range.1 hi
              have h1p : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
              have hsum : (2:ℕ) ^ (kk + 3) = 2 ^ (kk + 2) + 2 ^ (kk + 2) := by ring
              omega)
          (Nat.pow_le_pow_right (by omega) (by omega))
          hgood h1m (h1d2.trans (by norm_num)) h1K (mers_unfold Hp kk α)
      have hle : K ⊔ adjoin R (Set.range fun i => (mers Hp (kk + 4) α).coeff i) ≤ V :=
        sup_adjoin_range_le hKV hV
      have hQV : ∀ j, (mers Hp (kk + 2) (fun j => α (6 + j))).coeff j ∈ V :=
        add_known_coeff_mem (fun j => hle (hS₁ j)) (fun j => hKV (h3K j))
      have hα5 : α 5 ∈ V := by
        have hc0 : (Hp (kk + 3) + C (α 5)).coeff 0 ∈ V := hle (hS₂ 0)
        have hkey : α 5 = (Hp (kk + 3) + C (α 5)).coeff 0 - (Hp (kk + 3)).coeff 0 := by
          rw [coeff_add, coeff_C_zero]; ring
        rw [hkey]
        exact Subalgebra.sub_mem _ hc0 (hKV (h3K 0))
      have hblock : ∀ t', t' < 2 ^ (kk + 2) - 1 → α (6 + t') ∈ V := by
        intro t' ht'
        exact ih (kk + 2) (by omega)
          (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
          (fun j => α (6 + j)) V hKV hQV t' ht'
      have hlevel : ∀ i, 2 ≤ i → i ≤ kk + 2 → ∀ r, r < 3 * 2 ^ (i - 1) →
          α (doff (kk + 4) i + r) ∈ V := by
        intro i h2i hi r hr
        obtain ⟨hqV, hbV, hqhV, hahV⟩ := hlev i h2i hi
        match r with
        | 0 => exact hle hbV
        | 1 => exact hle hahV
        | (r' + 2) =>
          rcases Nat.lt_or_ge r' (2 ^ (i - 1) - 1) with hq | hq
          · have hqV' : ∀ j,
                (mers Hp (i - 1) (fun j => α (doff (kk + 4) i + 2 + j))).coeff j ∈ V :=
              fun j => hle (hqV j)
            have hmem := ih (i - 1) (by omega)
              (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
              (fun j => α (doff (kk + 4) i + 2 + j)) V hKV hqV' r' hq
            have heq : doff (kk + 4) i + 2 + r' = doff (kk + 4) i + (r' + 2) := by omega
            rw [← heq]
            exact hmem
          · have hqhV' : ∀ j,
                (mers Hp i
                  (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j))).coeff j ∈ V :=
              fun j => hle (hqhV j)
            have hsum : (2:ℕ) ^ i = 2 ^ (i - 1) + 2 ^ (i - 1) := by
              have hi1 : i - 1 + 1 = i := by omega
              calc (2:ℕ) ^ i = 2 ^ (i - 1 + 1) := by rw [hi1]
              _ = 2 ^ (i - 1) + 2 ^ (i - 1) := by ring
            have h1p : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
            have hmem := ih i (by omega)
              (fun i' h1 hik => hHp i' h1 (by omega)) (by omega)
              (fun j => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j)) V hKV hqhV'
              (r' - (2 ^ (i - 1) - 1)) (by omega)
            have heq : doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + (r' - (2 ^ (i - 1) - 1))
                = doff (kk + 4) i + (r' + 2) := by omega
            rw [← heq]
            exact hmem
      intro t ht
      rcases Nat.lt_or_ge t 6 with h6 | h6
      · match t with
        | 0 => exact hle hβ₀
        | 1 => exact hle hβ₁
        | 2 => exact hle hβ₂
        | 3 => exact hle hα₀'
        | 4 => exact hle hα₁'
        | 5 => exact hα5
        | (s + 6) => omega
      · rcases Nat.lt_or_ge t (6 + (2 ^ (kk + 2) - 1)) with hm | hm
        · have heq : 6 + (t - 6) = t := by omega
          rw [← heq]
          exact hblock (t - 6) (by omega)
        · have h1W : (1:ℕ) ≤ 2 ^ (kk + 2) := Nat.one_le_pow _ _ (by omega)
          have hend : (2:ℕ) ^ (kk + 4) = 4 * 2 ^ (kk + 2) := by ring
          obtain ⟨i₀, hi1, him, hvle, hvlt⟩ := exists_pow_interval (kk + 2)
            ((t - (5 + 2 ^ (kk + 2))) / 3 + 2) (by omega) (by omega)
          have hdoff : doff (kk + 4) (i₀ + 1) = 5 + 2 ^ (kk + 2) + 3 * (2 ^ i₀ - 2) := by
            unfold doff
            rw [show kk + 4 - 2 = kk + 2 from rfl, show i₀ + 1 - 1 = i₀ from rfl]
          have hp1 : (2:ℕ) ^ (i₀ + 1) = 2 ^ i₀ + 2 ^ i₀ := by ring
          have h2i0 : (2:ℕ) ≤ 2 ^ i₀ := by
            calc (2:ℕ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ i₀ := Nat.pow_le_pow_right (by omega) (by omega)
          have hr : t - doff (kk + 4) (i₀ + 1) < 3 * 2 ^ (i₀ + 1 - 1) := by
            rw [hdoff, show i₀ + 1 - 1 = i₀ from rfl]
            omega
          have hge : doff (kk + 4) (i₀ + 1) ≤ t := by
            rw [hdoff]
            omega
          have hmem := hlevel (i₀ + 1) (by omega) (by omega)
            (t - doff (kk + 4) (i₀ + 1)) hr
          have heq : doff (kk + 4) (i₀ + 1) + (t - doff (kk + 4) (i₀ + 1)) = t := by omega
          rw [← heq]
          exact hmem

/-- Provenance of the Mersenne construction: every coefficient of `Q_{2^k-1}` lies in any
subalgebra containing the tower coefficients and the parameter block. -/
theorem mers_coeff_mem {K : Subalgebra R A} (Hp : ℕ → A[X]) :
    ∀ k, (∀ i, 1 ≤ i → i < k → ∀ j, (Hp i).coeff j ∈ K) → 1 ≤ k →
      ∀ α : ℕ → A, ∀ V : Subalgebra R A, K ≤ V →
      (∀ t, t < 2 ^ k - 1 → α t ∈ V) →
      ∀ j, (mers Hp k α).coeff j ∈ V := by
  have hXC : ∀ (V : Subalgebra R A) (a : A), a ∈ V →
      ∀ j, ((X : A[X]) + C a).coeff j ∈ V := by
    intro V a ha j
    rw [coeff_add, coeff_X, coeff_C]
    refine Subalgebra.add_mem _ ?_ ?_
    · split
      · exact Subalgebra.one_mem _
      · exact Subalgebra.zero_mem _
    · split
      · exact ha
      · exact Subalgebra.zero_mem _
  have hCmem : ∀ (V : Subalgebra R A) (a : A), a ∈ V → ∀ j, (C a : A[X]).coeff j ∈ V := by
    intro V a ha j
    rw [coeff_C]
    split
    · exact ha
    · exact Subalgebra.zero_mem _
  have haddC : ∀ (V : Subalgebra R A) (P : A[X]) (a : A), (∀ j, P.coeff j ∈ V) → a ∈ V →
      ∀ j, (P + C a).coeff j ∈ V := by
    intro V P a hP ha j
    rw [coeff_add]
    exact Subalgebra.add_mem _ (hP j) (hCmem V a ha j)
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hHp hk α V hKV hα j
    match k with
    | 0 => exact absurd hk (by omega)
    | 1 => exact hXC V (α 0) (hα 0 (by norm_num)) j
    | 2 =>
      show ((X + C (α 2)) * (Hp 1 + C (α 1)) + C (α 0)).coeff j ∈ V
      have h3 : (2:ℕ) ^ 2 - 1 = 3 := by norm_num
      refine haddC V _ (α 0) ?_ (hα 0 (by omega)) j
      intro j'
      refine coeff_mul_mem V (hXC V (α 2) (hα 2 (by omega))) ?_ j'
      exact haddC V _ (α 1) (fun j'' => hKV (hHp 1 (by omega) (by omega) j''))
        (hα 1 (by omega))
    | 3 =>
      show ((X + C (α 0)) * ((Hp 1 + C (α 1)) * (Hp 2 + C (α 5)) + C (α 4))
          + ((Hp 1 + C (α 2)) * (Hp 2 + C (α 6)) + C (α 3))).coeff j ∈ V
      have h7 : (2:ℕ) ^ 3 - 1 = 7 := by norm_num
      rw [coeff_add]
      refine Subalgebra.add_mem _ ?_ ?_
      · refine coeff_mul_mem V (hXC V (α 0) (hα 0 (by omega))) ?_ j
        refine haddC V _ (α 4) ?_ (hα 4 (by omega))
        intro j'
        refine coeff_mul_mem V ?_ ?_ j'
        · exact haddC V _ (α 1) (fun j'' => hKV (hHp 1 (by omega) (by omega) j''))
            (hα 1 (by omega))
        · exact haddC V _ (α 5) (fun j'' => hKV (hHp 2 (by omega) (by omega) j''))
            (hα 5 (by omega))
      · refine haddC V _ (α 3) ?_ (hα 3 (by omega)) j
        intro j'
        refine coeff_mul_mem V ?_ ?_ j'
        · exact haddC V _ (α 2) (fun j'' => hKV (hHp 1 (by omega) (by omega) j''))
            (hα 2 (by omega))
        · exact haddC V _ (α 6) (fun j'' => hKV (hHp 2 (by omega) (by omega) j''))
            (hα 6 (by omega))
    | (kk + 4) =>
      rw [mers_unfold Hp kk α]
      -- arithmetic bridges for the slot bounds
      have h1i4 : (16:ℕ) ≤ 2 ^ (kk + 4) := by
        calc (16:ℕ) = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ (kk + 4) := Nat.pow_le_pow_right (by omega) (by omega)
      have h1k : (4:ℕ) ≤ 2 ^ (kk + 2) := by
        calc (4:ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (kk + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h42 : (2:ℕ) ^ (kk + 4) = 4 * 2 ^ (kk + 2) := by ring
      -- the fill-chain coefficient facts
      have hSP1 : ∀ j', (Hp (kk + 3) + mers Hp (kk + 2) (fun j'' => α (6 + j''))).coeff j' ∈ V := by
        intro j'
        rw [coeff_add]
        refine Subalgebra.add_mem _ (hKV (hHp (kk + 3) (by omega) (by omega) j')) ?_
        refine ih (kk + 2) (by omega) (fun i' h1' hik' j'' => hHp i' h1' (by omega) j'')
          (by omega) (fun j'' => α (6 + j'')) V hKV (fun t ht => hα (6 + t) (by
            have hle : (2:ℕ) ^ (kk + 2) ≤ 2 ^ (kk + 4) := Nat.pow_le_pow_right (by omega) (by omega)
            omega)) j'
      have hSP2 : ∀ j', (Hp (kk + 3) + C (α 5)).coeff j' ∈ V :=
        haddC V _ (α 5) (fun j'' => hKV (hHp (kk + 3) (by omega) (by omega) j''))
          (hα 5 (by omega))
      have hlev : ∀ i, 2 ≤ i → i ≤ kk + 2 →
          (∀ j', (Hp i).coeff j' ∈ V) ∧
          (∀ j', (mersD Hp (mers Hp) (kk + 4) α i).q.coeff j' ∈ V) ∧
          (mersD Hp (mers Hp) (kk + 4) α i).b ∈ V ∧
          (∀ j', (mersD Hp (mers Hp) (kk + 4) α i).qh.coeff j' ∈ V) ∧
          (mersD Hp (mers Hp) (kk + 4) α i).ah ∈ V := by
        intro i h2i hi
        have hdoff : doff (kk + 4) i = 5 + 2 ^ (kk + 2) + 3 * (2 ^ (i - 1) - 2) := by
          unfold doff
          rw [show kk + 4 - 2 = kk + 2 from rfl]
        have h1a : (1:ℕ) ≤ 2 ^ (i - 1) := Nat.one_le_pow _ _ (by omega)
        have hia : (2:ℕ) ^ (i - 1) ≤ 2 ^ (kk + 1) := Nat.pow_le_pow_right (by omega) (by omega)
        have h21 : (2:ℕ) ^ (kk + 2) = 2 ^ (kk + 1) + 2 ^ (kk + 1) := by ring
        have hi1 : i - 1 + 1 = i := by omega
        have hdb : (2:ℕ) ^ i = 2 ^ (i - 1) + 2 ^ (i - 1) := by
          calc (2:ℕ) ^ i = 2 ^ (i - 1 + 1) := by rw [hi1]
          _ = 2 ^ (i - 1) + 2 ^ (i - 1) := by ring
        have hib : (2:ℕ) ^ i ≤ 2 ^ (kk + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        refine ⟨fun j' => hKV (hHp i (by omega) (by omega) j'), ?_, ?_, ?_, ?_⟩
        · show ∀ j', (mers Hp (i - 1) (fun j'' => α (doff (kk + 4) i + 2 + j''))).coeff j' ∈ V
          intro j'
          refine ih (i - 1) (by omega) (fun i' h1' hik' j'' => hHp i' h1' (by omega) j'')
            (by omega) (fun j'' => α (doff (kk + 4) i + 2 + j'')) V hKV
            (fun t ht => hα (doff (kk + 4) i + 2 + t) (by omega)) j'
        · show α (doff (kk + 4) i) ∈ V
          exact hα _ (by omega)
        · show ∀ j', (mers Hp i
              (fun j'' => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j''))).coeff j' ∈ V
          intro j'
          refine ih i (by omega) (fun i' h1' hik' j'' => hHp i' h1' (by omega) j'')
            (by omega) (fun j'' => α (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + j'')) V hKV
            (fun t ht => hα (doff (kk + 4) i + 2 + (2 ^ (i - 1) - 1) + t) (by omega)) j'
        · show α (doff (kk + 4) i + 1) ∈ V
          exact hα _ (by omega)
      obtain ⟨hCH1, hCH2⟩ := fillChain_coeff_mem (V := V) Hp
        (mersD Hp (mers Hp) (kk + 4) α) (kk + 2)
        (Hp (kk + 3) + mers Hp (kk + 2) (fun j'' => α (6 + j'')),
         Hp (kk + 3) + C (α 5)) hlev hSP1 hSP2
      rw [coeff_add]
      refine Subalgebra.add_mem _ ?_ ?_
      · refine coeff_mul_mem V (hXC V (α 0) (hα 0 (by omega))) ?_ j
        refine haddC V _ (α 4) ?_ (hα 4 (by omega))
        intro j'
        refine coeff_mul_mem V ?_ hCH1 j'
        exact haddC V _ (α 1) (fun j'' => hKV (hHp 1 (by omega) (by omega) j''))
          (hα 1 (by omega))
      · refine haddC V _ (α 3) ?_ (hα 3 (by omega)) j
        intro j'
        refine coeff_mul_mem V ?_ hCH2 j'
        exact haddC V _ (α 2) (fun j'' => hKV (hHp 1 (by omega) (by omega) j''))
          (hα 2 (by omega))
