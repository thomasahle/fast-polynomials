import FastPoly.Section6.QOddDegree

/-!
# Gadget decoders in `V`-relative form

The two constructive `𝒬_d` gadgets, packaged in the exact shape the induction steps
(`eightk3_decodable`/`eightk7_decodable`) consume: any subalgebra containing the gadget's
output coefficients (and the supplied powers) contains every parameter block, plus the
byproduct quartic for `Q_{4k+1}`.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]
variable {K : Subalgebra R A} {k : ℕ} {α : ℕ → A} {H2 : A[X]} {γ ρ a e β : A}

/-- **V-relative decoder for `Q_{4k+1}`** (`lem:Q4k+1-from-H2`, packaged in the form the
induction steps consume): any subalgebra containing the coefficients of `Q_{4k+1}` and of
the quadratic `H₂` contains the five gadget parameters, the coefficients of the byproduct
quartic `Ĥ₄`, and the full slot block. -/
theorem q4k1_decodable (hk : 1 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    (h2 : IsUnit (2 : R))
    (hH2m : H2.Monic) (hH2d : H2.natDegree = 2) (γ ρ a e β : A)
    (V : Subalgebra R A) (hH2V : ∀ j, H2.coeff j ∈ V)
    (hQV : ∀ j, (q4k1 H2 γ ρ a e β k α).coeff j ∈ V) :
    (β ∈ V ∧ γ ∈ V ∧ a ∈ V ∧ e ∈ V ∧ ρ ∈ V)
    ∧ (∀ j, (crownH4 (H2.coeff 1) (H2.coeff 0 + γ) a e).coeff j ∈ V)
    ∧ (∀ t, t < (k - 1) * 4 → α t ∈ V) := by
  classical
  -- the five parameters, via the `Vis`-form instantiated at context `V`
  have hVle : ∀ t, Vis R V (q4k1 H2 γ ρ a e β k α) (Finset.range (4 * k + 2)) t ≤ V :=
    fun t => Vis_le le_rfl fun i _ _ => hQV i
  obtain ⟨hβ, hγ, ha, he, hρ⟩ :=
    q4k1_param_vis (K := V) (α := α) hk hadm hH2m hH2d hH2V γ ρ a e β
  have hβV : β ∈ V := hVle _ hβ
  have hγV : γ ∈ V := hVle _ hγ
  have haV : a ∈ V := hVle _ ha
  have heV : e ∈ V := hVle _ he
  have hρV : ρ ∈ V := hVle _ hρ
  -- the crown tower data over `V`
  set b' : A := H2.coeff 1 with hb'
  set c' : A := H2.coeff 0 + γ with hc'
  have hb'V : b' ∈ V := hH2V 1
  have hc'V : c' ∈ V := add_mem (hH2V 0) hγV
  have hH4V : ∀ j, (crownH4 b' c' a e).coeff j ∈ V :=
    crownH4_coeff_mem hb'V hc'V haV heV
  refine ⟨⟨hβV, hγV, haV, heV, hρV⟩, hH4V, ?_⟩
  -- degree bookkeeping for the tower
  obtain ⟨hH2m', hH2d'⟩ := crownH2_monic (A := A) (b := b') (c := c')
  obtain ⟨hH4m, hH4d⟩ := crownH4_monic (A := A) (b := b') (c := c') (a := a) (e := e)
  obtain ⟨hHtm, hHtd⟩ := crownH4t_good (b := b') (c := c') (a := a) (e := e) ρ
  have htowerV : ∀ i, 1 ≤ i → i ≤ 2 → ((crownHp b' c' a e) i).Monic ∧
      ((crownHp b' c' a e) i).natDegree = 2 ^ i ∧
      (∀ j, ((crownHp b' c' a e) i).coeff j ∈ V) := by
    intro i h1 hi
    rcases Nat.lt_or_ge i 2 with h | h
    · have hie : i = 1 := by omega
      subst hie
      rw [crownHp_one]
      exact ⟨hH2m', by rw [hH2d']; norm_num, crownH2_coeff_mem hb'V hc'V⟩
    · have hie : i = 2 := by omega
      subst hie
      rw [crownHp_two]
      exact ⟨hH4m, by rw [hH4d]; norm_num, hH4V⟩
  have hHtV : ∀ j, (crownH4 b' c' a e + C ρ).coeff j ∈ V :=
    coeff_add_C_mem hH4V hρV
  -- the compatible pair at context `V`, and `(x+β)`-extraction of the `T`-pair
  have hcp : CompatiblePair V
      (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1
      (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).2 (k * 2 ^ 2)
      (Finset.range ((k - 1) * 2 ^ 2)) :=
    Tpair_compatiblePair hk le_rfl htowerV hHtm (by rw [hHtd]; norm_num) hHtV
      (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
      (fun n h1 h2' => hadm n h1 (by omega))
  have hP : q4k1 H2 γ ρ a e β k α
      = (X + C β) * (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1
        + (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).2 := by
    unfold q4k1
    rfl
  obtain ⟨-, hT₁, hT₂⟩ := x_alpha_mem hcp
    (by have h4 : k * 2 ^ 2 = 4 * k := by ring
        rw [h4]; omega)
    (fun i hi => by
      simp only [Finset.mem_range] at hi ⊢
      have h4 : (2:ℕ) ^ 2 = 4 := by norm_num
      rw [h4] at hi ⊢
      omega) hP
  have hVQ : V ⊔ adjoin R (Set.range fun i => (q4k1 H2 γ ρ a e β k α).coeff i) ≤ V :=
    sup_le le_rfl (adjoin_le (by rintro _ ⟨i, rfl⟩; exact hQV i))
  have hT₁V : ∀ j,
      (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).1.coeff j ∈ V :=
    fun j => hVQ (hT₁ j)
  have hT₂V : ∀ j,
      (Tpair (crownHp b' c' a e) (crownH4 b' c' a e + C ρ) k 2 α).2.coeff j ∈ V :=
    fun j => hVQ (hT₂ j)
  -- the remainder pair's combined coefficients, and the slot extraction
  have hcombR := Rpair_combined_coeff_mem (V := V) hT₁V hT₂V
    (fun j => by rw [show crownHp b' c' a e 2 = crownH4 b' c' a e from
      crownHp_two]; exact hH4V j) hHtV
  intro t ht
  refine Rk2l_extract (K := V) (V := V) k hk 2 α le_rfl htowerV hHtm
    (by rw [hHtd]; norm_num) hHtV
    (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
    (fun n h1 h2' => hadm n h1 (by omega)) h2 le_rfl hcombR t ?_
  simp only [show (2:ℕ) ^ 2 = 4 from by norm_num]
  omega

section qodd

variable {Hp : ℕ → A[X]} {l : ℕ} {β' : ℕ → A} {δ : A}

/-- V-relative form of `q_odd_degree_decodable`, as consumed by the `𝒬_d` dispatch. -/
theorem q_odd_degree_decodable' (hk : 1 ≤ k) (hl : 2 ≤ l)
    (htower : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ K))
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    {D : ℕ → FillData A} {Wh : ℕ → Finset ℕ}
    (hgood : ∀ i, 2 ≤ i → i ≤ l - 1 → GoodLevel K (Hp i) (D i) i (Wh i))
    {β₀ β₁ β₂ α₀ α₁ : A} {P : A[X]}
    (hP : P = (X + C β₀) * ((Hp 1 + C β₁)
        * (fillChain Hp D (l - 1)
            (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β'))
              (Hp l + peel Hp (l - 1) β' + C δ) (2 * k) l α)).1 + C α₁)
      + ((Hp 1 + C β₂)
          * (fillChain Hp D (l - 1)
              (Tpair (Function.update Hp l (Hp l + peel Hp (l - 1) β'))
                (Hp l + peel Hp (l - 1) β' + C δ) (2 * k) l α)).2 + C α₀))
    (V : Subalgebra R A) (hKV : K ≤ V) (hPV : ∀ j, P.coeff j ∈ V) :
    β₀ ∈ V ∧ β₁ ∈ V ∧ β₂ ∈ V ∧ α₀ ∈ V ∧ α₁ ∈ V ∧
    (∀ i, 2 ≤ i → i ≤ l - 1 → LevelMem V (D i)) ∧
    (∀ t, t < 2 ^ (l - 1) - 1 → β' t ∈ V) ∧
    δ ∈ V ∧
    (∀ t, t < (2 * k - 1) * 2 ^ l → α t ∈ V) := by
  have hle : K ⊔ adjoin R (Set.range fun i => P.coeff i) ≤ V :=
    sup_le hKV (adjoin_le (by rintro _ ⟨i, rfl⟩; exact hPV i))
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    q_odd_degree_decodable (β := β') (δ := δ) hk hl htower hadm hgood hP
  refine ⟨hle h1, hle h2, hle h3, hle h4, hle h5, ?_,
    fun t ht => hle (h7 t ht), hle h8, fun t ht => hle (h9 t ht)⟩
  intro i hi hi'
  obtain ⟨hq, hb, hqh, hah⟩ := h6 i hi hi'
  exact ⟨fun j => hle (hq j), hle hb, fun j => hle (hqh j), hle hah⟩
end qodd

/-- **Pair-level decoder for the `4k+1` branch** (`lem:4k+1-splittable`, decodability
half): any subalgebra containing the combined coefficients of the crown pair contains
the five crown parameters, the two recorded powers, and the full slot block. -/
theorem fourk_decodable (hk : 1 ≤ k)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * k → IsUnit (((n : ℕ) : ℤ) : R))
    (h2 : IsUnit (2 : R)) (b c a e ρ : A) (α : ℕ → A)
    (V : Subalgebra R A)
    (hPV : ∀ j, (combined
      (Tpair (crownHp b c a e) (crownH4 b c a e + C ρ) k 2 α).1
      (Tpair (crownHp b c a e) (crownH4 b c a e + C ρ) k 2 α).2).coeff j ∈ V) :
    (b ∈ V ∧ c ∈ V ∧ a ∈ V ∧ e ∈ V ∧ ρ ∈ V)
    ∧ (∀ j, (crownH2 b c).coeff j ∈ V)
    ∧ (∀ j, (crownH4 b c a e).coeff j ∈ V)
    ∧ (∀ t, t < (k - 1) * 4 → α t ∈ V) := by
  classical
  have hVle : ∀ t, Vis R V (combined
      (Tpair (crownHp b c a e) (crownH4 b c a e + C ρ) k 2 α).1
      (Tpair (crownHp b c a e) (crownH4 b c a e + C ρ) k 2 α).2)
      (Finset.range (4 * k + 1)) t ≤ V :=
    fun t => Vis_le le_rfl fun i _ _ => hPV i
  obtain ⟨hb, hc, ha, he, hρ⟩ := fourk_param_vis (K := V) (α := α) hk hadm b c a e ρ
  have hbV : b ∈ V := hVle _ hb
  have hcV : c ∈ V := hVle _ hc
  have haV : a ∈ V := hVle _ ha
  have heV : e ∈ V := hVle _ he
  have hρV : ρ ∈ V := hVle _ hρ
  have hH2V : ∀ j, (crownH2 b c).coeff j ∈ V := crownH2_coeff_mem hbV hcV
  have hH4V : ∀ j, (crownH4 b c a e).coeff j ∈ V := crownH4_coeff_mem hbV hcV haV heV
  refine ⟨⟨hbV, hcV, haV, heV, hρV⟩, hH2V, hH4V, ?_⟩
  -- degree bookkeeping
  obtain ⟨hH2m', hH2d'⟩ := crownH2_monic (A := A) (b := b) (c := c)
  obtain ⟨hH4m, hH4d⟩ := crownH4_monic (A := A) (b := b) (c := c) (a := a) (e := e)
  obtain ⟨hHtm, hHtd⟩ := crownH4t_good (b := b) (c := c) (a := a) (e := e) ρ
  have htowerV : ∀ i, 1 ≤ i → i ≤ 2 → ((crownHp b c a e) i).Monic ∧
      ((crownHp b c a e) i).natDegree = 2 ^ i ∧
      (∀ j, ((crownHp b c a e) i).coeff j ∈ V) := by
    intro i h1 hi
    rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
    · rw [crownHp_one]
      exact ⟨hH2m', by rw [hH2d']; norm_num, hH2V⟩
    · rw [crownHp_two]
      exact ⟨hH4m, by rw [hH4d]; norm_num, hH4V⟩
  have hHtV : ∀ j, (crownH4 b c a e + C ρ).coeff j ∈ V :=
    coeff_add_C_mem hH4V hρV
  -- the pair's own coefficients
  obtain ⟨hT₁V, hT₂V⟩ := CausalPair.coeff_mem_of_le
    (fourk_crown_compatible (K := V) hk hadm b c a e ρ α).toCausalPair
    le_rfl hPV
  -- the remainder pair's combined coefficients
  have hcombR := Rpair_combined_coeff_mem (V := V) hT₁V hT₂V
    (fun j => by rw [show crownHp b c a e 2 = crownH4 b c a e from
      crownHp_two]; exact hH4V j) hHtV
  intro t ht
  refine Rk2l_extract (K := V) (V := V) k hk 2 α le_rfl htowerV hHtm
    (by rw [hHtd]; norm_num) hHtV
    (fun _ _ _ => ⟨ρ, crownHp_sd ρ⟩)
    (fun n h1 h2' => hadm n h1 (by omega)) h2 le_rfl hcombR t ?_
  simp only [show (2:ℕ) ^ 2 = 4 from by norm_num]
  omega

end FastPoly
