import FastPoly.Section4.FillTwo

/-!
# The fill construction: one general step

The construction invariant behind `alg:constr-fill` (paper `lem:fill-correctness`): one
level of the fill recursion

  `S₁' = (H + q)·S₁ + qh`,   `S₂' = (H + C b)·S₂ + C ah`

maps a compatible pair on a low window to a compatible pair on the assembled window,
via Multiplicativity with the head pair `(H + q, H + C b)` and equal-degree Additivity with
the low-padding pair `(X^{n+h} + qh, X^{n+h} + ah)`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

/-- Shared disjointness/multiplicativity setup of `fillStep_compat` and `fillStep_mem`:
the two window-disjointness facts and the product pair at degree `n + h`. -/
private theorem fillStep_core {K : Subalgebra R A} {S₁ S₂ H q : A[X]} {b : A}
    {n h e r : ℕ} {G Wh : Finset ℕ}
    (hS : CompatiblePair K S₁ S₂ n G) (hGlt : ∀ i ∈ G, i < n - h)
    (hpair : CompatiblePair K (H + q) (H + C b) h Wh) (hWhlt : ∀ i ∈ Wh, i < e)
    (hrh : r ≤ h) (hhn : h ≤ n) :
    Disjoint (shiftW n Wh) (shiftW h G) ∧
    Disjoint (shiftW n Wh ∪ shiftW h G) (Finset.range r) ∧
    CompatiblePair K ((H + q) * S₁) ((H + C b) * S₂) (n + h)
      (shiftW n Wh ∪ shiftW h G) := by
  have hdis₁ : Disjoint (shiftW n Wh) (shiftW h G) := by
    rw [Finset.disjoint_left]
    intro a h₁ h₂
    rcases mem_shiftW.1 h₁ with ⟨i, hi, rfl⟩
    rcases mem_shiftW.1 h₂ with ⟨i', hi', hii'⟩
    have h1 := hWhlt i hi
    have h2 := hGlt i' hi'
    omega
  have hdis₂ : Disjoint (shiftW n Wh ∪ shiftW h G) (Finset.range r) := by
    rw [Finset.disjoint_left]
    intro a h₁ h₂
    have har : a < r := Finset.mem_range.1 h₂
    rcases Finset.mem_union.1 h₁ with h₁ | h₁
    · have := le_of_mem_shiftW h₁; omega
    · have := le_of_mem_shiftW h₁; omega
  have hmul := hpair.mul hS hdis₁
  exact ⟨hdis₁, hdis₂, by rwa [Nat.add_comm h n] at hmul⟩

/-- **One fill step preserves compatibility** (the construction half of
`lem:fill-correctness`).  Hypotheses: the input pair `(S₁,S₂)` of degree `n` on `G` with
`G` below `n - h`; the head pair `(H + q, H + C b)` of degree `h` on `Wh` with `Wh` below
`e`; the additive part `qh` monic of degree `r - 1`.  Output: degree `n + h` on
`range r ∪ (shiftW n Wh ∪ shiftW h G)`, which lies below `n + e` when `e ≤ h ≤ n`,
`r ≤ h`. -/
theorem fillStep_compat {K : Subalgebra R A} {S₁ S₂ H q qh : A[X]} {b ah : A}
    {n h e r : ℕ} {G Wh : Finset ℕ}
    (hS : CompatiblePair K S₁ S₂ n G) (hGlt : ∀ i ∈ G, i < n - h)
    (hpair : CompatiblePair K (H + q) (H + C b) h Wh) (hWhlt : ∀ i ∈ Wh, i < e)
    (hqh : qh.Monic) (hdqh : qh.natDegree = r - 1)
    (hr1 : 1 ≤ r) (hrh : r ≤ h) (heh : e ≤ h) (hhn : h ≤ n) :
    CompatiblePair K ((H + q) * S₁ + qh) ((H + C b) * S₂ + C ah) (n + h)
      (Finset.range r ∪ (shiftW n Wh ∪ shiftW h G)) ∧
    (∀ i ∈ Finset.range r ∪ (shiftW n Wh ∪ shiftW h G), i < n + e) := by
  classical
  obtain ⟨-, hdis₂, hmul'⟩ := fillStep_core hS hGlt hpair hWhlt hrh hhn
  -- Additivity with the low-padding pair
  have hpad : CompatiblePair K ((X : A[X]) ^ (n + h) + qh) ((X : A[X]) ^ (n + h) + C ah)
      (n + h) (Finset.range r) :=
    compatiblePair_low_padding hr1 (by omega) hqh hdqh ah
  have hadd := hmul'.add_of_eq hpad hdis₂
  have hE1 : (H + q) * S₁ + ((X : A[X]) ^ (n + h) + qh) - X ^ (n + h)
      = (H + q) * S₁ + qh := by ring
  have hE2 : (H + C b) * S₂ + ((X : A[X]) ^ (n + h) + C ah) - X ^ (n + h)
      = (H + C b) * S₂ + C ah := by ring
  rw [hE1, hE2] at hadd
  have hwin : ∀ i ∈ Finset.range r ∪ (shiftW n Wh ∪ shiftW h G), i < n + e := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · have := Finset.mem_range.1 hi; omega
    · rcases Finset.mem_union.1 hi with hi | hi
      · rcases mem_shiftW.1 hi with ⟨i', hi', rfl⟩
        have := hWhlt i' hi'; omega
      · rcases mem_shiftW.1 hi with ⟨i', hi', rfl⟩
        have := hGlt i' hi'; omega
  refine ⟨?_, hwin⟩
  refine hadd.mono le_rfl ?_ ?_
  · rw [Finset.union_comm]
  · intro i hi
    exact Finset.mem_range.2 (by have := hwin i hi; omega)

/-- **One fill step is decodable** (the recovery half of `lem:fill-correctness`): if all
coefficients of the stepped pair lie in a subalgebra `V ⊇ K`, then so do all coefficients of
the input pair, of the head polynomial `q`, of the additive part `qh`, and the scalars
`b, ah`.  Everything is transported through the three separation engines. -/
theorem fillStep_mem {K : Subalgebra R A} {S₁ S₂ H q qh : A[X]} {b ah : A}
    {n h e r : ℕ} {G Wh : Finset ℕ}
    (hS : CompatiblePair K S₁ S₂ n G) (hGlt : ∀ i ∈ G, i < n - h)
    (hpair : CompatiblePair K (H + q) (H + C b) h Wh) (hWhlt : ∀ i ∈ Wh, i < e)
    (hqh : qh.Monic) (hdqh : qh.natDegree = r - 1)
    (hr1 : 1 ≤ r) (hrh : r ≤ h) (heh : e ≤ h) (hhn : h ≤ n)
    (hHK : ∀ j, H.coeff j ∈ K)
    {V : Subalgebra R A} (hKV : K ≤ V)
    (hV₁ : ∀ j, ((H + q) * S₁ + qh).coeff j ∈ V)
    (hV₂ : ∀ j, ((H + C b) * S₂ + C ah).coeff j ∈ V) :
    (∀ j, S₁.coeff j ∈ V) ∧ (∀ j, S₂.coeff j ∈ V) ∧
    (∀ j, q.coeff j ∈ V) ∧ b ∈ V ∧ (∀ j, qh.coeff j ∈ V) ∧ ah ∈ V := by
  classical
  obtain ⟨hdis₁, hdis₂, hmul'⟩ := fillStep_core hS hGlt hpair hWhlt hrh hhn
  have hpad : CompatiblePair K ((X : A[X]) ^ (n + h) + qh) ((X : A[X]) ^ (n + h) + C ah)
      (n + h) (Finset.range r) :=
    compatiblePair_low_padding hr1 (by omega) hqh hdqh ah
  -- the raw sum pair and its relation to the stepped pair
  set PL₁ := (H + q) * S₁ with hPL₁
  set PL₂ := (H + C b) * S₂ with hPL₂
  set PR₁ := (X : A[X]) ^ (n + h) + qh with hPR₁
  set PR₂ := (X : A[X]) ^ (n + h) + C ah with hPR₂
  have hsum₁ : PL₁ + PR₁ = ((H + q) * S₁ + qh) + X ^ (n + h) := by
    rw [hPL₁, hPR₁]; ring
  have hsum₂ : PL₂ + PR₂ = ((H + C b) * S₂ + C ah) + X ^ (n + h) := by
    rw [hPL₂, hPR₂]; ring
  -- the visible algebra of the raw sum's combined polynomial embeds into V
  have hVsum : ∀ (Gw : Finset ℕ) (t : ℕ),
      Vis R K (combined (PL₁ + PR₁) (PL₂ + PR₂)) Gw t ≤ V := by
    intro Gw t
    refine Vis_le hKV ?_
    intro i _ _
    have hkey : (combined (PL₁ + PR₁) (PL₂ + PR₂)).coeff i
        = (combined ((H + q) * S₁ + qh) ((H + C b) * S₂ + C ah)).coeff i
          + (combined ((X : A[X]) ^ (n + h)) ((X : A[X]) ^ (n + h))).coeff i := by
      rw [show combined (PL₁ + PR₁) (PL₂ + PR₂)
          = combined ((H + q) * S₁ + qh) ((H + C b) * S₂ + C ah)
            + combined ((X : A[X]) ^ (n + h)) ((X : A[X]) ^ (n + h)) from by
        simp only [combined, hsum₁, hsum₂]; ring, coeff_add]
    rw [hkey]
    refine Subalgebra.add_mem _ ?_ ?_
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [coeff_combined_zero]
        exact hV₂ 0
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [coeff_combined]
        exact Subalgebra.add_mem _ (hV₁ i') (hV₂ (i' + 1))
    · rcases Nat.eq_zero_or_pos i with rfl | hi
      · rw [coeff_combined_zero]
        exact hKV (coeff_X_pow_mem K (n + h) 0)
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        rw [coeff_combined]
        exact Subalgebra.add_mem _ (hKV (coeff_X_pow_mem K (n + h) i'))
          (hKV (coeff_X_pow_mem K (n + h) (i' + 1)))
  -- the product pair's visible algebra embeds into V (through Additivity)
  have hVprod : ∀ t, Vis R K (combined PL₁ PL₂) (shiftW n Wh ∪ shiftW h G) t ≤ V :=
    fun t => le_trans
      (vis_le_vis_add hmul'.toCausalPair hpad.toCausalPair hdis₂ t) (hVsum _ t)
  -- the input pair and the head pair embed into V (through Multiplicativity)
  have hVS : ∀ t, Vis R K (combined S₁ S₂) G t ≤ V :=
    fun t => le_trans (vis_le_vis_mul' hpair hS hdis₁ t) (hVprod (h + t))
  have hVhead : ∀ t, Vis R K (combined (H + q) (H + C b)) Wh t ≤ V :=
    fun t => le_trans (vis_le_vis_mul hpair hS hdis₁ t) (hVprod (n + t))
  -- conclusions
  have hS₁V : ∀ j, S₁.coeff j ∈ V := fun j => hVS (j + 1) (hS.mem₁ j)
  have hS₂V : ∀ j, S₂.coeff j ∈ V := fun j => hVS j (hS.mem₂ j)
  have hheadV₁ : ∀ j, (H + q).coeff j ∈ V := fun j => hVhead (j + 1) (hpair.mem₁ j)
  have hheadV₂ : ∀ j, (H + C b).coeff j ∈ V := fun j => hVhead j (hpair.mem₂ j)
  have hqV : ∀ j, q.coeff j ∈ V := by
    intro j
    have hkey : q.coeff j = (H + q).coeff j - H.coeff j := by
      rw [coeff_add]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hheadV₁ j) (hKV (hHK j))
  have hbV : b ∈ V := by
    have hkey : b = (H + C b).coeff 0 - H.coeff 0 := by
      rw [coeff_add, coeff_C, if_pos rfl]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hheadV₂ 0) (hKV (hHK 0))
  have hprodV₁ : ∀ j, PL₁.coeff j ∈ V := fun j => hVprod (j + 1) (hmul'.mem₁ j)
  have hprodV₂ : ∀ j, PL₂.coeff j ∈ V := fun j => hVprod j (hmul'.mem₂ j)
  have hqhV : ∀ j, qh.coeff j ∈ V := by
    intro j
    have hkey : qh.coeff j = ((H + q) * S₁ + qh).coeff j - PL₁.coeff j := by
      rw [hPL₁, coeff_add]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hV₁ j) (hprodV₁ j)
  have hahV : ah ∈ V := by
    have hkey : ah = ((H + C b) * S₂ + C ah).coeff 0 - PL₂.coeff 0 := by
      rw [hPL₂, coeff_add, coeff_C, if_pos rfl]; ring
    rw [hkey]
    exact Subalgebra.sub_mem _ (hV₂ 0) (hprodV₂ 0)
  exact ⟨hS₁V, hS₂V, hqV, hbV, hqhV, hahV⟩
