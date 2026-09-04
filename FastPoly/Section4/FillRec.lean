import FastPoly.Section4.Fill
import FastPoly.Polynomial.SquareGadget

/-!
# The fill chain

Iterating the general fill step over levels `l, l-1, …, 2` (level `1` and the final
`(x+β₀)`-step are `fill_two_mem`).  The dyadic bookkeeping is exact: a step at level `i`
turns a pair of degree `n` with window below `n - 2^i` into a pair of degree `n + 2^i`
with window below `(n + 2^i) - 2^{i-1}`, which is precisely the hypothesis for level
`i - 1`.
-/

namespace FastPoly

open Polynomial Algebra Finset

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

/-- Per-level data of the fill construction: the head polynomial `q`, the additive part
`qh`, and the two scalars. -/
structure FillData (A : Type*) [CommRing A] where
  q : A[X]
  qh : A[X]
  b : A
  ah : A

/-- One fill step on a pair. -/
noncomputable def fillStep (H : A[X]) (d : FillData A) (S : A[X] × A[X]) : A[X] × A[X] :=
  ((H + d.q) * S.1 + d.qh, (H + C d.b) * S.2 + C d.ah)

/-- The fill chain, applying levels `l, l-1, …, 2` (levels `0, 1` are the identity here;
level `1` is handled by `fill_two_mem`). -/
noncomputable def fillChain (H : ℕ → A[X]) (D : ℕ → FillData A) :
    (l : ℕ) → A[X] × A[X] → A[X] × A[X]
  | 0, S => S
  | 1, S => S
  | (i + 2), S => fillChain H D (i + 1) (fillStep (H (i + 2)) (D (i + 2)) S)

/-- Well-formedness of the level-`i` data relative to the known context: the head pair is
compatible on a window below `2^{i-1}`, and the additive part is monic of degree
`2^i - 1`. -/
structure GoodLevel (K : Subalgebra R A) (H : A[X]) (d : FillData A) (i : ℕ)
    (Wh : Finset ℕ) : Prop where
  pair : CompatiblePair K (H + d.q) (H + C d.b) (2 ^ i) Wh
  wlt : ∀ j ∈ Wh, j < 2 ^ (i - 1)
  qh_monic : d.qh.Monic
  qh_deg : d.qh.natDegree = 2 ^ i - 1
  HK : ∀ j, H.coeff j ∈ K

/-- Shared induction-step setup of `fillChain_compat` and `fillChain_mem`: one
`fillStep_compat` application at level `l' + 2`, with the window bound and degree
lower bound needed by the level-`l' + 1` induction hypothesis. -/
private theorem fillChain_step_setup {K : Subalgebra R A} {H : ℕ → A[X]}
    {D : ℕ → FillData A} {Wh : ℕ → Finset ℕ} {l' n : ℕ} {G : Finset ℕ}
    {S : A[X] × A[X]}
    (hS : CompatiblePair K S.1 S.2 n G) (hGlt : ∀ i ∈ G, i < n - 2 ^ (l' + 2))
    (hn : 2 ^ (l' + 2) ≤ n)
    (hg : GoodLevel K (H (l' + 2)) (D (l' + 2)) (l' + 2) (Wh (l' + 2))) :
    CompatiblePair K (fillStep (H (l' + 2)) (D (l' + 2)) S).1
        (fillStep (H (l' + 2)) (D (l' + 2)) S).2 (n + 2 ^ (l' + 2))
        (Finset.range (2 ^ (l' + 2)) ∪
          (shiftW n (Wh (l' + 2)) ∪ shiftW (2 ^ (l' + 2)) G)) ∧
    (∀ i ∈ Finset.range (2 ^ (l' + 2)) ∪
        (shiftW n (Wh (l' + 2)) ∪ shiftW (2 ^ (l' + 2)) G),
        i < (n + 2 ^ (l' + 2)) - 2 ^ (l' + 1)) ∧
    2 ^ (l' + 1) ≤ n + 2 ^ (l' + 2) := by
  have hqhdeg : (D (l' + 2)).qh.natDegree = 2 ^ (l' + 2) - 1 := hg.qh_deg
  have hr1 : (1:ℕ) ≤ 2 ^ (l' + 2) := Nat.one_le_pow _ _ (by omega)
  have heh : (2:ℕ) ^ (l' + 2 - 1) ≤ 2 ^ (l' + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  obtain ⟨hpair', hbound'⟩ := fillStep_compat (K := K) (r := 2 ^ (l' + 2))
    (h := 2 ^ (l' + 2)) (ah := (D (l' + 2)).ah) hS hGlt
    hg.pair hg.wlt hg.qh_monic hqhdeg hr1 le_rfl heh hn
  refine ⟨hpair', ?_, ?_⟩
  · intro i hi
    have h1 := hbound' i hi
    rw [show l' + 2 - 1 = l' + 1 from by omega] at h1
    have hsum : (2:ℕ) ^ (l' + 2) = 2 ^ (l' + 1) + 2 ^ (l' + 1) := by ring
    omega
  · have h3 : (2:ℕ) ^ (l' + 1) ≤ 2 ^ (l' + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- **The fill chain preserves compatibility** with the exact dyadic window bound. -/
theorem fillChain_compat {K : Subalgebra R A} (H : ℕ → A[X]) (D : ℕ → FillData A)
    (Wh : ℕ → Finset ℕ) :
    ∀ l, 1 ≤ l → ∀ n G (S : A[X] × A[X]),
      CompatiblePair K S.1 S.2 n G → (∀ i ∈ G, i < n - 2 ^ l) → (2 ^ l ≤ n) →
      (∀ i, 2 ≤ i → i ≤ l → GoodLevel K (H i) (D i) i (Wh i)) →
      ∃ G', CompatiblePair K (fillChain H D l S).1 (fillChain H D l S).2
          (n + (2 ^ (l + 1) - 4)) G' ∧
        (∀ i ∈ G', i < n + (2 ^ (l + 1) - 4) - 2) := by
  intro l
  induction l with
  | zero => omega
  | succ l ih =>
    intro hl n G S hS hGlt hn hgood
    rcases Nat.lt_or_ge l 1 with hl1 | hl1
    · -- l + 1 = 1: identity
      have : l = 0 := by omega
      subst this
      refine ⟨G, ?_, ?_⟩
      · simpa [fillChain, show (2 : ℕ) ^ 2 - 4 = 0 from by norm_num] using hS
      · intro i hi
        have := hGlt i hi
        simp only [show (2 : ℕ) ^ 2 - 4 = 0 from by norm_num]
        omega
    · -- l + 1 ≥ 2: one step at level l + 1, then the chain at level l
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hg := hgood (l' + 2) (by omega) le_rfl
      obtain ⟨hpair', hbound'', hn'⟩ := fillChain_step_setup hS hGlt hn hg
      have hchain := ih (by omega) (n + 2 ^ (l' + 2)) _
        (fillStep (H (l' + 2)) (D (l' + 2)) S) hpair' hbound'' hn'
        (fun i h2i hil => hgood i h2i (by omega))
      obtain ⟨G', hG'pair, hG'lt⟩ := hchain
      refine ⟨G', ?_, ?_⟩
      · have harith : n + 2 ^ (l' + 2) + (2 ^ (l' + 1 + 1) - 4)
            = n + (2 ^ (l' + 2 + 1) - 4) := by
          have h4 : (4:ℕ) ≤ 2 ^ (l' + 2) := by
            calc (4:ℕ) = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ (l' + 2) := Nat.pow_le_pow_right (by omega) (by omega)
          have h5 : (2:ℕ) ^ (l' + 2 + 1) = 2 ^ (l' + 2) + 2 ^ (l' + 2) := by ring
          have h6 : (2:ℕ) ^ (l' + 1 + 1) = 2 ^ (l' + 2) := by norm_num
          omega
        rw [show fillChain H D (l' + 2) S
            = fillChain H D (l' + 1) (fillStep (H (l' + 2)) (D (l' + 2)) S) from rfl,
          ← harith]
        exact hG'pair
      · intro i hi
        have h1 := hG'lt i hi
        have h4 : (4:ℕ) ≤ 2 ^ (l' + 2) := by
          calc (4:ℕ) = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (l' + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        have h5 : (2:ℕ) ^ (l' + 2 + 1) = 2 ^ (l' + 2) + 2 ^ (l' + 2) := by ring
        have h6 : (2:ℕ) ^ (l' + 1 + 1) = 2 ^ (l' + 2) := by norm_num
        omega

/-- Recovery of one level's data package. -/
def LevelMem (V : Subalgebra R A) (d : FillData A) : Prop :=
  (∀ j, d.q.coeff j ∈ V) ∧ d.b ∈ V ∧ (∀ j, d.qh.coeff j ∈ V) ∧ d.ah ∈ V

/-- **The fill chain is decodable**: if all coefficients of the chain output lie in a
subalgebra `V ⊇ K`, then so do all coefficients of the input pair and all per-level data. -/
theorem fillChain_mem {K : Subalgebra R A} (H : ℕ → A[X]) (D : ℕ → FillData A)
    (Wh : ℕ → Finset ℕ) :
    ∀ l, 1 ≤ l → ∀ n G (S : A[X] × A[X]),
      CompatiblePair K S.1 S.2 n G → (∀ i ∈ G, i < n - 2 ^ l) → (2 ^ l ≤ n) →
      (∀ i, 2 ≤ i → i ≤ l → GoodLevel K (H i) (D i) i (Wh i)) →
      ∀ (V : Subalgebra R A), K ≤ V →
      (∀ j, (fillChain H D l S).1.coeff j ∈ V) →
      (∀ j, (fillChain H D l S).2.coeff j ∈ V) →
      (∀ j, S.1.coeff j ∈ V) ∧ (∀ j, S.2.coeff j ∈ V) ∧
        (∀ i, 2 ≤ i → i ≤ l → LevelMem V (D i)) := by
  intro l
  induction l with
  | zero => omega
  | succ l ih =>
    intro hl n G S hS hGlt hn hgood V hKV hV₁ hV₂
    rcases Nat.lt_or_ge l 1 with hl1 | hl1
    · -- l + 1 = 1: identity chain
      have : l = 0 := by omega
      subst this
      exact ⟨hV₁, hV₂, fun i h2i hi1 => absurd (le_trans h2i hi1) (by omega)⟩
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      have hg := hgood (l' + 2) (by omega) le_rfl
      have hqhdeg : (D (l' + 2)).qh.natDegree = 2 ^ (l' + 2) - 1 := hg.qh_deg
      have hr1 : (1:ℕ) ≤ 2 ^ (l' + 2) := Nat.one_le_pow _ _ (by omega)
      have heh : (2:ℕ) ^ (l' + 2 - 1) ≤ 2 ^ (l' + 2) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      obtain ⟨hpair', hbound'', hn'⟩ := fillChain_step_setup hS hGlt hn hg
      have hchain := ih (by omega) (n + 2 ^ (l' + 2)) _
        (fillStep (H (l' + 2)) (D (l' + 2)) S) hpair' hbound'' hn'
        (fun i h2i hil => hgood i h2i (by omega))
        V hKV hV₁ hV₂
      obtain ⟨hstep₁V, hstep₂V, hlev⟩ := hchain
      -- decode the level-(l'+2) step
      have hdec := fillStep_mem (K := K) (r := 2 ^ (l' + 2)) (h := 2 ^ (l' + 2))
        (ah := (D (l' + 2)).ah) hS hGlt hg.pair hg.wlt hg.qh_monic hqhdeg hr1 le_rfl heh hn
        hg.HK hKV hstep₁V hstep₂V
      obtain ⟨hS₁V, hS₂V, hqV, hbV, hqhV, hahV⟩ := hdec
      refine ⟨hS₁V, hS₂V, ?_⟩
      intro i h2i hi
      rcases Nat.lt_or_ge i (l' + 2) with hlt | hge
      · exact hlev i h2i (by omega)
      · have : i = l' + 2 := by omega
        subst this
        exact ⟨hqV, hbV, hqhV, hahV⟩

/-- **Full fill correctness** (paper `lem:fill-correctness`): the chain over levels
`l, …, 2` followed by the level-1 step and the `(x+β₀)`-head.  All parameters of every
level, the five head parameters, and all coefficients of the input pair are recoverable
from the coefficients of the output `P` given `K`. -/
theorem fill_correct {K : Subalgebra R A} {S : A[X] × A[X]} {H : ℕ → A[X]}
    {D : ℕ → FillData A} {Wh : ℕ → Finset ℕ} {n l : ℕ} {G : Finset ℕ}
    {β₀ β₁ β₂ α₀ α₁ : A} {P : A[X]}
    (hl : 1 ≤ l) (hS : CompatiblePair K S.1 S.2 n G)
    (hGlt : ∀ i ∈ G, i < n - 2 ^ l) (hn : 2 ^ l ≤ n)
    (hgood : ∀ i, 2 ≤ i → i ≤ l → GoodLevel K (H i) (D i) i (Wh i))
    (hH2 : (H 1).Monic) (hdH2 : (H 1).natDegree = 2) (hH2K : ∀ j, (H 1).coeff j ∈ K)
    (hP : P = (X + C β₀) * ((H 1 + C β₁) * (fillChain H D l S).1 + C α₁)
        + ((H 1 + C β₂) * (fillChain H D l S).2 + C α₀)) :
    β₀ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    β₁ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    β₂ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    α₀ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    α₁ ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i) ∧
    (∀ j, S.1.coeff j ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) ∧
    (∀ j, S.2.coeff j ∈ K ⊔ adjoin R (Set.range fun i => P.coeff i)) ∧
    (∀ i, 2 ≤ i → i ≤ l →
      LevelMem (K ⊔ adjoin R (Set.range fun i => P.coeff i)) (D i)) := by
  classical
  have h2l : (2:ℕ) ≤ 2 ^ l := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) hl
  obtain ⟨G', hpair', hG'lt⟩ := fillChain_compat H D Wh l hl n G S hS hGlt hn hgood
  have hn' : 2 ≤ n + (2 ^ (l + 1) - 4) := by omega
  obtain ⟨hβ₀, hβ₁, hβ₂, hα₀, hα₁, hC₁, hC₂⟩ :=
    fill_two_mem K hpair' hG'lt hn' hH2 hdH2 hH2K rfl rfl hP
  obtain ⟨hS₁, hS₂, hlev⟩ := fillChain_mem H D Wh l hl n G S hS hGlt hn hgood
    (K ⊔ adjoin R (Set.range fun i => P.coeff i)) le_sup_left hC₁ hC₂
  exact ⟨hβ₀, hβ₁, hβ₂, hα₀, hα₁, hS₁, hS₂, hlev⟩

omit [Nontrivial A] in
/-- The chain only reads the level data at levels `2..l`. -/
theorem fillChain_congr (H : ℕ → A[X]) {D D' : ℕ → FillData A} :
    ∀ l (S : A[X] × A[X]), (∀ i, 2 ≤ i → i ≤ l → D i = D' i) →
      fillChain H D l S = fillChain H D' l S
  | 0, S, _ => rfl
  | 1, S, _ => rfl
  | (i + 2), S, hEq => by
    show fillChain H D (i + 1) (fillStep (H (i + 2)) (D (i + 2)) S)
        = fillChain H D' (i + 1) (fillStep (H (i + 2)) (D' (i + 2)) S)
    rw [hEq (i + 2) (by omega) le_rfl]
    exact fillChain_congr H (i + 1) _ (fun j h2 hj => hEq j h2 (by omega))

/-- Monicity and degree of the assembled fill output
`P = (x+β₀)((H₂+β₁)S₁ + α₁) + ((H₂+β₂)S₂ + α₀)`. -/
theorem fill_output_monic {H₂ S₁ S₂ : A[X]} {m : ℕ} {β₀ β₁ β₂ α₀ α₁ : A}
    (hH : H₂.Monic) (hdH : H₂.natDegree = 2)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = m)
    (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = m) :
    ((X + C β₀) * ((H₂ + C β₁) * S₁ + C α₁) + ((H₂ + C β₂) * S₂ + C α₀)).Monic ∧
    ((X + C β₀) * ((H₂ + C β₁) * S₁ + C α₁) + ((H₂ + C β₂) * S₂ + C α₀)).natDegree
      = m + 3 := by
  have hA : ∀ (b c : A) (S : A[X]), S.Monic → S.natDegree = m →
      ((H₂ + C b) * S + C c).Monic ∧ ((H₂ + C b) * S + C c).natDegree = m + 2 := by
    intro b c S hS hdS
    obtain ⟨hmb, hdb⟩ := monic_add_C hH (by omega) b
    have hmul : ((H₂ + C b) * S).Monic := hmb.mul hS
    have hdmul : ((H₂ + C b) * S).natDegree = m + 2 := by
      rw [hmb.natDegree_mul hS, hdb, hdH, hdS]; omega
    exact ⟨(monic_add_C hmul (by omega) c).1,
      by rw [(monic_add_C hmul (by omega) c).2, hdmul]⟩
  obtain ⟨hA₁m, hA₁d⟩ := hA β₁ α₁ S₁ hS₁ hd₁
  obtain ⟨hA₂m, hA₂d⟩ := hA β₂ α₀ S₂ hS₂ hd₂
  have hXm : (X + C β₀ : A[X]).Monic := monic_X_add_C β₀
  have hXd : (X + C β₀ : A[X]).natDegree = 1 := by
    simpa using natDegree_X_add_C β₀
  have hheadm : ((X + C β₀) * ((H₂ + C β₁) * S₁ + C α₁)).Monic := hXm.mul hA₁m
  have hheadd : ((X + C β₀) * ((H₂ + C β₁) * S₁ + C α₁)).natDegree = m + 3 := by
    rw [hXm.natDegree_mul hA₁m, hXd, hA₁d]
    omega
  have hlt : ((H₂ + C β₂) * S₂ + C α₀).degree
      < ((X + C β₀) * ((H₂ + C β₁) * S₁ + C α₁)).degree := by
    rw [degree_eq_natDegree hA₂m.ne_zero, degree_eq_natDegree hheadm.ne_zero,
      hA₂d, hheadd]
    exact_mod_cast (by omega : m + 2 < m + 3)
  refine ⟨hheadm.add_of_left hlt, ?_⟩
  have := degree_add_eq_left_of_degree_lt hlt
  exact natDegree_eq_of_degree_eq_some
    (by rw [this, degree_eq_natDegree hheadm.ne_zero, hheadd])
/-- One fill step: monicity and degree. -/
theorem fillStep_monic {H q qh S₁ S₂ : A[X]} {b ah : A} {n h : ℕ}
    (hH : H.Monic) (hdH : H.natDegree = h) (h1 : 1 ≤ h)
    (hq : q.natDegree < h) (hqh : qh.natDegree < h)
    (hS₁ : S₁.Monic) (hd₁ : S₁.natDegree = n) (hS₂ : S₂.Monic) (hd₂ : S₂.natDegree = n) :
    (((H + q) * S₁ + qh).Monic ∧ ((H + q) * S₁ + qh).natDegree = n + h) ∧
    (((H + C b) * S₂ + C ah).Monic ∧ ((H + C b) * S₂ + C ah).natDegree = n + h) := by
  have hone : ∀ (p e : A[X]), p.Monic → p.natDegree = h → e.natDegree < h →
      ∀ (T : A[X]), T.Monic → T.natDegree = n →
      (((p + e) * T).Monic ∧ ((p + e) * T).natDegree = n + h) := by
    intro p e hp hdp he T hT hdT
    have hdeg : e.degree < p.degree := by
      rcases eq_or_ne e 0 with rfl | hne
      · rw [degree_zero, degree_eq_natDegree hp.ne_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree hne, degree_eq_natDegree hp.ne_zero, hdp]
        exact_mod_cast he
    have hm : (p + e).Monic := hp.add_of_left hdeg
    have hd : (p + e).natDegree = h := by
      have hde := degree_add_eq_left_of_degree_lt hdeg
      exact natDegree_eq_of_degree_eq_some
        (by rw [hde, degree_eq_natDegree hp.ne_zero, hdp])
    exact ⟨hm.mul hT, by rw [hm.natDegree_mul hT, hd, hdT]; omega⟩
  have haddlow : ∀ (P e : A[X]), P.Monic → P.natDegree = n + h → e.natDegree < h →
      (P + e).Monic ∧ (P + e).natDegree = n + h := by
    intro P e hP hdP he
    have hdeg : e.degree < P.degree := by
      rcases eq_or_ne e 0 with rfl | hne
      · rw [degree_zero, degree_eq_natDegree hP.ne_zero]
        exact WithBot.bot_lt_coe _
      · rw [degree_eq_natDegree hne, degree_eq_natDegree hP.ne_zero, hdP]
        exact_mod_cast (by omega : e.natDegree < n + h)
    refine ⟨hP.add_of_left hdeg, ?_⟩
    have hde := degree_add_eq_left_of_degree_lt hdeg
    exact natDegree_eq_of_degree_eq_some
      (by rw [hde, degree_eq_natDegree hP.ne_zero, hdP])
  obtain ⟨hm₁, hd₁'⟩ := hone H q hH hdH hq S₁ hS₁ hd₁
  obtain ⟨hm₂, hd₂'⟩ := hone H (C b) hH hdH
    (by rw [natDegree_C]; omega) S₂ hS₂ hd₂
  refine ⟨haddlow _ _ hm₁ hd₁' (by omega), haddlow _ _ hm₂ hd₂' ?_⟩
  rw [natDegree_C]; omega

/-- The fill chain: monicity and degree, with only structural per-level data. -/
theorem fillChain_monic {H : ℕ → A[X]} {D : ℕ → FillData A} :
    ∀ l (S : A[X] × A[X]) (n : ℕ),
      S.1.Monic → S.1.natDegree = n → S.2.Monic → S.2.natDegree = n →
      (∀ i, 2 ≤ i → i ≤ l → (H i).Monic ∧ (H i).natDegree = 2 ^ i ∧
        (D i).q.natDegree < 2 ^ i ∧ (D i).qh.natDegree < 2 ^ i) →
      ((fillChain H D l S).1.Monic ∧
        (fillChain H D l S).1.natDegree = n + (2 ^ (l + 1) - 4)) ∧
      ((fillChain H D l S).2.Monic ∧
        (fillChain H D l S).2.natDegree = n + (2 ^ (l + 1) - 4)) := by
  intro l
  induction l with
  | zero =>
    intro S n h1 h2 h3 h4 _
    refine ⟨⟨h1, ?_⟩, ⟨h3, ?_⟩⟩
    · show S.1.natDegree = n + (2 ^ (0 + 1) - 4)
      rw [h2]; norm_num
    · show S.2.natDegree = n + (2 ^ (0 + 1) - 4)
      rw [h4]; norm_num
  | succ l ih =>
    intro S n hm₁ hd₁ hm₂ hd₂ hgood
    rcases Nat.lt_or_ge l 1 with hl1 | hl1
    · have : l = 0 := by omega
      subst this
      refine ⟨⟨hm₁, ?_⟩, ⟨hm₂, ?_⟩⟩
      · show S.1.natDegree = n + (2 ^ (0 + 1 + 1) - 4)
        rw [hd₁]; norm_num
      · show S.2.natDegree = n + (2 ^ (0 + 1 + 1) - 4)
        rw [hd₂]; norm_num
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      obtain ⟨hHm, hHd, hqd, hqhd⟩ := hgood (l' + 2) (by omega) le_rfl
      obtain ⟨⟨hs₁m, hs₁d⟩, ⟨hs₂m, hs₂d⟩⟩ := fillStep_monic (b := (D (l' + 2)).b)
        (ah := (D (l' + 2)).ah) hHm hHd (Nat.one_le_pow _ _ (by omega)) hqd hqhd
        hm₁ hd₁ hm₂ hd₂
      have hch := ih (fillStep (H (l' + 2)) (D (l' + 2)) S) (n + 2 ^ (l' + 2))
        hs₁m hs₁d hs₂m hs₂d (fun i h2 hi => hgood i h2 (by omega))
      obtain ⟨⟨hc₁m, hc₁d⟩, ⟨hc₂m, hc₂d⟩⟩ := hch
      have h4 : (4:ℕ) ≤ 2 ^ (l' + 2) := by
        calc (4:ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (l' + 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h5 : (2:ℕ) ^ (l' + 1 + 1 + 1) = 2 ^ (l' + 2) + 2 ^ (l' + 2) := by ring
      have h6 : (2:ℕ) ^ (l' + 1 + 1) = 2 ^ (l' + 2) := by ring
      refine ⟨⟨hc₁m, ?_⟩, ⟨hc₂m, ?_⟩⟩
      · rw [show fillChain H D (l' + 2) S
            = fillChain H D (l' + 1) (fillStep (H (l' + 2)) (D (l' + 2)) S) from rfl,
          hc₁d]
        omega
      · rw [show fillChain H D (l' + 2) S
            = fillChain H D (l' + 1) (fillStep (H (l' + 2)) (D (l' + 2)) S) from rfl,
          hc₂d]
        omega

omit [Nontrivial A] in
/-- Provenance of the fill chain: all output coefficients lie in any subalgebra
containing the level data and the input coefficients. -/
theorem fillChain_coeff_mem {V : Subalgebra R A} (H : ℕ → A[X]) (D : ℕ → FillData A) :
    ∀ l (S : A[X] × A[X]),
      (∀ i, 2 ≤ i → i ≤ l → (∀ j, (H i).coeff j ∈ V) ∧ (∀ j, (D i).q.coeff j ∈ V) ∧
        (D i).b ∈ V ∧ (∀ j, (D i).qh.coeff j ∈ V) ∧ (D i).ah ∈ V) →
      (∀ j, S.1.coeff j ∈ V) → (∀ j, S.2.coeff j ∈ V) →
      (∀ j, (fillChain H D l S).1.coeff j ∈ V) ∧
      (∀ j, (fillChain H D l S).2.coeff j ∈ V) := by
  intro l
  induction l with
  | zero => intro S _ h1 h2; exact ⟨h1, h2⟩
  | succ l ih =>
    intro S hlev h1 h2
    rcases Nat.lt_or_ge l 1 with hl1 | hl1
    · have hl0 : l = 0 := by omega
      subst hl0
      exact ⟨h1, h2⟩
    · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
      obtain ⟨hHV, hqV, hbV, hqhV, hahV⟩ := hlev (l' + 2) (by omega) le_rfl
      have hs1 : ∀ j, ((H (l' + 2) + (D (l' + 2)).q) * S.1 + (D (l' + 2)).qh).coeff j ∈ V := by
        intro j
        rw [coeff_add]
        refine Subalgebra.add_mem _ ?_ (hqhV j)
        refine coeff_mul_mem V (fun j' => ?_) h1 j
        rw [coeff_add]
        exact Subalgebra.add_mem _ (hHV j') (hqV j')
      have hs2 : ∀ j, ((H (l' + 2) + C (D (l' + 2)).b) * S.2 + C (D (l' + 2)).ah).coeff j ∈ V := by
        intro j
        rw [coeff_add, coeff_C]
        refine Subalgebra.add_mem _ ?_ ?_
        · refine coeff_mul_mem V (fun j' => ?_) h2 j
          rw [coeff_add, coeff_C]
          refine Subalgebra.add_mem _ (hHV j') ?_
          split
          · exact hbV
          · exact Subalgebra.zero_mem _
        · split
          · exact hahV
          · exact Subalgebra.zero_mem _
      exact ih (fillStep (H (l' + 2)) (D (l' + 2)) S)
        (fun i hi2 hil => hlev i hi2 (by omega)) hs1 hs2
