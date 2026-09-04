import FastPoly.Section5.Rk2lEven
import FastPoly.Section5.Rk2lOdd

/-!
# `lem:Rk2l`: the master degree induction

`Rk2l_deg`: for every `k ≥ 1` (over a good tower, at level `l ≥ 2`, with the
scalar-difference condition at the shared odd base), both remainder components have
degree at most `(k-1)·2^l`.  This is the sole datum threaded through the strong
induction; the boundary coefficients (`R-top-two`) then follow at every level by
instantiating `Rpair_even_top` / `Rpair_odd_top` / `Rpair_oddbase_top` with these
bounds — see `notes/rk2l_lean_design.md`.
-/

namespace FastPoly

open Polynomial Finset

variable {A : Type*} [CommRing A] [Nontrivial A]

/-- Band conversion of the even descent: `(k/2-1)·2^{l+1} = (k-2)·2^l`. -/
theorem even_band_conv {k l : ℕ} (hpar : k % 2 = 0) (hk : 2 ≤ k) :
    (k / 2 - 1) * 2 ^ (l + 1) = (k - 2) * 2 ^ l := by
  have hh : (k / 2 - 1) * 2 = k - 2 := by omega
  calc (k / 2 - 1) * 2 ^ (l + 1) = (k / 2 - 1) * 2 * 2 ^ l := by ring
  _ = (k - 2) * 2 ^ l := by rw [hh]

/-- Band conversion of the odd descent: `((k-1)/2-1)·2^{l+1} = (k-3)·2^l`. -/
theorem odd_band_conv {k l : ℕ} (hpar : k % 2 ≠ 0) (hk : 3 ≤ k) :
    ((k - 1) / 2 - 1) * 2 ^ (l + 1) = (k - 3) * 2 ^ l := by
  have hh : ((k - 1) / 2 - 1) * 2 = k - 3 := by omega
  calc ((k - 1) / 2 - 1) * 2 ^ (l + 1) = ((k - 1) / 2 - 1) * 2 * 2 ^ l := by ring
  _ = (k - 3) * 2 ^ l := by rw [hh]

/-- `odd_band_conv` at the shared odd base (`l = 2`). -/
theorem odd_band_conv_base {k : ℕ} (hpar : k % 2 ≠ 0) (hk : 3 ≤ k) :
    ((k - 1) / 2 - 1) * 2 ^ 3 = (k - 3) * 2 ^ 2 :=
  odd_band_conv (l := 2) hpar hk

/-- `odd_band_conv_base` in the `4·(k-3)` spelling. -/
theorem odd_band_conv_base' {k : ℕ} (hpar : k % 2 ≠ 0) (hk : 3 ≤ k) :
    ((k - 1) / 2 - 1) * 2 ^ 3 = 4 * (k - 3) := by
  calc ((k - 1) / 2 - 1) * 2 ^ 3 = (k - 3) * 2 ^ 2 := odd_band_conv_base hpar hk
  _ = 4 * (k - 3) := by ring

/-- **`lem:Rk2l`(2), bound form**: remainder degrees are at most `(k-1)·2^l`. -/
theorem Rk2l_deg :
    ∀ k, 1 ≤ k → ∀ l (Hp : ℕ → A[X]) (Ht : A[X]) (α : ℕ → A), 2 ≤ l →
      (∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i) →
      Ht.Monic → Ht.natDegree = 2 ^ l →
      (l = 2 → ¬ k % 2 = 0 → 3 ≤ k → ∃ ρ : A, Ht - Hp 2 = C ρ) →
      (Rpair Hp Ht k l α).1.natDegree ≤ (k - 1) * 2 ^ l ∧
      (Rpair Hp Ht k l α).2.natDegree ≤ (k - 1) * 2 ^ l := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk l Hp Ht α hl hHp hHt hdHt hsd
    rcases Nat.lt_or_ge k 2 with hk1 | hk2
    · have hkeq : k = 1 := by omega
      subst hkeq
      constructor
      · rw [Rpair_one]
        show (0 : A[X]).natDegree ≤ (1 - 1) * 2 ^ l
        rw [natDegree_zero]
        omega
      · rw [Rpair_one]
        show (0 : A[X]).natDegree ≤ (1 - 1) * 2 ^ l
        rw [natDegree_zero]
        omega
    · rcases eq_or_ne (k % 2) 0 with hpar | hpar
      · -- even step
        obtain ⟨hHm', hHd'⟩ := evenH_good (k := k) (α := α) hHp hl
        obtain ⟨hTm', hTd'⟩ := evenHt_good (k := k) (α := α) hHp hl hHt hdHt
        have hgood' := good_update (m := l) (H' := evenH Hp k l α) hHp hHm' hHd'
        have hinner := ih (k / 2) (by omega) (by omega) (l + 1)
          (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α) α
          (by omega) hgood' hTm' hTd' (fun h32 => absurd h32 (by omega))
        have hconv : (k / 2 - 1) * 2 ^ (l + 1) = (k - 2) * 2 ^ l :=
          even_band_conv hpar (by omega)
        obtain ⟨hi1, hi2⟩ := hinner
        rw [hconv] at hi1 hi2
        obtain ⟨⟨hd1, -, -⟩, ⟨hd2, -, -⟩⟩ := Rpair_even_top (k := k) (α := α) hHp hl hpar
          (by omega) hHt hdHt hi1 hi2
        exact ⟨hd1, hd2⟩
      · have hk3 : 3 ≤ k := by omega
        rcases Nat.lt_or_ge l 3 with hlb | hl3
        · -- shared odd base, l = 2
          have hleq : l = 2 := by omega
          subst hleq
          obtain ⟨h8m, h8d⟩ := obH8_good (k := k) (α := α)
            (hHp 1 (by omega) (by omega)) (hHp 2 (by omega) le_rfl)
          have hgood3 := good_update (m := 2) (H' := obH8 Hp k α) hHp h8m h8d
          obtain ⟨ht8m, ht8d⟩ := monic_add_low (e := C (α (4 * (k - 2)))) h8m
            (Or.inr (by rw [natDegree_C, h8d]; norm_num))
          have hinner := ih ((k - 1) / 2) (by omega) (by omega) 3
            (Function.update Hp 3 (obH8 Hp k α)) (obH8 Hp k α + C (α (4 * (k - 2))))
            (fun j => α (4 + j)) (by omega) hgood3 ht8m (ht8d.trans h8d)
            (fun h32 => absurd h32 (by omega))
          have hconv : ((k - 1) / 2 - 1) * 2 ^ 3 = (k - 3) * 2 ^ 2 :=
            odd_band_conv_base hpar (by omega)
          obtain ⟨hi1, hi2⟩ := hinner
          rw [hconv] at hi1 hi2
          obtain ⟨⟨hd1, -, -⟩, ⟨hd2, -, -⟩⟩ := Rpair_oddbase_top (k := k) (α := α) hHp
            hpar hk3 hHt hdHt (hsd rfl hpar hk3) hi1 hi2
          exact ⟨hd1, hd2⟩
        · -- odd main, l ≥ 3
          obtain ⟨hHm', hHd'⟩ := oddH_good (k := k) (α := α) hHp hl3
          obtain ⟨hTm', hTd'⟩ := oddHt_good (k := k) (α := α) hHp hl3 hHt hdHt
          have hgood' := good_update (m := l) (H' := oddH Hp k l α) hHp hHm' hHd'
          have hinner := ih ((k - 1) / 2) (by omega) (by omega) (l + 1)
            (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
            (fun j => α (2 ^ l + j)) (by omega) hgood' hTm' hTd'
            (fun h32 => absurd h32 (by omega))
          have hconv : ((k - 1) / 2 - 1) * 2 ^ (l + 1) = (k - 3) * 2 ^ l :=
            odd_band_conv hpar (by omega)
          obtain ⟨hi1, hi2⟩ := hinner
          rw [hconv] at hi1 hi2
          obtain ⟨⟨hd1, -, -⟩, ⟨hd2, -, -⟩⟩ := Rpair_odd_top (k := k) (α := α) hHp hl3
            hpar hk3 hHt hdHt hi1 hi2
          exact ⟨hd1, hd2⟩

/-- Packaged even descent: the updated tower is good and `Rk2l_deg` on it gives the
degree bounds already converted to the `(k-2)·2^l` band. -/
theorem Rk2l_deg_even {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}
    (hk : 2 ≤ k) (hpar : k % 2 = 0) (hl : 2 ≤ l)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) :
    (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
      (k / 2) (l + 1) α).1.natDegree ≤ (k - 2) * 2 ^ l ∧
    (Rpair (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α)
      (k / 2) (l + 1) α).2.natDegree ≤ (k - 2) * 2 ^ l := by
  obtain ⟨hHm', hHd'⟩ := evenH_good (k := k) (α := α) hHp hl
  obtain ⟨hTm', hTd'⟩ := evenHt_good (k := k) (α := α) hHp hl hHt hdHt
  have hgood' := good_update (m := l) (H' := evenH Hp k l α) hHp hHm' hHd'
  obtain ⟨hi1, hi2⟩ := Rk2l_deg (k / 2) (by omega) (l + 1)
    (Function.update Hp (l + 1) (evenH Hp k l α)) (evenHt Hp Ht k l α) α
    (by omega) hgood' hTm' hTd' (fun h32 => absurd h32 (by omega))
  rw [even_band_conv hpar hk] at hi1 hi2
  exact ⟨hi1, hi2⟩

/-- Packaged shared-odd-base descent (`l = 2`): the octic update is good and
`Rk2l_deg` on it gives the `(k-3)·2²` band bounds. -/
theorem Rk2l_deg_oddbase {Hp : ℕ → A[X]} {k : ℕ} {α : ℕ → A}
    (hk : 3 ≤ k) (hpar : k % 2 ≠ 0)
    (hHp : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i) :
    (Rpair (Function.update Hp 3 (obH8 Hp k α)) (obH8 Hp k α + C (α (4 * (k - 2))))
      ((k - 1) / 2) 3 (fun j => α (4 + j))).1.natDegree ≤ (k - 3) * 2 ^ 2 ∧
    (Rpair (Function.update Hp 3 (obH8 Hp k α)) (obH8 Hp k α + C (α (4 * (k - 2))))
      ((k - 1) / 2) 3 (fun j => α (4 + j))).2.natDegree ≤ (k - 3) * 2 ^ 2 := by
  obtain ⟨h8m, h8d⟩ := obH8_good (k := k) (α := α)
    (hHp 1 (by omega) (by omega)) (hHp 2 (by omega) le_rfl)
  have hgood3 := good_update (m := 2) (H' := obH8 Hp k α) hHp h8m h8d
  obtain ⟨ht8m, ht8d⟩ := monic_add_low (e := C (α (4 * (k - 2)))) h8m
    (Or.inr (by rw [natDegree_C, h8d]; norm_num))
  obtain ⟨hi1, hi2⟩ := Rk2l_deg ((k - 1) / 2) (by omega) 3
    (Function.update Hp 3 (obH8 Hp k α)) (obH8 Hp k α + C (α (4 * (k - 2))))
    (fun j => α (4 + j)) (by omega) hgood3 ht8m (ht8d.trans h8d)
    (fun h32 => absurd h32 (by omega))
  rw [odd_band_conv_base hpar hk] at hi1 hi2
  exact ⟨hi1, hi2⟩

/-- Packaged odd main descent (`l ≥ 3`): the odd update is good and `Rk2l_deg` on it
gives the `(k-3)·2^l` band bounds. -/
theorem Rk2l_deg_odd {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}
    (hk : 3 ≤ k) (hpar : k % 2 ≠ 0) (hl : 3 ≤ l)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l) :
    (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
      ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).1.natDegree
        ≤ (k - 3) * 2 ^ l ∧
    (Rpair (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
      ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j))).2.natDegree
        ≤ (k - 3) * 2 ^ l := by
  obtain ⟨hHm', hHd'⟩ := oddH_good (k := k) (α := α) hHp hl
  obtain ⟨hTm', hTd'⟩ := oddHt_good (k := k) (α := α) hHp hl hHt hdHt
  have hgood' := good_update (m := l) (H' := oddH Hp k l α) hHp hHm' hHd'
  obtain ⟨hi1, hi2⟩ := Rk2l_deg ((k - 1) / 2) (by omega) (l + 1)
    (Function.update Hp (l + 1) (oddH Hp k l α)) (oddHt Hp Ht k l α)
    (fun j => α (2 ^ l + j)) (by omega) hgood' hTm' hTd'
    (fun h32 => absurd h32 (by omega))
  rw [odd_band_conv hpar hk] at hi1 hi2
  exact ⟨hi1, hi2⟩

/-- The pivot-scale `γ_k` of `lem:Rk2l`: `k/2` for even `k`, `k(k-1)/2` for odd `k`. -/
def gammaZ (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 else k.choose 2

/-- **`lem:Rk2l`, leading-coefficient form** (`R-top-two`, first equation): for `k ≥ 2`
both remainder components have `[x^d]R⁽ⁱ⁾ = -γ_k` at `d = (k-1)·2^l`. -/
theorem Rk2l_lead (k : ℕ) (hk : 2 ≤ k) (l : ℕ) (Hp : ℕ → A[X]) (Ht : A[X]) (α : ℕ → A)
    (hl : 2 ≤ l)
    (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hHt : Ht.Monic) (hdHt : Ht.natDegree = 2 ^ l)
    (hsd : l = 2 → ¬ k % 2 = 0 → 3 ≤ k → ∃ ρ : A, Ht - Hp 2 = C ρ) :
    (Rpair Hp Ht k l α).1.coeff ((k - 1) * 2 ^ l) = -((gammaZ k : ℕ) : A) ∧
    (Rpair Hp Ht k l α).2.coeff ((k - 1) * 2 ^ l) = -((gammaZ k : ℕ) : A) := by
  rcases eq_or_ne (k % 2) 0 with hpar | hpar
  · -- even
    obtain ⟨hi1, hi2⟩ := Rk2l_deg_even (α := α) hk hpar hl hHp hHt hdHt
    obtain ⟨⟨-, hc1, -⟩, ⟨-, hc2, -⟩⟩ := Rpair_even_top (k := k) (α := α) hHp hl hpar
      hk hHt hdHt hi1 hi2
    have hγ : gammaZ k = k / 2 := by
      unfold gammaZ
      rw [if_pos hpar]
    rw [hγ]
    exact ⟨hc1, hc2⟩
  · have hk3 : 3 ≤ k := by omega
    have hγ : gammaZ k = k.choose 2 := by
      unfold gammaZ
      rw [if_neg hpar]
    rcases Nat.lt_or_ge l 3 with hlb | hl3
    · -- shared odd base, l = 2
      have hleq : l = 2 := by omega
      subst hleq
      obtain ⟨hi1, hi2⟩ := Rk2l_deg_oddbase (α := α) hk3 hpar hHp
      obtain ⟨⟨-, hc1, -⟩, ⟨-, hc2, -⟩⟩ := Rpair_oddbase_top (k := k) (α := α) hHp
        hpar hk3 hHt hdHt (hsd rfl hpar hk3) hi1 hi2
      rw [hγ]
      exact ⟨hc1, hc2⟩
    · -- odd main, l ≥ 3
      obtain ⟨hi1, hi2⟩ := Rk2l_deg_odd (α := α) hk3 hpar hl3 hHp hHt hdHt
      obtain ⟨⟨-, hc1, -⟩, ⟨-, hc2, -⟩⟩ := Rpair_odd_top (k := k) (α := α) hHp hl3
        hpar hk3 hHt hdHt hi1 hi2
      rw [hγ]
      exact ⟨hc1, hc2⟩

section sigma

variable {Hp : ℕ → A[X]} {Ht : A[X]} {k l : ℕ} {α : ℕ → A}

/-- `σ₁` is parameter-free: the top coefficient of `S⁽¹⁾₁` is the tower coefficient
plus the monic-fixed leading `1` of its `Q`-block. -/
theorem tS1_coeff_top (hHp : ∀ i, 1 ≤ i → i ≤ l → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i)
    (hl : 2 ≤ l) :
    (tS1 Hp k l α).coeff (2 ^ (l - 1) - 1)
      = (Hp (l - 1)).coeff (2 ^ (l - 1) - 1) + 1 := by
  obtain ⟨hqm, hqd⟩ := peel_monic Hp (l - 1)
    (fun i' h1' hik => hHp i' h1' (by omega)) (by omega)
    (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
  have hlead : (peel Hp (l - 1)
      (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))).coeff (2 ^ (l - 1) - 1) = 1 := by
    rw [← hqd]
    exact hqm.coeff_natDegree
  unfold tS1
  rw [coeff_add, hlead]

/-- `σ₂` is parameter-free: the scalar shift does not reach the top coefficient. -/
theorem tS1t_coeff_top (hl : 2 ≤ l) :
    (tS1t Hp k l α).coeff (2 ^ (l - 1) - 1)
      = (Hp (l - 1)).coeff (2 ^ (l - 1) - 1) := by
  have h2 : (2:ℕ) ≤ 2 ^ (l - 1) := by
    calc (2:ℕ) = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (l - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  unfold tS1t
  rw [coeff_add, coeff_C, if_neg (by omega), add_zero]

/-- Shared-base `σ₁`: `[x^1](H₂ + x + u) = [x^1]H₂ + 1`. -/
theorem obS1_coeff_one :
    (obS1 Hp k α).coeff 1 = (Hp 1).coeff 1 + 1 := by
  unfold obS1
  rw [coeff_add, coeff_add, coeff_X, coeff_C, if_pos rfl, if_neg (by omega)]
  ring

/-- Shared-base `σ₂`: the known scalar `ρ` does not reach `[x^1]`. -/
theorem obS1_sub_coeff_one (ρ : A) :
    (obS1 Hp k α - C ρ).coeff 1 = (obS1 Hp k α).coeff 1 := by
  rw [coeff_sub, coeff_C, if_neg (by omega), sub_zero]

end sigma

end FastPoly
