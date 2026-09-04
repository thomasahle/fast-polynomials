import FastPoly.Section6.GadgetDecoders

/-!
# The `𝒬_d` dispatch (`lem:odd-gadgets-H2H4`)

For every odd `d`, a monic degree-`d` gadget with a fresh block of exactly `d`
parameters, decodable from its own coefficients and the two recorded powers
`(H₂, H₄)`.  The residue classes: `d ∈ {1,3,7}` explicit/Mersenne bases,
`d ≡ 1 (mod 4)` the `Q_{4k+1}` crown gadget, `d ≡ 3 (mod 8)` the known-powers
construction at `l = 2`, and `d ≡ 7 (mod 8)`, `d ≥ 15` the barred construction —
the latter realized by the sealed `lem:barQ8k+7` circuits
(`barredGadgets_of_admissible`); the `BarredGadgets` interface below remains as
the algebraic existence form.
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [Nontrivial A]

/-- **The barred-gadget interface** (`lem:barQ8k+7`/`lem:barQ15`): for every
degree `8m+7 ≤ cap`, a monic gadget of that degree decodable from its own coefficients
and the two powers. -/
def BarredGadgets (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (cap : ℕ) : Prop :=
  ∀ H₂ H₄ : A[X], H₂.Monic → H₂.natDegree = 2 → H₄.Monic → H₄.natDegree = 4 →
    ∀ m : ℕ, 1 ≤ m → 8 * m + 7 ≤ cap → ∀ θ : ℕ → A,
    ∃ Q : A[X], Q.Monic ∧ Q.natDegree = 8 * m + 7 ∧
      ∀ V : Subalgebra R A, (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
        (∀ j, Q.coeff j ∈ V) → ∀ t, t < 8 * m + 7 → θ t ∈ V

theorem BarredGadgets.mono {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {cap cap' : ℕ} (h : BarredGadgets (R := R) (A := A) cap) (hle : cap' ≤ cap) :
    BarredGadgets (R := R) (A := A) cap' :=
  fun H₂ H₄ h2m h2d h4m h4d m hm1 hmc θ =>
    h H₂ H₄ h2m h2d h4m h4d m hm1 (by omega) θ

section knownGadget

variable {H₂ H₄ : A[X]}

/-- The two-level power family `(H₂, H₄)`. -/
noncomputable def knownTower (H₂ H₄ : A[X]) : ℕ → A[X] :=
  fun i => if i = 1 then H₂ else H₄

/-- **The known-powers `𝒬_{8m+3}` gadget** over `(H₂, H₄)`: the `l = 2` instance of
`alg:constr-known-2n-1` with the fresh block `θ 0, …, θ (8m+2)`. -/
noncomputable def knownGadget (H₂ H₄ : A[X]) (m : ℕ) (θ : ℕ → A) : A[X] :=
  (X + C (θ 0)) * ((knownTower H₂ H₄ 1 + C (θ 1))
      * (fillChain (knownTower H₂ H₄) (fun _ => ⟨0, 0, 0, 0⟩) (2 - 1)
          (Tpair (Function.update (knownTower H₂ H₄) 2
              (knownTower H₂ H₄ 2 + peel (knownTower H₂ H₄) (2 - 1)
                (fun t => θ (5 + t))))
            (knownTower H₂ H₄ 2 + peel (knownTower H₂ H₄) (2 - 1)
              (fun t => θ (5 + t)) + C (θ 6)) (2 * m) 2
            (fun t => θ (7 + t)))).1 + C (θ 4))
    + ((knownTower H₂ H₄ 1 + C (θ 2))
        * (fillChain (knownTower H₂ H₄) (fun _ => ⟨0, 0, 0, 0⟩) (2 - 1)
            (Tpair (Function.update (knownTower H₂ H₄) 2
                (knownTower H₂ H₄ 2 + peel (knownTower H₂ H₄) (2 - 1)
                  (fun t => θ (5 + t))))
              (knownTower H₂ H₄ 2 + peel (knownTower H₂ H₄) (2 - 1)
                (fun t => θ (5 + t)) + C (θ 6)) (2 * m) 2
              (fun t => θ (7 + t)))).2 + C (θ 3))

/-- The known-powers gadget is monic of degree `8m+3`. -/
theorem knownGadget_good (hH2m : H₂.Monic) (hH2d : H₂.natDegree = 2)
    (hH4m : H₄.Monic) (hH4d : H₄.natDegree = 4) (hm1 : 1 ≤ m) (θ : ℕ → A) :
    (knownGadget H₂ H₄ m θ).Monic
    ∧ (knownGadget H₂ H₄ m θ).natDegree = 8 * m + 3 := by
  set Hp : ℕ → A[X] := knownTower H₂ H₄ with hHpdef
  have hHp1 : Hp 1 = H₂ := if_pos rfl
  have hHp2 : Hp 2 = H₄ := if_neg (by omega)
  set D0 : ℕ → FillData A := fun _ => ⟨0, 0, 0, 0⟩ with hD0
  set β' : ℕ → A := fun t => θ (5 + t) with hβ'
  set αs : ℕ → A := fun t => θ (7 + t) with hαs
  set Tp := Tpair (Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β'))
    (Hp 2 + peel Hp (2 - 1) β' + C (θ 6)) (2 * m) 2 αs with hTp
  set Q : A[X] := (X + C (θ 0)) * ((Hp 1 + C (θ 1))
      * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4))
    + ((Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)) with hQ
  have hfc : ∀ S : A[X] × A[X], fillChain Hp D0 (2 - 1) S = S := fun S => rfl
  -- Mersenne level-1 facts
  obtain ⟨hMm, hMd⟩ := peel_monic Hp 1 (fun i h1 hi => absurd h1 (by omega))
    (by omega) β'
  -- the updated tower
  have htwm : ∀ i, 1 ≤ i → i ≤ 2 →
      ((Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β')) i).Monic ∧
      ((Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β')) i).natDegree = 2 ^ i := by
    intro i h1 hi
    rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
    · have hne : (1 : ℕ) ≠ 2 := by omega
      rw [update_ne _ hne]
      rw [hHp1]
      exact ⟨hH2m, by rw [hH2d]; norm_num⟩
    · have hupd : (Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β')) 2
          = Hp 2 + peel Hp (2 - 1) β' := by
        rw [update_last]
      rw [hupd, hHp2]
      obtain ⟨hm', hd'⟩ := monic_add_low (e := peel Hp (2 - 1) β') hH4m
        (Or.inr (by rw [hMd, hH4d]; norm_num))
      exact ⟨hm', by rw [hd', hH4d]; norm_num⟩
  have hHtm : (Hp 2 + peel Hp (2 - 1) β' + C (θ 6)).Monic ∧
      (Hp 2 + peel Hp (2 - 1) β' + C (θ 6)).natDegree = 2 ^ 2 := by
    obtain ⟨hm', hd'⟩ := monic_add_low (e := peel Hp (2 - 1) β') hH4m
      (Or.inr (by rw [hMd, hH4d]; norm_num))
    rw [hHp2]
    obtain ⟨hm'', hd''⟩ := monic_add_C hm' (by rw [hd', hH4d]; omega) (θ 6)
    exact ⟨hm'', by rw [hd'', hd', hH4d]; norm_num⟩
  -- pair degrees
  obtain ⟨⟨hT1m, hT1d⟩, hT2m, hT2d⟩ := Tpair_good
    (Hp := Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β'))
    (Ht := Hp 2 + peel Hp (2 - 1) β' + C (θ 6)) (k := 2 * m) (l := 2) (α := αs)
    (by omega) (by omega) (fun _ _ => by omega) htwm hHtm.1 hHtm.2
  -- outer degrees
  have hfacm : (Hp 1 + C (θ 1)).Monic ∧ (Hp 1 + C (θ 1)).natDegree = 2 := by
    rw [hHp1]
    obtain ⟨hm', hd'⟩ := monic_add_C hH2m (by omega) (θ 1)
    exact ⟨hm', by rw [hd', hH2d]⟩
  have hfacm2 : (Hp 1 + C (θ 2)).Monic ∧ (Hp 1 + C (θ 2)).natDegree = 2 := by
    rw [hHp1]
    obtain ⟨hm', hd'⟩ := monic_add_C hH2m (by omega) (θ 2)
    exact ⟨hm', by rw [hd', hH2d]⟩
  have hin1 : ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4)).Monic ∧
      ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4)).natDegree
        = 2 * m * 2 ^ 2 + 2 := by
    rw [hfc]
    have hpm : ((Hp 1 + C (θ 1)) * Tp.1).Monic := hfacm.1.mul hT1m
    have hpd : ((Hp 1 + C (θ 1)) * Tp.1).natDegree = 2 * m * 2 ^ 2 + 2 := by
      rw [hfacm.1.natDegree_mul hT1m, hfacm.2, hT1d]
      omega
    obtain ⟨hm', hd'⟩ := monic_add_C hpm (by rw [hpd]; positivity) (θ 4)
    exact ⟨hm', by rw [hd', hpd]⟩
  have hin2 : ((Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)).Monic ∧
      ((Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)).natDegree
        = 2 * m * 2 ^ 2 + 2 := by
    rw [hfc]
    have hpm : ((Hp 1 + C (θ 2)) * Tp.2).Monic := hfacm2.1.mul hT2m
    have hpd : ((Hp 1 + C (θ 2)) * Tp.2).natDegree = 2 * m * 2 ^ 2 + 2 := by
      rw [hfacm2.1.natDegree_mul hT2m, hfacm2.2, hT2d]
      omega
    obtain ⟨hm', hd'⟩ := monic_add_C hpm (by rw [hpd]; positivity) (θ 3)
    exact ⟨hm', by rw [hd', hpd]⟩
  have hXm : ((X + C (θ 0))
      * ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4))).Monic :=
    (monic_X_add_C _).mul hin1.1
  have hXd : ((X + C (θ 0))
      * ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4))).natDegree
      = 2 * m * 2 ^ 2 + 3 := by
    rw [(monic_X_add_C _).natDegree_mul hin1.1, natDegree_X_add_C, hin1.2]
    omega
  have hQm : Q.Monic ∧ Q.natDegree = 8 * m + 3 := by
    rw [hQ]
    obtain ⟨hm', hd'⟩ := monic_add_low
      (e := (Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)) hXm
      (Or.inr (by rw [hin2.2, hXd]; omega))
    refine ⟨hm', by rw [hd', hXd]; omega⟩
  rw [show knownGadget H₂ H₄ m θ = Q from by rw [hQ]; rfl]
  exact hQm

/-- The known-powers gadget decodes its full parameter block from its coefficients
and the two powers. -/
theorem knownGadget_decodable (hm1 : 1 ≤ m)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * m → IsUnit (((n : ℕ) : ℤ) : R))
    (hH2m : H₂.Monic) (hH2d : H₂.natDegree = 2)
    (hH4m : H₄.Monic) (hH4d : H₄.natDegree = 4) (θ : ℕ → A)
    (V : Subalgebra R A) (hH2V : ∀ j, H₂.coeff j ∈ V) (hH4V : ∀ j, H₄.coeff j ∈ V)
    (hQV : ∀ j, (knownGadget H₂ H₄ m θ).coeff j ∈ V) :
    ∀ t, t < 8 * m + 3 → θ t ∈ V := by
  set Hp : ℕ → A[X] := knownTower H₂ H₄ with hHpdef
  have hHp1 : Hp 1 = H₂ := if_pos rfl
  have hHp2 : Hp 2 = H₄ := if_neg (by omega)
  set D0 : ℕ → FillData A := fun _ => ⟨0, 0, 0, 0⟩ with hD0
  set β' : ℕ → A := fun t => θ (5 + t) with hβ'
  set αs : ℕ → A := fun t => θ (7 + t) with hαs
  set Tp := Tpair (Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β'))
    (Hp 2 + peel Hp (2 - 1) β' + C (θ 6)) (2 * m) 2 αs with hTp
  set Q : A[X] := (X + C (θ 0)) * ((Hp 1 + C (θ 1))
      * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4))
    + ((Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)) with hQ
  have hfc : ∀ S : A[X] × A[X], fillChain Hp D0 (2 - 1) S = S := fun S => rfl
  -- Mersenne level-1 facts
  obtain ⟨hMm, hMd⟩ := peel_monic Hp 1 (fun i h1 hi => absurd h1 (by omega))
    (by omega) β'
  -- the updated tower
  have htwm : ∀ i, 1 ≤ i → i ≤ 2 →
      ((Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β')) i).Monic ∧
      ((Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β')) i).natDegree = 2 ^ i := by
    intro i h1 hi
    rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
    · have hne : (1 : ℕ) ≠ 2 := by omega
      rw [update_ne _ hne]
      rw [hHp1]
      exact ⟨hH2m, by rw [hH2d]; norm_num⟩
    · have hupd : (Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β')) 2
          = Hp 2 + peel Hp (2 - 1) β' := by
        rw [update_last]
      rw [hupd, hHp2]
      obtain ⟨hm', hd'⟩ := monic_add_low (e := peel Hp (2 - 1) β') hH4m
        (Or.inr (by rw [hMd, hH4d]; norm_num))
      exact ⟨hm', by rw [hd', hH4d]; norm_num⟩
  have hHtm : (Hp 2 + peel Hp (2 - 1) β' + C (θ 6)).Monic ∧
      (Hp 2 + peel Hp (2 - 1) β' + C (θ 6)).natDegree = 2 ^ 2 := by
    obtain ⟨hm', hd'⟩ := monic_add_low (e := peel Hp (2 - 1) β') hH4m
      (Or.inr (by rw [hMd, hH4d]; norm_num))
    rw [hHp2]
    obtain ⟨hm'', hd''⟩ := monic_add_C hm' (by rw [hd', hH4d]; omega) (θ 6)
    exact ⟨hm'', by rw [hd'', hd', hH4d]; norm_num⟩
  -- pair degrees
  obtain ⟨⟨hT1m, hT1d⟩, hT2m, hT2d⟩ := Tpair_good
    (Hp := Function.update Hp 2 (Hp 2 + peel Hp (2 - 1) β'))
    (Ht := Hp 2 + peel Hp (2 - 1) β' + C (θ 6)) (k := 2 * m) (l := 2) (α := αs)
    (by omega) (by omega) (fun _ _ => by omega) htwm hHtm.1 hHtm.2
  -- outer degrees
  have hfacm : (Hp 1 + C (θ 1)).Monic ∧ (Hp 1 + C (θ 1)).natDegree = 2 := by
    rw [hHp1]
    obtain ⟨hm', hd'⟩ := monic_add_C hH2m (by omega) (θ 1)
    exact ⟨hm', by rw [hd', hH2d]⟩
  have hfacm2 : (Hp 1 + C (θ 2)).Monic ∧ (Hp 1 + C (θ 2)).natDegree = 2 := by
    rw [hHp1]
    obtain ⟨hm', hd'⟩ := monic_add_C hH2m (by omega) (θ 2)
    exact ⟨hm', by rw [hd', hH2d]⟩
  have hin1 : ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4)).Monic ∧
      ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4)).natDegree
        = 2 * m * 2 ^ 2 + 2 := by
    rw [hfc]
    have hpm : ((Hp 1 + C (θ 1)) * Tp.1).Monic := hfacm.1.mul hT1m
    have hpd : ((Hp 1 + C (θ 1)) * Tp.1).natDegree = 2 * m * 2 ^ 2 + 2 := by
      rw [hfacm.1.natDegree_mul hT1m, hfacm.2, hT1d]
      omega
    obtain ⟨hm', hd'⟩ := monic_add_C hpm (by rw [hpd]; positivity) (θ 4)
    exact ⟨hm', by rw [hd', hpd]⟩
  have hin2 : ((Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)).Monic ∧
      ((Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)).natDegree
        = 2 * m * 2 ^ 2 + 2 := by
    rw [hfc]
    have hpm : ((Hp 1 + C (θ 2)) * Tp.2).Monic := hfacm2.1.mul hT2m
    have hpd : ((Hp 1 + C (θ 2)) * Tp.2).natDegree = 2 * m * 2 ^ 2 + 2 := by
      rw [hfacm2.1.natDegree_mul hT2m, hfacm2.2, hT2d]
      omega
    obtain ⟨hm', hd'⟩ := monic_add_C hpm (by rw [hpd]; positivity) (θ 3)
    exact ⟨hm', by rw [hd', hpd]⟩
  have hXm : ((X + C (θ 0))
      * ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4))).Monic :=
    (monic_X_add_C _).mul hin1.1
  have hXd : ((X + C (θ 0))
      * ((Hp 1 + C (θ 1)) * (fillChain Hp D0 (2 - 1) Tp).1 + C (θ 4))).natDegree
      = 2 * m * 2 ^ 2 + 3 := by
    rw [(monic_X_add_C _).natDegree_mul hin1.1, natDegree_X_add_C, hin1.2]
    omega
  have hQm : Q.Monic ∧ Q.natDegree = 8 * m + 3 := by
    rw [hQ]
    obtain ⟨hm', hd'⟩ := monic_add_low
      (e := (Hp 1 + C (θ 2)) * (fillChain Hp D0 (2 - 1) Tp).2 + C (θ 3)) hXm
      (Or.inr (by rw [hin2.2, hXd]; omega))
    refine ⟨hm', by rw [hd', hXd]; omega⟩
  have hQV' : ∀ j, Q.coeff j ∈ V := by
    rw [show Q = knownGadget H₂ H₄ m θ from by rw [hQ]; rfl]
    exact hQV
  intro t ht
  have hH2V' : ∀ j, (Hp 1).coeff j ∈ V := by rw [hHp1]; exact hH2V
  have htowerV : ∀ i, 1 ≤ i → i ≤ 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i ∧
      (∀ j, (Hp i).coeff j ∈ V) := by
    intro i h1 hi
    rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
    · rw [hHp1]; exact ⟨hH2m, by rw [hH2d]; norm_num, hH2V⟩
    · rw [hHp2]; exact ⟨hH4m, by rw [hH4d]; norm_num, hH4V⟩
  obtain ⟨hβ₀, hβ₁, hβ₂, hα₀, hα₁, -, hβb, hδ, hαb⟩ :=
    q_odd_degree_decodable' (K := V) (k := m) (l := 2) (β' := β') (δ := θ 6)
      (α := αs) (D := D0) (Wh := fun _ => ∅) hm1 le_rfl htowerV
      (fun n h1 h2' => hadm n h1 (by omega))
      (fun i h2' h1' => absurd (le_trans h2' h1') (by omega))
      (hP := hQ) V le_rfl hQV'
  rcases Nat.lt_or_ge t 5 with h5' | h5'
  · rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 from by omega)
      with rfl | rfl | rfl | rfl | rfl
    · exact hβ₀
    · exact hβ₁
    · exact hβ₂
    · exact hα₀
    · exact hα₁
  · rcases Nat.lt_or_ge t 6 with h6' | h6'
    · rw [show t = 5 from by omega]
      exact hβb 0 (by norm_num)
    · rcases Nat.lt_or_ge t 7 with h7' | h7'
      · rw [show t = 6 from by omega]
        exact hδ
      · have h := hαb (t - 7) (by
          simp only [show (2:ℕ) ^ 2 = 4 from by norm_num]
          omega)
        have he : 7 + (t - 7) = t := by omega
        rw [hαs] at h
        simp only at h
        rwa [he] at h

end knownGadget

/-- **`lem:odd-gadgets-H2H4` (the `𝒬_d` dispatch)**: for every odd `d`, a monic degree-`d`
gadget with a fresh block of exactly `d` parameters, decodable from its coefficients and
the two powers.  The `d ≡ 7 (mod 8)`, `d ≥ 15` branch is delegated to the barred-gadget
interface. -/
theorem odd_gadget_dispatch (d : ℕ) (hd : d % 2 = 1)
    (hadm : ∀ n : ℕ, 1 ≤ n → n ≤ d → IsUnit (((n : ℕ) : ℤ) : R))
    {H₂ H₄ : A[X]} (hH2m : H₂.Monic) (hH2d : H₂.natDegree = 2)
    (hH4m : H₄.Monic) (hH4d : H₄.natDegree = 4)
    (hbar : BarredGadgets (R := R) (A := A) d)
    (θ : ℕ → A) :
    ∃ Q : A[X], Q.Monic ∧ Q.natDegree = d ∧
      ∀ V : Subalgebra R A, (∀ j, H₂.coeff j ∈ V) → (∀ j, H₄.coeff j ∈ V) →
        (∀ j, Q.coeff j ∈ V) → ∀ t, t < d → θ t ∈ V := by
  classical
  set Hp : ℕ → A[X] := fun i => if i = 1 then H₂ else H₄ with hHp
  have hHp1 : Hp 1 = H₂ := if_pos rfl
  have hHp2 : Hp 2 = H₄ := if_neg (by omega)
  rcases (show d = 1 ∨ d = 3 ∨ d = 7 ∨ (d % 4 = 1 ∧ 5 ≤ d) ∨ (d % 8 = 3 ∧ 11 ≤ d)
      ∨ (d % 8 = 7 ∧ 15 ≤ d) from by omega)
    with rfl | rfl | rfl | ⟨h4, h5⟩ | ⟨h8, h11⟩ | ⟨h8, h15⟩
  -- `d = 1`: the affine gadget
  · refine ⟨X + C (θ 0), monic_X_add_C _, natDegree_X_add_C _, ?_⟩
    intro V _ _ hQV t ht
    have h0 : (X + C (θ 0)).coeff 0 = θ 0 := by
      rw [coeff_add, coeff_X_zero, coeff_C, if_pos rfl, zero_add]
    have := hQV 0
    rw [h0] at this
    rwa [show t = 0 from by omega]
  -- `d = 3`: the Mersenne gadget at level 2
  · have htw : ∀ i, 1 ≤ i → i < 2 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i := by
      intro i h1 hi
      rw [show i = 1 from by omega, hHp1]
      exact ⟨hH2m, by rw [hH2d]; norm_num⟩
    obtain ⟨hQm, hQd⟩ := peel_monic Hp 2 htw (by omega) θ
    refine ⟨peel Hp 2 θ, hQm, by rw [hQd]; norm_num, ?_⟩
    intro V hH2V _ hQV t ht
    refine peel_correct (K := V) Hp 2 ?_ (by omega) θ V le_rfl hQV t (by omega)
    intro i h1 hi
    rw [show i = 1 from by omega, hHp1]
    exact ⟨hH2m, by rw [hH2d]; norm_num, hH2V⟩
  -- `d = 7`: the Mersenne gadget at level 3
  · have htw : ∀ i, 1 ≤ i → i < 3 → (Hp i).Monic ∧ (Hp i).natDegree = 2 ^ i := by
      intro i h1 hi
      rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
      · rw [hHp1]; exact ⟨hH2m, by rw [hH2d]; norm_num⟩
      · rw [hHp2]; exact ⟨hH4m, by rw [hH4d]; norm_num⟩
    obtain ⟨hQm, hQd⟩ := peel_monic Hp 3 htw (by omega) θ
    refine ⟨peel Hp 3 θ, hQm, by rw [hQd]; norm_num, ?_⟩
    intro V hH2V hH4V hQV t ht
    refine peel_correct (K := V) Hp 3 ?_ (by omega) θ V le_rfl hQV t (by omega)
    intro i h1 hi
    rcases (show i = 1 ∨ i = 2 from by omega) with rfl | rfl
    · rw [hHp1]; exact ⟨hH2m, by rw [hH2d]; norm_num, hH2V⟩
    · rw [hHp2]; exact ⟨hH4m, by rw [hH4d]; norm_num, hH4V⟩
  -- `d ≡ 1 (mod 4)`, `d ≥ 5`: the `Q_{4k+1}` crown gadget
  · obtain ⟨m, hm1, rfl⟩ : ∃ m, 1 ≤ m ∧ d = 4 * m + 1 := ⟨d / 4, by omega⟩
    have hadm' : ∀ n : ℕ, 1 ≤ n → n ≤ 2 * m → IsUnit (((n : ℕ) : ℤ) : R) :=
      fun n h1 h2 => hadm n h1 (by omega)
    have h2 : IsUnit (2 : R) := isUnit_two_of_cast hadm (by omega)
    obtain ⟨hQm, hQd⟩ := q4k1_good (α := fun t => θ (5 + t)) hm1
      (θ 1) (θ 4) (θ 2) (θ 3) (θ 0)
    refine ⟨q4k1 H₂ (θ 1) (θ 4) (θ 2) (θ 3) (θ 0) m (fun t => θ (5 + t)),
      hQm, hQd, ?_⟩
    intro V hH2V _ hQV t ht
    obtain ⟨⟨hβ, hγ, ha, he, hρ⟩, -, hα⟩ :=
      q4k1_decodable (α := fun t => θ (5 + t)) hm1 hadm' h2 hH2m hH2d
        (θ 1) (θ 4) (θ 2) (θ 3) (θ 0) V hH2V hQV
    rcases Nat.lt_or_ge t 5 with h5' | h5'
    · rcases (show t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 from by omega)
        with rfl | rfl | rfl | rfl | rfl
      · exact hβ
      · exact hγ
      · exact ha
      · exact he
      · exact hρ
    · have h := hα (t - 5) (by omega)
      rwa [show 5 + (t - 5) = t from by omega] at h
  -- `d ≡ 3 (mod 8)`, `d ≥ 11`: the known-powers construction at `l = 2`
  · obtain ⟨m, hm1, rfl⟩ : ∃ m, 1 ≤ m ∧ d = 8 * m + 3 := ⟨d / 8, by omega⟩
    obtain ⟨hQm, hQd⟩ := knownGadget_good hH2m hH2d hH4m hH4d hm1 θ
    exact ⟨knownGadget H₂ H₄ m θ, hQm, hQd, fun V hH2V hH4V hQV =>
      knownGadget_decodable hm1 (fun n h1 h2' => hadm n h1 (by omega))
        hH2m hH2d hH4m hH4d θ V hH2V hH4V hQV⟩
  -- `d ≡ 7 (mod 8)`, `d ≥ 15`: the barred gadget
  · obtain ⟨m, hm1, rfl⟩ : ∃ m, 1 ≤ m ∧ d = 8 * m + 7 := ⟨d / 8, by omega⟩
    exact hbar H₂ H₄ hH2m hH2d hH4m hH4d m hm1 le_rfl θ

end FastPoly
