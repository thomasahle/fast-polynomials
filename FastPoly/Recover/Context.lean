import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Monic

/-!
# Known-data contexts and cutoff-visible coefficient algebras

This is the semantic layer of the formalization of `sections/constructions.tex`.

* `R` is the base ring of *scalars*.
* `A` is an `R`-algebra in which all polynomial coefficients live.  In the intended
  instantiation `A = R[α₀, …, α_{d-1}]` is a free polynomial algebra in the active
  parameters, which is what makes the statements below non-vacuous: a subalgebra generated
  by *known* data cannot secretly contain an active parameter.
* `K : Subalgebra R A` is the *known context*: auxiliary data (coefficients of the given
  powers) together with parameters that have already been recovered.

For a polynomial `Φ : A[X]`, a window `G : Finset ℕ` and a cutoff `t : ℕ`, the
*visible algebra* is

  `Vis R K Φ G t = K ⊔ Algebra.adjoin R {Φ.coeff i | i ∈ G, t ≤ i}`.

"`a` is recoverable from the coefficients of `Φ` of degree `≥ t` on `G` given `K`" is the
statement `a ∈ Vis R K Φ G t`.  Because `Vis` is a subalgebra, closure under ring
operations is automatic, and "derivable via" (`lem:extractable-via-derivable` in the paper)
is the transport lemma `Vis_le`.

The probabilistic reading: `Vis R K Φ G ·` is a filtration (decreasing in `t`), a
compatible pair is a (predictable, adapted) pair of coefficient sequences with respect to it.
-/

namespace FastPoly

/-! `Function.update` version-compat shims: Mathlib renamed
`update_same`/`update_noteq` to `update_self`/`update_of_ne`; absorb once. -/

theorem update_last {α : Sort*} [DecidableEq α] {β : α → Sort*}
    (f : ∀ a, β a) (n : α) (x : β n) : Function.update f n x n = x := by
  first
  | rw [Function.update_same]
  | rw [Function.update_self]

theorem update_ne {α : Sort*} [DecidableEq α] {β : α → Sort*}
    (f : ∀ a, β a) {m n : α} (h : m ≠ n) (x : β n) :
    Function.update f n x m = f m := by
  first
  | rw [Function.update_noteq h]
  | rw [Function.update_of_ne h]

/-! Descending-induction engines: the fuel-based scaffolding shared by the combination
engines (`vis_le_vis_add`, `vis_le_vis_mul`, `vis_le_vis_sq`, `x_alpha_mem`).  Pure
`ℕ`/`Finset` statements — no `Vis`. -/

/-- **Descending induction over a finite index set**: to prove `Q` everywhere on `U` it
suffices, at each `k ∈ U`, to derive `Q k` from `Q` at the strictly larger indices of `U`. -/
theorem descend_on_finset {U : Finset ℕ} {Q : ℕ → Prop}
    (step : ∀ k ∈ U, (∀ i ∈ U, k < i → Q i) → Q k) :
    ∀ k ∈ U, Q k := by
  set N := U.sup id + 1 with hN
  have hUbound : ∀ k ∈ U, k < N := by
    intro k hk
    have h := Finset.le_sup (f := id) hk
    simp only [id_eq] at h
    omega
  have main : ∀ fuel, ∀ k ∈ U, N - k ≤ fuel → Q k := by
    intro fuel
    induction fuel with
    | zero =>
      intro k hk hfuel
      exact absurd (hUbound k hk) (by omega)
    | succ fuel ih =>
      intro k hk _
      refine step k hk (fun i hi hki => ih i hi ?_)
      have := hUbound i hi
      omega
  exact fun k hk => main (N - k) k hk le_rfl

/-- **Bounded descending induction on `ℕ`**: if `Q` holds from `B` upward and each `j < B`
follows from `Q` at all strictly larger indices, then `Q` holds everywhere. -/
theorem descend_below {B : ℕ} {Q : ℕ → Prop} (htop : ∀ j, B ≤ j → Q j)
    (step : ∀ j, j < B → (∀ i, j < i → Q i) → Q j) : ∀ j, Q j := by
  have main : ∀ fuel j, B - j ≤ fuel → Q j := by
    intro fuel
    induction fuel with
    | zero =>
      intro j hj
      exact htop j (by omega)
    | succ fuel ih =>
      intro j hj
      rcases Nat.lt_or_ge j B with hjB | hjB
      · exact step j hjB (fun i hi => ih i (by omega))
      · exact htop j hjB
  exact fun j => main (B - j) j le_rfl

open Polynomial Algebra

variable (R : Type*) {A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The combined polynomial `Φ = X·P₁ + P₂` of a pair. -/
noncomputable def combined (P₁ P₂ : A[X]) : A[X] := X * P₁ + P₂

/-- The coefficients of `Φ` visible on the window `G` at cutoff `t`. -/
def visible (Φ : A[X]) (G : Finset ℕ) (t : ℕ) : Set A :=
  (fun i => Φ.coeff i) '' {i | i ∈ G ∧ t ≤ i}

/-- The visible algebra `𝒱(K, Φ, G, t) = K ⊔ adjoin_R {Φ_i : i ∈ G, t ≤ i}`. -/
def Vis (K : Subalgebra R A) (Φ : A[X]) (G : Finset ℕ) (t : ℕ) : Subalgebra R A :=
  K ⊔ adjoin R (visible Φ G t)

variable {R}

section basic

variable {K : Subalgebra R A} {Φ : A[X]} {G : Finset ℕ} {t : ℕ}

theorem coeff_mem_visible {i : ℕ} (hi : i ∈ G) (ht : t ≤ i) : Φ.coeff i ∈ visible Φ G t :=
  ⟨i, ⟨hi, ht⟩, rfl⟩

theorem known_le_Vis : K ≤ Vis R K Φ G t := le_sup_left

theorem adjoin_visible_le_Vis : adjoin R (visible Φ G t) ≤ Vis R K Φ G t := le_sup_right

theorem known_mem_Vis {a : A} (ha : a ∈ K) : a ∈ Vis R K Φ G t := known_le_Vis ha

theorem coeff_mem_Vis {i : ℕ} (hi : i ∈ G) (ht : t ≤ i) : Φ.coeff i ∈ Vis R K Φ G t :=
  adjoin_visible_le_Vis (subset_adjoin (coeff_mem_visible hi ht))

theorem algebraMap_mem_Vis (r : R) : algebraMap R A r ∈ Vis R K Φ G t :=
  Subalgebra.algebraMap_mem _ r

/-- **Transport lemma** (cutoff-indexed): the visible algebra is the least subalgebra containing
`K` and the visible coefficients.  This is the formal counterpart of "derivable via", and the
tool for composing certificates: instantiate `W` with another visible algebra whose cutoff
depends on the current degree. -/
theorem Vis_le_iff {W : Subalgebra R A} :
    Vis R K Φ G t ≤ W ↔ K ≤ W ∧ ∀ i ∈ G, t ≤ i → Φ.coeff i ∈ W := by
  constructor
  · intro h
    refine ⟨le_trans known_le_Vis h, fun i hi ht => h (coeff_mem_Vis hi ht)⟩
  · rintro ⟨hK, hΦ⟩
    refine sup_le hK (adjoin_le ?_)
    rintro _ ⟨i, ⟨hi, ht⟩, rfl⟩
    exact hΦ i hi ht

theorem Vis_le {W : Subalgebra R A} (hK : K ≤ W)
    (hΦ : ∀ i ∈ G, t ≤ i → Φ.coeff i ∈ W) : Vis R K Φ G t ≤ W :=
  Vis_le_iff.2 ⟨hK, hΦ⟩

/-- Monotonicity in all three arguments: a larger context, a larger window, or a lower cutoff
sees more. -/
theorem Vis_mono {K' : Subalgebra R A} {G' : Finset ℕ} {t' : ℕ}
    (hK : K ≤ K') (hG : G ⊆ G') (ht : t' ≤ t) :
    Vis R K Φ G t ≤ Vis R K' Φ G' t' :=
  Vis_le (le_trans hK known_le_Vis) fun _ hi hti => coeff_mem_Vis (hG hi) (le_trans ht hti)

theorem Vis_antitone_cutoff {t' : ℕ} (ht : t' ≤ t) :
    Vis R K Φ G t ≤ Vis R K Φ G t' :=
  Vis_mono le_rfl Finset.Subset.rfl ht

/-- Raising the cutoff past an index outside the window changes nothing. -/
theorem Vis_succ_of_not_mem (ht : t ∉ G) : Vis R K Φ G t = Vis R K Φ G (t + 1) := by
  refine le_antisymm (Vis_le known_le_Vis fun i hi hti => ?_) (Vis_antitone_cutoff (by omega))
  have hne : i ≠ t := fun h => ht (h ▸ hi)
  have : t < i := lt_of_le_of_ne hti (Ne.symm hne)
  exact coeff_mem_Vis hi this

/-- Cancel an invertible scalar multiple inside a subalgebra. -/
theorem mem_of_natCast_mul_mem {S : Subalgebra R A} {n : ℕ} {x : A}
    (hn : IsUnit ((n : ℕ) : R)) (h : ((n : ℕ) : A) * x ∈ S) : x ∈ S := by
  obtain ⟨u, hu⟩ := hn
  have hkey : x = algebraMap R A ↑u⁻¹ * (((n : ℕ) : A) * x) := by
    rw [show ((n : ℕ) : A) = algebraMap R A ((n : ℕ) : R) from by push_cast; rfl,
      ← hu, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [hkey]
  exact S.mul_mem (S.algebraMap_mem _) h

/-- Divide an already visible affine pivot by a unit slope from the scalar ring.  This is
the algebraic operation underlying every scalar row of a decoding certificate. -/
theorem mem_of_unit_slope {V : Subalgebra R A} {r : R} (hr : IsUnit r)
    {x y : A} (hx : x ∈ V) (hxy : algebraMap R A r * y = x) : y ∈ V := by
  obtain ⟨u, hu⟩ := hr
  have hrA : algebraMap R A ↑u⁻¹ * algebraMap R A r = 1 := by
    rw [← hu, ← map_mul,
      Units.inv_mul, map_one]
  have hkey : y = algebraMap R A ↑u⁻¹ * x := by
    rw [← hxy, ← mul_assoc, hrA, one_mul]
  rw [hkey]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) hx

/-- Natural-number specialization of `mem_of_unit_slope`. -/
theorem mem_of_nat_mul_eq {V : Subalgebra R A} {m : ℕ} (hm : IsUnit (m : R))
    {x y : A} (hx : x ∈ V) (hxy : (m : A) * y = x) : y ∈ V := by
  apply mem_of_unit_slope hm hx
  rwa [map_natCast]

/-- The slope-two specialization used by the finite square decoders. -/
theorem mem_of_two_mul_eq {V : Subalgebra R A} (h2 : IsUnit (2 : R))
    {x y : A} (hx : x ∈ V) (hxy : 2 * y = x) : y ∈ V :=
  mem_of_nat_mul_eq h2 hx hxy

end basic

section combined

variable (P₁ P₂ : A[X])

@[simp] theorem coeff_combined (k : ℕ) :
    (combined P₁ P₂).coeff (k + 1) = P₁.coeff k + P₂.coeff (k + 1) := by
  simp [combined, coeff_X_mul]

@[simp] theorem coeff_combined_zero : (combined P₁ P₂).coeff 0 = P₂.coeff 0 := by
  simp [combined]


theorem coeff_combined_zero_left (W : A[X]) (i : ℕ) :
    (combined (0 : A[X]) W).coeff i = W.coeff i := by
  cases i with
  | zero => rw [coeff_combined_zero]
  | succ t => rw [coeff_combined, coeff_zero, zero_add]
end combined

/-- Componentwise membership of a pair's coefficients gives membership of the
combined polynomial's coefficients. -/
theorem coeff_combined_mem {P₁ P₂ : A[X]} {V : Subalgebra R A}
    (h₁ : ∀ j, P₁.coeff j ∈ V) (h₂ : ∀ j, P₂.coeff j ∈ V) :
    ∀ i, (combined P₁ P₂).coeff i ∈ V := by
  intro i
  cases i with
  | zero =>
    rw [coeff_combined_zero]
    exact h₂ 0
  | succ m =>
    rw [coeff_combined]
    exact Subalgebra.add_mem _ (h₁ m) (h₂ (m + 1))

/-- The *causal core* of compatibility: the degree-`j` coefficient of `P₁` is *predictable*
(visible at cutoff `j+1`) and that of `P₂` is *adapted* (visible at cutoff `j`) with respect
to the degree filtration of `Φ = X·P₁ + P₂`.  No monicity or degree data — this is what the
combination engines consume. -/
structure CausalPair (K : Subalgebra R A) (P₁ P₂ : A[X]) (G : Finset ℕ) : Prop where
  mem₁ : ∀ j, P₁.coeff j ∈ Vis R K (combined P₁ P₂) G (j + 1)
  mem₂ : ∀ j, P₂.coeff j ∈ Vis R K (combined P₁ P₂) G j

namespace CausalPair

variable {K : Subalgebra R A} {P₁ P₂ : A[X]} {G : Finset ℕ}

/-- Every coefficient of the combined polynomial is visible at its own cutoff. -/
theorem combined_coeff_mem (h : CausalPair K P₁ P₂ G) (i : ℕ) :
    (combined P₁ P₂).coeff i ∈ Vis R K (combined P₁ P₂) G i := by
  cases i with
  | zero => simpa using h.mem₂ 0
  | succ j =>
      rw [coeff_combined]
      exact Subalgebra.add_mem _ (h.mem₁ j) (h.mem₂ (j + 1))

theorem mono {K' : Subalgebra R A} {G' : Finset ℕ} (h : CausalPair K P₁ P₂ G)
    (hK : K ≤ K') (hG : G ⊆ G') : CausalPair K' P₁ P₂ G' where
  mem₁ j := Vis_mono hK hG le_rfl (h.mem₁ j)
  mem₂ j := Vis_mono hK hG le_rfl (h.mem₂ j)

/-- V-relative pair recovery: any subalgebra over `K` containing the combined
coefficients of a causal pair contains both components' coefficients. -/
theorem coeff_mem_of_le
    (h : CausalPair K P₁ P₂ G) {V : Subalgebra R A} (hKV : K ≤ V)
    (hPV : ∀ j, (combined P₁ P₂).coeff j ∈ V) :
    (∀ j, P₁.coeff j ∈ V) ∧ (∀ j, P₂.coeff j ∈ V) :=
  ⟨fun j => Vis_le hKV (fun i _ _ => hPV i) (h.mem₁ j),
   fun j => Vis_le hKV (fun i _ _ => hPV i) (h.mem₂ j)⟩

end CausalPair

section SideInformation

variable {K : Subalgebra R A}

/-- **`lem:discharge-side-information`** in the subalgebra encoding: a decoder for the
parameter set `Θ` from `Q` given the auxiliary list `B`, together with recovery of `Q`
and of every `B i` from `P` given the remaining side context `K`, yields a decoder for
`Θ` from `P` given `K` with no occurrence of the discharged list. -/
theorem discharge_side_information {ι : Type*} {Q P : A[X]} {B : ι → A[X]}
    {Θ : Set A}
    (hdec : ∀ V : Subalgebra R A, (∀ j, Q.coeff j ∈ V) →
      (∀ i j, (B i).coeff j ∈ V) → Θ ⊆ (V : Set A))
    (hQ : ∀ j, Q.coeff j ∈ K ⊔ adjoin R (Set.range fun j => P.coeff j))
    (hB : ∀ i j, (B i).coeff j ∈ K ⊔ adjoin R (Set.range fun j => P.coeff j)) :
    Θ ⊆ ((K ⊔ adjoin R (Set.range fun j => P.coeff j) : Subalgebra R A) : Set A) :=
  hdec _ hQ hB

/-- **`lem:extractable-via-derivable`** (recovery composes): if `Θ` decodes from `Q`
given `B`, and `Q` recovers from `P` given the same list `B`, then `Θ` decodes from
`P` given `B`. -/
theorem extractable_via_derivable {ι : Type*} {Q P : A[X]} {B : ι → A[X]}
    {Θ : Set A}
    (hdec : ∀ V : Subalgebra R A, (∀ j, Q.coeff j ∈ V) →
      (∀ i j, (B i).coeff j ∈ V) → Θ ⊆ (V : Set A))
    (hQ : ∀ V : Subalgebra R A, (∀ j, P.coeff j ∈ V) →
      (∀ i j, (B i).coeff j ∈ V) → ∀ j, Q.coeff j ∈ V) :
    ∀ V : Subalgebra R A, (∀ j, P.coeff j ∈ V) →
      (∀ i j, (B i).coeff j ∈ V) → Θ ⊆ (V : Set A) :=
  fun V hP hB => hdec V (hQ V hP hB) hB

end SideInformation

/-- A **compatible pair** on the window `G` given the known context `K` (paper
`def:compatible-pair`): a causal pair of monic polynomials of degree `n` with
`G ⊆ {0,…,n}`. -/
structure CompatiblePair (K : Subalgebra R A) (P₁ P₂ : A[X]) (n : ℕ) (G : Finset ℕ) :
    Prop extends CausalPair K P₁ P₂ G where
  monic₁ : P₁.Monic
  monic₂ : P₂.Monic
  natDegree₁ : P₁.natDegree = n
  natDegree₂ : P₂.natDegree = n
  window : G ⊆ Finset.range (n + 1)

namespace CompatiblePair

variable {K : Subalgebra R A} {P₁ P₂ : A[X]} {n : ℕ} {G : Finset ℕ}

/-- Compatibility is monotone in the known context and in the window. -/
theorem mono {K' : Subalgebra R A} {G' : Finset ℕ} (h : CompatiblePair K P₁ P₂ n G)
    (hK : K ≤ K') (hG : G ⊆ G') (hG' : G' ⊆ Finset.range (n + 1)) :
    CompatiblePair K' P₁ P₂ n G' where
  toCausalPair := h.toCausalPair.mono hK hG
  monic₁ := h.monic₁
  monic₂ := h.monic₂
  natDegree₁ := h.natDegree₁
  natDegree₂ := h.natDegree₂
  window := hG'

/-- Every coefficient of a compatible pair is recoverable from the whole window. -/
theorem coeff₁_mem (h : CompatiblePair K P₁ P₂ n G) (j : ℕ) :
    P₁.coeff j ∈ Vis R K (combined P₁ P₂) G 0 :=
  Vis_antitone_cutoff (Nat.zero_le _) (h.mem₁ j)

theorem coeff₂_mem (h : CompatiblePair K P₁ P₂ n G) (j : ℕ) :
    P₂.coeff j ∈ Vis R K (combined P₁ P₂) G 0 :=
  Vis_antitone_cutoff (Nat.zero_le _) (h.mem₂ j)

end CompatiblePair

end FastPoly
