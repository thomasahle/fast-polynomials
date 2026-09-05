import FastPoly.Height.Depth
import FastPoly.Cost.PeeledCircuit

/-!
# Depth environments for the construction wiring

The multiplicative-depth analogue of `constructionEnv`: the variable, the
parameters, and the source wires sit at depth `0`; the power wire `H_{2^i}`
sits at a given depth `dp i`; the shifted power at `dps`.  The first payload
theorem is the peeled gadget's ledger height (`lem:peeled-Q-count`, circuit
form): over a tower with `dp i ≤ i`, the peeled circuit has depth at most
`k` — the fact that collapses the tower recurrence of
`thm:construction-height`.
-/

namespace FastPoly.Height

open FastPoly.Cost

/-- Depth assignment for the construction inputs. -/
def denv (dp : ℕ → ℕ) (dps : ℕ) : ConstructionInput → ℕ
  | .variable => 0
  | .power i => dp i
  | .shiftedPower => dps
  | .parameter _ => 0
  | .source _ => 0

@[simp] theorem denv_variable (dp : ℕ → ℕ) (dps : ℕ) :
    denv dp dps .variable = 0 := rfl

@[simp] theorem denv_power (dp : ℕ → ℕ) (dps : ℕ) (i : ℕ) :
    denv dp dps (.power i) = dp i := rfl

@[simp] theorem denv_shiftedPower (dp : ℕ → ℕ) (dps : ℕ) :
    denv dp dps .shiftedPower = dps := rfl

@[simp] theorem denv_parameter (dp : ℕ → ℕ) (dps : ℕ) (i : ℕ) :
    denv dp dps (.parameter i) = 0 := rfl

@[simp] theorem denv_source (dp : ℕ → ℕ) (dps : ℕ) (i : Fin 2) :
    denv dp dps (.source i) = 0 := rfl

/-- Canonical gadget input depths: the supplied quadratic wire at depth one, the
supplied quartic (and its shifted copy) at depth two. -/
def gadgetDp : ℕ → ℕ := fun i => if i = 1 then 1 else 2

@[simp] theorem gadgetDp_one : gadgetDp 1 = 1 := rfl

@[simp] theorem gadgetDp_two : gadgetDp 2 = 2 := rfl

theorem gadgetDp_le : ∀ i, 1 ≤ i → gadgetDp i ≤ i := by
  intro i hi
  rw [gadgetDp]
  split <;> omega

/-- The canonical depth environment of a local odd gadget. -/
abbrev gadgetDepthEnv : ConstructionInput → ℕ := denv gadgetDp 2

variable {R : Type*} [CommRing R]

omit [CommRing R] in
/-- Depth is invariant under parameter reindexing. -/
theorem multDepth_reindexConstructionParameters {m : ℕ} (f : ℕ → ℕ)
    (c : Circuit R ConstructionInput m) (dp : ℕ → ℕ) (dps : ℕ) :
    (c.reindexConstructionParameters f).multDepth (denv dp dps)
      = c.multDepth (denv dp dps) := by
  rw [Circuit.reindexConstructionParameters, Circuit.multDepth_relabel]
  congr 1
  funext input
  cases input <;> rfl

omit [CommRing R] in
/-- **Height of the peeled gadget circuit** (`lem:peeled-Q-count`, circuit form):
over a tower at depths `dp i ≤ i`, the level-`k` peeled circuit has
multiplicative depth at most `k`. -/
theorem multDepth_peelCircuitF (dp : ℕ → ℕ) (dps : ℕ) :
    ∀ f k, 1 ≤ k → k ≤ f + 1 → (∀ i, 1 ≤ i → i < k → dp i ≤ i) →
      (peelCircuitF (R := R) f k).multDepth (denv dp dps) 0 ≤ k := by
  intro f
  induction f with
  | zero =>
    intro k hk1 hkf hdp
    match k, hk1, hkf with
    | 1, _, _ =>
      show max (denv dp dps .variable) (denv dp dps (.parameter 0)) ≤ 1
      simp
  | succ f ih =>
    intro k hk1 hkf hdp
    match k with
    | 1 =>
      show max (denv dp dps .variable) (denv dp dps (.parameter 0)) ≤ 1
      simp
    | 2 =>
      show max
          (max (max (denv dp dps .variable) (denv dp dps (.parameter 2)))
            (max (denv dp dps (.power 1)) (denv dp dps (.parameter 1))) + 1)
          (denv dp dps (.parameter 0)) ≤ 2
      have h1 := hdp 1 le_rfl (by omega)
      simp only [denv_variable, denv_parameter, denv_power]
      omega
    | 3 =>
      show max
          (max (max (denv dp dps (.power 2)) (denv dp dps (.parameter 0)))
            (max (max (max (denv dp dps .variable) (denv dp dps (.parameter 3)))
              (max (denv dp dps (.power 1)) (denv dp dps (.parameter 2))) + 1)
              (denv dp dps (.parameter 1))) + 1)
          (max (max (max (denv dp dps .variable) (denv dp dps (.parameter 6)))
            (max (denv dp dps (.power 1)) (denv dp dps (.parameter 5))) + 1)
            (denv dp dps (.parameter 4))) ≤ 3
      have h1 := hdp 1 le_rfl (by omega)
      have h2 := hdp 2 (by omega) (by omega)
      simp only [denv_variable, denv_parameter, denv_power]
      omega
    | kk + 4 =>
      have hW := ih (kk + 3) (by omega) (by omega)
        (fun i hi1 hik => hdp i hi1 (by omega))
      have hB := ih (kk + 3) (by omega) (by omega)
        (fun i hi1 hik => hdp i hi1 (by omega))
      have hpw := hdp (kk + 3) (by omega) (by omega)
      show max
          (max (max (denv dp dps (.power (kk + 3))) (denv dp dps (.parameter 0)))
            (((peelCircuitF (R := R) f (kk + 3)).reindexConstructionParameters
              (fun j => 1 + j)).multDepth (denv dp dps) 0) + 1)
          (((peelCircuitF (R := R) f (kk + 3)).reindexConstructionParameters
            (fun j => 2 ^ (kk + 3) + j)).multDepth (denv dp dps) 0) ≤ kk + 4
      rw [multDepth_reindexConstructionParameters, multDepth_reindexConstructionParameters]
      simp only [denv_power, denv_parameter]
      omega

omit [CommRing R] in
/-- The packaged form for the tower threading. -/
theorem multDepth_peelCircuit (dp : ℕ → ℕ) (dps : ℕ) (k : ℕ) (hk : 1 ≤ k)
    (hdp : ∀ i, 1 ≤ i → i < k → dp i ≤ i) :
    (peelCircuit (R := R) k).multDepth (denv dp dps) 0 ≤ k :=
  multDepth_peelCircuitF dp dps k k hk (by omega) hdp

end FastPoly.Height
