import FastPoly.Section5.Binomial

/-!
# The `U`-binomial expansion

Engine for the odd branch of `lem:Rk2l` (paper `R-odd-error-bound`): the exact expansion

  `(H - n·U)·(H + U)^n = ∑_{t=0}^{n+1} (C(n,t) - n·C(n,t-1)) · U^t · H^{n+1-t}`.

At `n = k - 1` the `t = 0` term is `H^k`, the `t = 1` coefficient vanishes, the `t = 2`
coefficient is `-k(k-1)/2 = -c`, and the `t ≥ 3` tail has controlled degree with top
coefficient `-τ = -k(k-1)(k-2)/3`.
-/

namespace FastPoly

open Polynomial Finset

variable {A : Type*} [CommRing A]

/-- **Exact `U`-binomial expansion** of `(H - n·U)·(H + U)^n`. -/
theorem mul_pow_expand (H U : A[X]) (n : ℕ) :
    (H - (n : A[X]) * U) * (H + U) ^ n
      = ∑ t ∈ Finset.range (n + 2),
          ((n.choose t : A[X])
            - (if t = 0 then 0 else (n : A[X]) * (n.choose (t - 1) : A[X])))
            * (U ^ t * H ^ (n + 1 - t)) := by
  have hpow : (U + H) ^ n
      = ∑ t ∈ Finset.range (n + 1), U ^ t * H ^ (n - t) * (n.choose t : A[X]) :=
    add_pow U H n
  have h1 : H * (U + H) ^ n
      = ∑ t ∈ Finset.range (n + 1), (n.choose t : A[X]) * (U ^ t * H ^ (n + 1 - t)) := by
    rw [hpow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have htn := Finset.mem_range.1 ht
    have hh : H * H ^ (n - t) = H ^ (n + 1 - t) := by
      rw [← pow_succ']
      congr 1
      omega
    calc H * (U ^ t * H ^ (n - t) * (n.choose t : A[X]))
        = (H * H ^ (n - t)) * (U ^ t * (n.choose t : A[X])) := by ring
      _ = (n.choose t : A[X]) * (U ^ t * H ^ (n + 1 - t)) := by rw [hh]; ring
  have h1' : H * (U + H) ^ n
      = ∑ t ∈ Finset.range (n + 2), (n.choose t : A[X]) * (U ^ t * H ^ (n + 1 - t)) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul,
      add_zero, h1]
  have h2 : (n : A[X]) * U * (U + H) ^ n
      = ∑ t ∈ Finset.range (n + 1),
          ((n : A[X]) * (n.choose t : A[X])) * (U ^ (t + 1) * H ^ (n - t)) := by
    rw [hpow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    have hu : U * U ^ t = U ^ (t + 1) := by rw [← pow_succ']
    calc (n : A[X]) * U * (U ^ t * H ^ (n - t) * (n.choose t : A[X]))
        = ((n : A[X]) * (n.choose t : A[X])) * ((U * U ^ t) * H ^ (n - t)) := by ring
      _ = ((n : A[X]) * (n.choose t : A[X])) * (U ^ (t + 1) * H ^ (n - t)) := by rw [hu]
  have h3 : ∑ s ∈ Finset.range (n + 2),
        (if s = 0 then 0 else (n : A[X]) * (n.choose (s - 1) : A[X]))
          * (U ^ s * H ^ (n + 1 - s))
      = ∑ t ∈ Finset.range (n + 1),
          ((n : A[X]) * (n.choose t : A[X])) * (U ^ (t + 1) * H ^ (n - t)) := by
    rw [Finset.sum_range_succ' _ (n + 1)]
    rw [if_pos rfl, zero_mul, add_zero]
    refine Finset.sum_congr rfl fun s hs => ?_
    have hidx : n + 1 - (s + 1) = n - s := by omega
    rw [if_neg (by omega), show s + 1 - 1 = s from rfl, hidx]
  have hprod : (H - (n : A[X]) * U) * (H + U) ^ n
      = H * (U + H) ^ n - (n : A[X]) * U * (U + H) ^ n := by
    rw [add_comm U H]
    ring
  rw [hprod, h1', h2, ← h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  ring

/-- The `t ≥ 3` tail of the `U`-binomial expansion. -/
noncomputable def uTail (H U : A[X]) (n : ℕ) : A[X] :=
  ∑ t ∈ Finset.Icc 3 (n + 1),
    ((n.choose t : A[X]) - (n : A[X]) * (n.choose (t - 1) : A[X]))
      * (U ^ t * H ^ (n + 1 - t))

/-- **Peeled `U`-binomial expansion** (paper: the explicit cancellation in `E_i^U`):
the `t = 1` term vanishes and the `t = 2` term carries `C(n,2) - n²`. -/
theorem mul_pow_split (H U : A[X]) {n : ℕ} (hn : 2 ≤ n) :
    (H - (n : A[X]) * U) * (H + U) ^ n
      = H ^ (n + 1)
        + ((n.choose 2 : A[X]) - (n : A[X]) * (n : A[X])) * (U ^ 2 * H ^ (n - 1))
        + uTail H U n := by
  rw [mul_pow_expand]
  have hsplit : Finset.range (n + 2)
      = insert 0 (insert 1 (insert 2 (Finset.Icc 3 (n + 1)))) := by
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [hsplit, Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_Icc]),
    Finset.sum_insert (by simp [Finset.mem_insert, Finset.mem_Icc]),
    Finset.sum_insert (by simp [Finset.mem_Icc])]
  have hbody : ∑ t ∈ Finset.Icc 3 (n + 1),
      ((n.choose t : A[X])
        - (if t = 0 then 0 else (n : A[X]) * (n.choose (t - 1) : A[X])))
        * (U ^ t * H ^ (n + 1 - t))
      = uTail H U n := by
    unfold uTail
    refine Finset.sum_congr rfl fun t ht => ?_
    have ht3 := (Finset.mem_Icc.1 ht).1
    rw [if_neg (by omega)]
  rw [hbody, if_pos rfl, if_neg (by omega : ¬(1:ℕ) = 0), if_neg (by omega : ¬(2:ℕ) = 0)]
  have hidx2 : n + 1 - 2 = n - 1 := by omega
  rw [hidx2]
  norm_num [Nat.choose_zero_right, Nat.choose_one_right]
  try ring

/-- Degree bound for the `U`-binomial tail: with `deg U ≤ r ≤ D` and `deg H ≤ D`, every
`t ≥ 3` summand has degree at most `3r + (n-2)D`. -/
theorem natDegree_uTail_le {H U : A[X]} {D r n : ℕ} (hH : H.natDegree ≤ D)
    (hU : U.natDegree ≤ r) (hrD : r ≤ D) :
    (uTail H U n).natDegree ≤ 3 * r + (n - 2) * D := by
  unfold uTail
  refine natDegree_sum_le_of_forall_le _ _ fun t ht => ?_
  obtain ⟨ht3, htn⟩ := Finset.mem_Icc.1 ht
  have hc : ((n.choose t : A[X]) - (n : A[X]) * (n.choose (t - 1) : A[X])).natDegree ≤ 0 := by
    refine le_trans (natDegree_sub_le _ _) (max_le (le_of_eq (natDegree_natCast _)) ?_)
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_natCast, natDegree_natCast]
  have hu : (U ^ t).natDegree ≤ t * r :=
    le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hU)
  have hh : (H ^ (n + 1 - t)).natDegree ≤ (n + 1 - t) * D :=
    le_trans natDegree_pow_le (Nat.mul_le_mul_left _ hH)
  have hterm : (((n.choose t : A[X]) - (n : A[X]) * (n.choose (t - 1) : A[X]))
      * (U ^ t * H ^ (n + 1 - t))).natDegree ≤ t * r + (n + 1 - t) * D := by
    refine le_trans natDegree_mul_le ?_
    have hin := le_trans natDegree_mul_le (Nat.add_le_add hu hh)
    omega
  refine le_trans hterm ?_
  have k1 : t * r = 3 * r + (t - 3) * r := by
    have h3 : t = 3 + (t - 3) := by omega
    calc t * r = (3 + (t - 3)) * r := by rw [← h3]
    _ = 3 * r + (t - 3) * r := by ring
  have k2 : (t - 3) * r ≤ (t - 3) * D := Nat.mul_le_mul_left _ hrD
  have k3 : (t - 3) * D + (n + 1 - t) * D = (n - 2) * D := by
    have h6 : t - 3 + (n + 1 - t) = n - 2 := by omega
    calc (t - 3) * D + (n + 1 - t) * D = (t - 3 + (n + 1 - t)) * D := by ring
    _ = (n - 2) * D := by rw [h6]
  omega

end FastPoly
