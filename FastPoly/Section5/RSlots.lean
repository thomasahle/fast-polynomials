import FastPoly.Section4.PeeledCert

/-!
# Row→slot map of the `lem:Rk2l`(3) certificates

`rSlot k l α r` is the pivot parameter of row `r` of the `Rpair k l` certificate
(`l ≥ 2`; the layout is machine-validated in `tools/rk2l_stage_table.py`).
-/

namespace FastPoly

open Polynomial Algebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Fuel-indexed row→slot map of the `R_{k,2^l}` certificate. -/
noncomputable def rSlotF : ℕ → ℕ → ℕ → (ℕ → A) → ℕ → A
  | 0, _, _, α, r => α r
  | f + 1, k, l, α, r =>
    if k ≤ 1 then α r
    else if k = 2 then
      if r = 0 then α 0
      else if r < 2 ^ (l - 1) then peelSlot (l - 1) (fun j => α (1 + j)) (r - 1)
      else if r = 2 ^ (l - 1) then α (2 ^ (l - 1))
      else peelSlot (l - 1) (fun j => α (2 ^ (l - 1) + 1 + j)) (r - 2 ^ (l - 1) - 1)
    else if k % 2 = 0 then
      if r < (k - 2) * 2 ^ l then rSlotF f (k / 2) (l + 1) α r
      else if r = (k - 2) * 2 ^ l then α ((k - 2) * 2 ^ l)
      else if r < (k - 2) * 2 ^ l + 2 ^ (l - 1) then
        peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 1 + j))
          (r - (k - 2) * 2 ^ l - 1)
      else if r = (k - 2) * 2 ^ l + 2 ^ (l - 1) then
        α ((k - 2) * 2 ^ l + 2 ^ (l - 1))
      else
        peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
          (r - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1)
    else if l ≤ 2 then
      if r < 4 then α r
      else if r < 4 * (k - 2) then
        rSlotF f ((k - 1) / 2) 3 (fun j => α (4 + j)) (r - 4)
      else α r
    else
      if r = 0 then α 0
      else if r < 2 ^ l then peelSlot l (fun j => α (1 + j)) (r - 1)
      else if r < (k - 2) * 2 ^ l then
        rSlotF f ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) (r - 2 ^ l)
      else if r = (k - 2) * 2 ^ l then α ((k - 2) * 2 ^ l)
      else if r < (k - 2) * 2 ^ l + 2 ^ (l - 2) then
        peelSlot (l - 2) (fun j => α ((k - 2) * 2 ^ l + 1 + j))
          (r - (k - 2) * 2 ^ l - 1)
      else if r = (k - 2) * 2 ^ l + 2 ^ (l - 2) then
        α ((k - 2) * 2 ^ l + 2 ^ (l - 2))
      else if r < (k - 2) * 2 ^ l + 2 ^ (l - 1) then
        peelSlot (l - 2) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + j))
          (r - (k - 2) * 2 ^ l - 2 ^ (l - 2) - 1)
      else if r = (k - 2) * 2 ^ l + 2 ^ (l - 1) then
        α ((k - 2) * 2 ^ l + 2 ^ (l - 1))
      else
        peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
          (r - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1)

/-- The row→slot map of the `R_{k,2^l}` certificate (`l ≥ 2`). -/
noncomputable def rSlot (k l : ℕ) (α : ℕ → A) : ℕ → A := rSlotF k k l α

/-- One-step unfolding of `rSlotF` (definitional). -/
theorem rSlotF_succ (f k l : ℕ) (α : ℕ → A) (r : ℕ) :
    rSlotF (f + 1) k l α r =
      (if k ≤ 1 then α r
      else if k = 2 then
        if r = 0 then α 0
        else if r < 2 ^ (l - 1) then peelSlot (l - 1) (fun j => α (1 + j)) (r - 1)
        else if r = 2 ^ (l - 1) then α (2 ^ (l - 1))
        else peelSlot (l - 1) (fun j => α (2 ^ (l - 1) + 1 + j)) (r - 2 ^ (l - 1) - 1)
      else if k % 2 = 0 then
        if r < (k - 2) * 2 ^ l then rSlotF f (k / 2) (l + 1) α r
        else if r = (k - 2) * 2 ^ l then α ((k - 2) * 2 ^ l)
        else if r < (k - 2) * 2 ^ l + 2 ^ (l - 1) then
          peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 1 + j))
            (r - (k - 2) * 2 ^ l - 1)
        else if r = (k - 2) * 2 ^ l + 2 ^ (l - 1) then
          α ((k - 2) * 2 ^ l + 2 ^ (l - 1))
        else
          peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
            (r - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1)
      else if l ≤ 2 then
        if r < 4 then α r
        else if r < 4 * (k - 2) then
          rSlotF f ((k - 1) / 2) 3 (fun j => α (4 + j)) (r - 4)
        else α r
      else
        if r = 0 then α 0
        else if r < 2 ^ l then peelSlot l (fun j => α (1 + j)) (r - 1)
        else if r < (k - 2) * 2 ^ l then
          rSlotF f ((k - 1) / 2) (l + 1) (fun j => α (2 ^ l + j)) (r - 2 ^ l)
        else if r = (k - 2) * 2 ^ l then α ((k - 2) * 2 ^ l)
        else if r < (k - 2) * 2 ^ l + 2 ^ (l - 2) then
          peelSlot (l - 2) (fun j => α ((k - 2) * 2 ^ l + 1 + j))
            (r - (k - 2) * 2 ^ l - 1)
        else if r = (k - 2) * 2 ^ l + 2 ^ (l - 2) then
          α ((k - 2) * 2 ^ l + 2 ^ (l - 2))
        else if r < (k - 2) * 2 ^ l + 2 ^ (l - 1) then
          peelSlot (l - 2) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 2) + 1 + j))
            (r - (k - 2) * 2 ^ l - 2 ^ (l - 2) - 1)
        else if r = (k - 2) * 2 ^ l + 2 ^ (l - 1) then
          α ((k - 2) * 2 ^ l + 2 ^ (l - 1))
        else
          peelSlot (l - 1) (fun j => α ((k - 2) * 2 ^ l + 2 ^ (l - 1) + 1 + j))
            (r - (k - 2) * 2 ^ l - 2 ^ (l - 1) - 1)) := rfl

/-- Fuel irrelevance of the `Rk2l` slot map. -/
theorem rSlotF_fuel :
    ∀ k f f', k ≤ f → k ≤ f' → ∀ (l : ℕ) (α : ℕ → A) (r : ℕ),
      rSlotF f k l α r = rSlotF f' k l α r := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro f f' hf hf' l α r
    match k, f, f' with
    | 0, 0, 0 => rfl
    | 0, 0, _ + 1 => rfl
    | 0, _ + 1, 0 => rfl
    | 0, _ + 1, _ + 1 => rfl
    | k + 1, f + 1, f' + 1 =>
      rw [rSlotF_succ, rSlotF_succ,
        ih ((k + 1) / 2) (by omega) f f' (by omega) (by omega) (l + 1) α r,
        ih ((k + 1 - 1) / 2) (by omega) f f' (by omega) (by omega) 3
          (fun j => α (4 + j)) (r - 4),
        ih ((k + 1 - 1) / 2) (by omega) f f' (by omega) (by omega) (l + 1)
          (fun j => α (2 ^ l + j)) (r - 2 ^ l)]

section anchors

variable (α : ℕ → A)

-- (4,3) rows 0..7 = {0,4,5,7,6,3,2,1} (inner R(2,4) base block), 16..23 identity
example : rSlot 4 3 α 1 = α 5 := rfl
example : rSlot 4 3 α 3 = α 7 := rfl
example : rSlot 4 3 α 7 = α 4 := rfl
example : rSlot 4 3 α 11 = α 15 := rfl
example : rSlot 4 3 α 17 = α 17 := rfl
example : rSlot 4 3 α 20 = α 20 := rfl
-- (5,3): low peel-embed, shifted inner, identity band
example : rSlot 5 3 α 3 = α 7 := rfl
example : rSlot 5 3 α 9 = α 13 := rfl
example : rSlot 5 3 α 19 = α 23 := rfl
example : rSlot 5 3 α 27 = α 27 := rfl
-- (5,2) identity, (8,2) nested
example : rSlot 5 2 α 13 = α 13 := rfl
example : rSlot 8 2 α 3 = α 7 := rfl
example : rSlot 8 2 α 24 = α 24 := rfl

end anchors

end FastPoly
