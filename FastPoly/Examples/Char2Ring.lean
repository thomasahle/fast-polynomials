import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Ring normalization in characteristic two

`ring_char2` is ordinary `ring_nf`, followed by explicit applications of
`CharP.cast_eq_mod` to its integer coefficients. It produces kernel-checked
ring identities, not a finite-field decision procedure. Exponents are never
reduced using finite-field identities: in particular it does not use `x² = x`.
-/

open Lean Meta Elab Tactic

private def ringChar2Step : TacticM Unit := do
  evalTactic (← `(tactic| ring_nf (config := { failIfUnchanged := false })))
  if (← getGoals).isEmpty then return
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOfArity ``Eq 3 do
    throwError "ring_char2 expects an equality"
  let carrier := target.getAppArgs[0]!
  let numerals ← IO.mkRef (#[] : Array Nat)
  target.forEach fun e => do
    if e.isAppOfArity ``OfNat.ofNat 3 then
      let args := e.getAppArgs
      if args[0]! == carrier then
        if let .lit (.natVal n) := args[1]! then
          if n > 1 && !(← numerals.get).contains n then
            numerals.modify (·.push n)
  if (← numerals.get).isEmpty then return
  let ty ← Term.exprToSyntax carrier
  let mut hs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for n in ← numerals.get do
    let h := mkIdent (← mkFreshUserName `char2Coefficient)
    let ns := Syntax.mkNumLit (toString n)
    let rs := Syntax.mkNumLit (toString (n % 2))
    evalTactic (← `(tactic|
      have $h : ($ns : $ty) = ($rs : $ty) := by
        simpa only [Nat.reduceMod, Nat.cast_zero, Nat.cast_one] using
          (CharP.cast_eq_mod $ty 2 $ns)))
    hs := hs.push (← `(Parser.Tactic.simpLemma| $h:ident))
  evalTactic (← `(tactic|
    simp only [$[$hs],*, zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one]))

/-- Reducing coefficients can expose another ring subexpression. Each bounded
normalization pass uses the ordinary ring normalizer and explicit cast lemmas. -/
elab "ring_char2" : tactic => do
  for _ in [:16] do
    if (← getGoals).isEmpty then return
    let before ← instantiateMVars (← getMainTarget)
    ringChar2Step
    if (← getGoals).isEmpty then return
    if before == (← instantiateMVars (← getMainTarget)) then
      throwError "ring_char2 reached a fixed point without closing the identity"
  throwError "ring_char2 exhausted its normalization passes"
