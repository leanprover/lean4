import Std.Tactic.Do

/-!
`mvcgen` splits a program headed by `cond` (`bif c then t else e`) into one verification
condition per branch, with `c = true` or `c = false` in scope.
-/

open Std.Do

set_option mvcgen.warning false
set_option grind.warning false

def condEffects (f : Nat → Bool) : StateM Nat Nat := do
  bif f 0 then set 1 else set 2
  get

theorem condEffects_triple (f : Nat → Bool) :
    ⦃⌜True⌝⦄ condEffects f ⦃⇓ r => ⌜r > 0⌝⦄ := by
  unfold condEffects
  mvcgen
  all_goals grind

def condValue (b : Bool) : Id Nat := do
  let x ← bif b then pure 1 else pure 2
  pure (x + 1)

theorem condValue_triple (b : Bool) :
    ⦃⌜True⌝⦄ condValue b ⦃⇓ r => ⌜r > 1⌝⦄ := by
  unfold condValue
  mvcgen
  all_goals grind

def condTwice (f : Nat → Bool) : StateM Nat Nat := do
  bif f 0 then set 1 else set 2
  bif f 1 then modify (· + 1) else modify (· + 2)
  get

theorem condTwice_triple (f : Nat → Bool) :
    ⦃⌜True⌝⦄ condTwice f ⦃⇓ r => ⌜r > 1⌝⦄ := by
  unfold condTwice
  mvcgen
  all_goals grind

def condLit : StateM Nat Nat := do
  bif true then set 1 else set 2
  get

theorem condLit_triple : ⦃⌜True⌝⦄ condLit ⦃⇓ r => ⌜r = 1⌝⦄ := by
  unfold condLit
  mvcgen
  all_goals grind
