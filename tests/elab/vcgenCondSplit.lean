import Std.WP
import Std.Tactic.Do

/-!
`vcgen` splits a program headed by `cond` (`bif c then t else e`) into one verification
condition per branch, with `c = true` or `c = false` in scope. The split rule is cached
per monad, so repeated `cond` programs reuse it.
-/

open Std.WP

set_option mvcgen.warning false

def condEffects (f : Nat → Bool) : StateM Nat Nat := do
  bif f 0 then set 1 else set 2
  get

theorem condEffects_spec (f : Nat → Bool) :
    ⦃ fun _ => True ⦄ condEffects f ⦃ fun r _ => r > 0 ⦄ := by
  vcgen [condEffects] with finish

def condValue (b : Bool) : Id Nat := do
  let x ← bif b then pure 1 else pure 2
  pure (x + 1)

theorem condValue_spec (b : Bool) :
    ⦃ True ⦄ condValue b ⦃ fun r => r > 1 ⦄ := by
  vcgen [condValue] with finish

def condTwice (f : Nat → Bool) : StateM Nat Nat := do
  bif f 0 then set 1 else set 2
  bif f 1 then modify (· + 1) else modify (· + 2)
  get

theorem condTwice_spec (f : Nat → Bool) :
    ⦃ fun _ => True ⦄ condTwice f ⦃ fun r _ => r > 1 ⦄ := by
  vcgen [condTwice] with finish

def condLit : StateM Nat Nat := do
  bif true then set 1 else set 2
  get

theorem condLit_spec : ⦃ fun _ => True ⦄ condLit ⦃ fun r _ => r = 1 ⦄ := by
  vcgen [condLit] with finish
