import Lean
import Std
import Std.Tactic.Do

set_option mvcgen.warning false
set_option warn.sorry false

/-! Tests for the `mvcgen' until <pattern>` stop condition. -/

open Std.Do

namespace MVCGenUntil

def tick : StateM Nat Unit := modify (· + 1)

def useTick : StateM Nat Nat := do
  tick
  return 0

def step (k : Nat) : StateM Nat Unit := modify (· + k)

def useStep : StateM Nat Nat := do
  step 1
  return 0

def getThenTick : StateM Nat Nat := do
  let x ← get
  tick
  return x

-- `until tick` matches the nullary `tick` call and stops; `unfold tick` hits the leftover `wp⟦tick⟧`.
theorem useTick_until : ⦃⌜True⌝⦄ useTick ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen' [useTick] until tick
  all_goals unfold tick
  all_goals admit

-- An explicit hole matches: `until step _` stops at `step 1`, the `_` matching its argument.
theorem useStep_until_hole : ⦃⌜True⌝⦄ useStep ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen' [useStep] until step _
  all_goals unfold step
  all_goals admit

-- A concrete argument discriminates: `until step 1` matches the `step 1` call and stops.
theorem useStep_until_one : ⦃⌜True⌝⦄ useStep ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen' [useStep] until step 1
  all_goals unfold step
  all_goals admit

-- ...but `until step 2` does not match `step 1`, so VC generation reaches the un-specced call.
/-- error: No spec found for program step 1. -/
#guard_msgs in
example : ⦃⌜True⌝⦄ useStep ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen' [useStep] until step 2

-- A non-matching `until` (with a hole) is a no-op: VC generation runs to completion.
theorem useStep_until_nomatch : ⦃⌜True⌝⦄ useStep ⦃⇓ r => ⌜r = 0⌝⦄ := by
  mvcgen' [useStep, step] until List.length _
  all_goals grind

-- The overloaded `get` is resolved against the program's monad and matches the `get` call, so VC
-- generation stops before the un-specced `tick`. A wrong resolution would proceed to `tick` and error.
theorem getThenTick_until_get : ⦃⌜True⌝⦄ getThenTick ⦃⇓ _ => ⌜True⌝⦄ := by
  mvcgen' [getThenTick] until get
  all_goals admit

end MVCGenUntil
