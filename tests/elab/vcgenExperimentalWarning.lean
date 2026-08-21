import Std.WP
import Std.Tactic.Do

/-!
`vcgen` warns about its experimental status on each call. `set_option experimental.vcgen true`
acknowledges the experimental status and silences the warning.
-/

open Std.WP

set_option warn.sorry false

/--
warning: The `vcgen` tactic is an experimental drop-in replacement for `mvcgen` that will eventually replace it; `set_option experimental.vcgen true` acknowledges its experimental status and silences this warning.
-/
#guard_msgs (warning) in
example : ⦃ (True : Prop) ⦄ (pure 0 : Id Nat) ⦃ fun _ => True ⦄ := by
  vcgen
  all_goals sorry

#guard_msgs in
set_option experimental.vcgen true in
example : ⦃ (True : Prop) ⦄ (pure 0 : Id Nat) ⦃ fun _ => True ⦄ := by
  vcgen
  all_goals sorry
