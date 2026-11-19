import Std.Tactic.Do
import Std.WP

set_option sym.debug true

/-! `vcgen` explains how to migrate when the goal is a `Std.Do` triple and `Std.WP` is imported
(#15691). -/

set_option experimental.vcgen true

def f : Id Nat := pure 1

open Std.Do in
/-- error: vcgen: the goal is stated in the `Std.Do` program logic, but `vcgen` works on `Std.WP` triples

Hint: To use `vcgen`, restate the goal and its specifications with the definitions from `Std.WP`, such as `Std.WP.Triple`.
-/
#guard_msgs in
example : ⦃⌜True⌝⦄ f ⦃⇓ r => ⌜r = 1⌝⦄ := by
  vcgen [f]

open Std.WP in
example : ⦃ True ⦄ f ⦃ fun r => r = 1 ⦄ := by
  vcgen [f]
