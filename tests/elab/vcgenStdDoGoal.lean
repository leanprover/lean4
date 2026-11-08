import Std.Tactic.Do

/-! `vcgen` explains how to migrate when the goal is a `Std.Do` triple and `Std.WP` is not
imported (#15691). -/

open Std.Do

set_option experimental.vcgen true

def f : Id Nat := pure 1

/-- error: vcgen: the goal is stated in the `Std.Do` program logic, but `vcgen` works on `Std.WP` triples

Hint: To use `vcgen`, add `import Std.WP` and restate the goal and its specifications with the definitions from `Std.WP`, such as `Std.WP.Triple`.
-/
#guard_msgs in
example : ⦃⌜True⌝⦄ f ⦃⇓ r => ⌜r = 1⌝⦄ := by
  vcgen [f]

/-- error: vcgen: the goal is stated in the `Std.Do` program logic, but `vcgen` works on `Std.WP` triples

Hint: To use `vcgen`, add `import Std.WP` and restate the goal and its specifications with the definitions from `Std.WP`, such as `Std.WP.Triple`.
-/
#guard_msgs in
example : ⌜True⌝ ⊢ₛ wp⟦f⟧ (⇓ r => ⌜r = 1⌝) := by
  vcgen [f]

/-- error: vcgen: the `Std.WP` program logic is not available

Hint: Add `import Std.WP`.
-/
#guard_msgs in
example : True := by
  vcgen
