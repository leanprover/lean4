/-!
# cutsat deprecation test

Tests that `cutsat` suggests replacing with `lia`.
-/

/--
warning: `cutsat` has been deprecated, use `lia` instead
---
info: Try this:
  [apply] lia
-/
#guard_msgs in
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  cutsat

/--
warning: `cutsat` has been deprecated, use `lia` instead
---
info: Try this:
  [apply] lia
-/
#guard_msgs in
example {x y : Int} :  2 * x + 3 * y = 0 → 1 ≤ x → y < 1 := by
  cutsat

-- Test that lia works the same way
example {x y : Int} : 2 * x + 4 * y ≠ 5 := by
  lia

example {x y : Int} : 2 * x + 3 * y = 0 → 1 ≤ x → y < 1 := by
  lia
