/-!
Regression test for #16229: `grind.debug` panicked in `checkEqc` on `-x = -1` for signed fixed-width
integers. Literals such as `-1` are not in the congruence table, and the invariant checker must not
require `-1` to be the congruence root of `-x` when `x = 1`.
-/
set_option grind.debug true

example (x : Int8) (h : x = 1) : -x = -1 := by grind
example (x : Int16) (h : x = 1) : -x = -1 := by grind
example (x : Int32) (h : x = 1) : -x = -1 := by grind
example (x : Int64) (h : x = 1) : -x = -1 := by grind
example (x : Int) (h : x = 1) : -x = -1 := by grind

example (x : Int8) (h : x = 1) (p : Int8 → Prop) (h₂ : p (-1)) : p (-x) := by grind
example (x : Int64) (h : x = 5) (p : Int64 → Prop) (h₂ : p (-5)) : p (-x) := by grind
