import Lean

set_premise_selector Lean.PremiseSelection.sineQuaNonSelector

-- Test that grind? +premises does NOT include +premises in its output
/--
info: Try this:
  [apply] grind only
-/
#guard_msgs in
example {x y : Nat} (h : x = y) : y = x := by
  grind? +premises
