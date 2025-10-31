import Lean

set_premise_selector Lean.LibrarySuggestions.sineQuaNonSelector

-- Test that grind? +suggestions does NOT include +suggestions in its output
/--
info: Try this:
  [apply] grind only
-/
#guard_msgs in
example {x y : Nat} (h : x = y) : y = x := by
  grind? +suggestions
