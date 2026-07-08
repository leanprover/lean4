import Lean

set_library_suggestions Lean.LibrarySuggestions.sineQuaNonSelector

-- Test that grind? +suggestions does NOT include +suggestions in its output
/--
info: Try this:
  [apply] grind only
-/
#guard_msgs in
example {x y : Nat} (h : x = y) : y = x := by
  grind? +suggestions

def f (x : α) := x

/--
info: Try these:
  [apply] grind only [f]
  [apply] grind => instantiate only [f]
-/
#guard_msgs in
example {x y : Nat} (h : x = y) : x = f y := by
  grind? +suggestions [f]
