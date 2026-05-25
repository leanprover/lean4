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

-- `cases` parameters affect the case-split configuration rather than the
-- E-matching theorem set, so `grind?` must preserve them in `grind only`
-- suggestions.
/--
grind only [cases Option]
-/
#guard_msgs (substring := true) in
example (x : Option Nat) : x = none \/ Exists fun n => x = some n := by
  grind? [cases Option]

/--
grind only [cases Bool]
-/
#guard_msgs (substring := true) in
example (f : Bool -> Bool) (x : Bool) : f (f (f x)) = f x := by
  cases h1 : f true <;> cases h2 : f false <;> grind? only [cases Bool]
