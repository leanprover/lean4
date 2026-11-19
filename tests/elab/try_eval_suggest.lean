/-!
# Tests for `try? => tac` syntax

These tests verify that the `try? => tac` syntax correctly runs a user-supplied tactic
through `evalSuggest` and reports suggestions.
-/

/-- info: Try this:
  [apply] rfl -/
#guard_msgs (info) in
example : 1 = 1 := by
  try? => rfl

/-- info: Try this:
  [apply] rfl -/
#guard_msgs (info) in
example : 1 = 1 := by
  try? => first | assumption | rfl

/-- info: Try these:
  [apply] rfl
  [apply] simp_all -/
#guard_msgs (info) in
example : 1 = 1 := by
  try? => attempt_all | rfl | simp_all

/-- info: Try these:
  [apply] rfl
  [apply] simp_all -/
#guard_msgs (info) in
example : 1 = 1 := by
  try? => attempt_all_par | rfl | simp_all

-- first_par returns whichever finishes first; just test it doesn't error
#guard_msgs (drop info) in
example : 1 = 1 := by
  try? => first_par | rfl | simp_all

/-- info: Try these:
  [apply] assumption
  [apply] rfl -/
#guard_msgs (info) in
example (h : 1 = 1) : 1 = 1 := by
  try? => attempt_all | assumption | rfl

-- `max` config option should limit suggestions
/-- info: Try this:
  [apply] rfl -/
#guard_msgs (info) in
example : 1 = 1 := by
  try? (max := 1) => attempt_all | rfl | simp_all
