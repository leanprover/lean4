/-!
# Tests for `exact? +all`

This tests the `+all` option which collects all successful lemmas
instead of stopping at the first complete solution.
-/

set_option linter.unusedVariables false

-- Create a custom inductive with limited lemmas for controlled testing
inductive MyTrue : Prop where
  | intro

-- Define exactly three ways to prove MyTrue
theorem myTrue1 : MyTrue := MyTrue.intro
theorem myTrue2 : MyTrue := MyTrue.intro
theorem myTrue3 : MyTrue := MyTrue.intro

-- Test: without +all, we get a single suggestion and the goal is solved
/--
info: Try this:
  [apply] exact myTrue3
-/
#guard_msgs in
example : MyTrue := by exact?

-- Test: with +all, exact? finds all lemmas (including the constructor)
-- The goal is admitted (sorry), and all suggestions are shown in one message
/--
info: Try these:
  [apply] exact myTrue3
  [apply] exact MyTrue.intro
  [apply] exact myTrue1
  [apply] exact myTrue2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : MyTrue := by exact? +all

-- Test: apply? also supports +all
/--
info: Try these:
  [apply] exact myTrue3
  [apply] exact MyTrue.intro
  [apply] exact myTrue1
  [apply] exact myTrue2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example : MyTrue := by apply? +all

-- Test: verify that +all without any matches still errors appropriately
/--
error: `exact?` could not close the goal. Try `apply?` to see partial suggestions.
-/
#guard_msgs in
example (n : Nat) (h : n = n + 1) : False := by exact? +all

def Empty.elim2 := @Empty.elim

/--
info: Try these:
  [apply] exact h.elim
  [apply] exact h.elim2
---
warning: declaration uses `sorry`
-/
#guard_msgs in
example {α : Sort u} (h : Empty) : α := by exact? +all

/-- error: `exact?` could not close the goal. -/
#guard_msgs in
example {α : Sort u} (h : Empty) : α := by exact? +all -star
