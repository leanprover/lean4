/-
Tests for `tactic.tryOnEmptyBy`: empty `by` blocks run `try?` and suggest proofs.
-/

set_option tactic.tryOnEmptyBy true

-- Basic: empty by reports unsolved goals first (so the user sees it immediately
-- even when `try?` is slow), then `try?` emits its suggestions as a single info
-- message with the option-disabling hint at the end.
/--
error: unsolved goals
⊢ True
---
info: Try these:
  [apply] by solve_by_elim
  [apply] by simp
  [apply] by simp only
  [apply] by grind
  [apply] by grind only
  [apply] by simp_all

(Disable this with `set_option tactic.tryOnEmptyBy false`.)
-/
#guard_msgs in
example : True := by

-- Disabled: empty by gives unsolved goals
/--
error: unsolved goals
⊢ True
-/
#guard_msgs in
set_option tactic.tryOnEmptyBy false in
example : True := by

-- Non-empty by is not affected
example : True := by
  trivial

-- by { } (braces) is not affected
example : True := by { trivial }

-- by { } (empty braces) does not trigger try?
/--
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by { }

-- Unprovable goal: try? finds no suggestions, so the implicit mode is fully silent
-- (no "Try this", no error or warning from try? itself — only the unsolved-goals error).
-- We use an opaque Prop so the default branches (including `impossible by decide |
-- impossible by simp | impossible by grind`) cannot dispatch it.
opaque OpaqueProp : Prop
/--
error: unsolved goals
⊢ OpaqueProp
-/
#guard_msgs in
example : OpaqueProp := by

-- Nested in a backtracking combinator (`errToSorry = false`): try? must stay silent.
-- We only assert the absence of the try? info message; the unsolved-goals error is expected
-- because `exact (by)` succeeds at term-elab time (the empty tactic block fails later).
/--
error: unsolved goals
⊢ True
-/
#guard_msgs in
example : True := by first | exact (by) | trivial
