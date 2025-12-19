module

/-!
# Tests for `exact?` with private declarations

This tests that `exact?` can suggest private theorems defined locally in the same module.
-/

-- Test that exact? suggests private declarations
axiom P : Prop
private axiom p : P

/--
info: Try this:
  [apply] exact p
-/
#guard_msgs in
example : P := by exact?
