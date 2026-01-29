/-!
# Test that `grind?` includes local variable dot notation params in its suggestion

When a user provides a parameter like `s.myThm` where `s` is a local variable
and `myThm` is a field access, it should be included in the suggestion.
These params are processed as term params (not global decls) and produce anchors.
Without including the original term in the suggestion, the anchor can't match on replay.

Regression test for: grind? suggestions not working with local variable dot notation
-/
set_option linter.unusedVariables false

structure MyStruct where
  val : Nat

-- A theorem with an indexable pattern
theorem MyStruct.add_comm (s : MyStruct) (a b : Nat) : a + b = b + a := Nat.add_comm a b

-- Test: Local variable dot notation should be included in the suggestion
-- `s.add_comm` is a local variable dot notation (not a global decl),
-- so it should appear in the grind only suggestion
/--
info: Try this:
  [apply] grind only [= s.add_comm]
-/
#guard_msgs in
example (s : MyStruct) : (1 : Nat) + 2 = 2 + 1 := by
  grind? [= s.add_comm]

-- Verify the suggestion works by using it
example (s : MyStruct) : (1 : Nat) + 2 = 2 + 1 := by
  grind only [= s.add_comm]
