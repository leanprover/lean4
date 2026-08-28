/-!
# Test that `grind?` includes term parameters in its suggestion

When a user provides term arguments to `grind?`, they should be included
in the suggestion even if they are not tracked via E-matching.
-/

-- Test: Term argument should be included in suggestion
-- The term `show False by exact h` is passed as argument and should appear in output
/--
info: Try this:
  [apply] grind only [show False by exact h]
-/
#guard_msgs in
example (h : False) : False := by grind? [show False by exact h]
