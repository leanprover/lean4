import LinterTest.Suggest

/- The `#suggestMark` linter attaches a `Try this` suggestion in each of its `pre` and `post` passes,
so both surface as messages on the command. -/

/--
info: Try this:
  [apply] #eval 0
---
info: Try this:
  [apply] #eval 1
-/
#guard_msgs (ordering := sorted) in
#suggestMark
