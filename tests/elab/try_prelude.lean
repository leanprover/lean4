prelude
import Init.Notation
/-!
Tests that while working on the prelude, try?-on-by does not run when not all infrastructure is
availbe.
-/

set_option tactic.tryOnEmptyBy true

/--
error: unsolved goals
⊢ True
-/
#guard_msgs in
theorem test : True := by
