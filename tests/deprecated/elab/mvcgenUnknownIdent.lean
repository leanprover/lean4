import Std.Tactic.Do

/-!
Tests the error message of the deprecated `mvcgen` tactic for an unknown spec identifier.
-/

set_option sym.debug true

open Std.Do

-- The following used to print the Syntax object representing `abc`

/-- error: Could not resolve spec theorem `abc` -/
#guard_msgs (error) in
example : True := by mvcgen [abc]
