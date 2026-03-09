import Std.Tactic.Do

open Std.Do

set_option mvcgen.warning false

-- The following used to print the Syntax object representing `abc`

/-- error: Could not resolve spec theorem `abc` -/
#guard_msgs (error) in
example : True := by mvcgen [abc]
