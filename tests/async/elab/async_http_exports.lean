module

import Std.Http

/-!
`import Std.Http` gives the HTTP library, not the helpers its test suite uses: those come from
`import Std.Http.Test.Helpers`.
-/

/-- error: Unknown identifier `Std.Http.Internal.Test.mkGet` -/
#guard_msgs in
#check Std.Http.Internal.Test.mkGet
