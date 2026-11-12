import Std.Http

/-!
`import Std.Http` gives the HTTP library, not the helpers its test suite uses: those come from
`import Std.Http.Test.Helpers` (#16282). This file is not a `module`, so it sees everything that
`import Std.Http` loads.
-/

/-- error: Unknown identifier `Std.Http.Internal.Test.mkGet` -/
#guard_msgs in
#check Std.Http.Internal.Test.mkGet

/-- error: Unknown identifier `Std.Http.Internal.Test.check` -/
#guard_msgs in
#check Std.Http.Internal.Test.check

/-- error: Unknown identifier `Std.Http.Internal.Test.serveRaw` -/
#guard_msgs in
#check Std.Http.Internal.Test.serveRaw

/-- error: Unknown identifier `Std.Http.Internal.Test.hangGuard` -/
#guard_msgs in
#check Std.Http.Internal.Test.hangGuard

/-- error: Unknown identifier `Std.Http.Internal.Test.MachineTester` -/
#guard_msgs in
#check Std.Http.Internal.Test.MachineTester
