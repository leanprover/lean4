import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-!
Cancellation tests. Use `wait_for_cancel_once` to block the server and send a message to the client
who should wait for it with `waitFor` and then issue a new document version, which will unblock
`wait_for_cancel_once`
-/

/-! Changes in a declaration should invalidate elaboration of later declarations. -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ collectDiagnostics
       -- (should never print "blocked")

theorem t : True := by
  wait_for_cancel_once
  dbg_trace "rerun!"
  trivial

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! Changes in a declaration should not invalidate async tasks of previous declarations. -/

theorem t1 : True := by
  wait_for_unblock_async
  trivial

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; unblock"
       --^ collectDiagnostics
       -- (should print "blocked" exactly once)

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! Changes in a tactic should not invalidate async tasks of previous tactics. -/

theorem t1 : True := by
  wait_for_unblock_async
  trivial
       --^ waitFor: blocked
       --^ insert: "; unblock"
       --^ collectDiagnostics
       -- (should print "blocked" exactly once)
