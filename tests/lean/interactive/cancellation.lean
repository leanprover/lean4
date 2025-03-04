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

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! Changes in a tactic *should* invalidate async tasks of subsequent tactics. -/

theorem t1 : True := by
  skip
    --^ waitFor: blocked
    --^ insert: "; skip"
    --^ collectDiagnostics
    -- (should never print "blocked")
  wait_for_cancel_once_async
  trivial

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! Changes in the body should not invalidate header async tasks. -/

theorem t1 : (by wait_for_unblock_async; exact True) := by
  skip
    --^ waitFor: blocked
    --^ insert: "; unblock"
    --^ collectDiagnostics
    -- (should print "blocked" exactly once)
  trivial

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! Changes in the header *should* invalidate header async tasks. -/

theorem t1 : (by wait_for_cancel_once_async; exact True) := by
        --^ waitFor: blocked
        --^ insert: "'"
        --^ collectDiagnostics
        -- (should never print "blocked")
  trivial

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! Changes in the body (without incrementality) *should* invalidate body async tasks. -/

theorem t1 : True := (by
  skip
    --^ waitFor: blocked
    --^ insert: "; skip"
    --^ collectDiagnostics
    -- (should never print "blocked")
  wait_for_cancel_once_async
  trivial)
