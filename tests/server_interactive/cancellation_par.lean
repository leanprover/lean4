import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-!
Test that cancellation propagates into parallel tactic combinators (`attempt_all_par`,
`first_par`).

Each section's first elaboration runs `block_until_cancelled "<label>"`, which loops on
`Core.checkInterrupted`. The test driver edits the preceding `example` to trigger
re-elaboration; the second elaboration's invocation no-ops (label already seen) so the test can
terminate. If cancellation reaches the (possibly subtask) tactic, the loop throws and the test
completes; if not, the test hangs and the runner times out.

Section 1 uses sequential `first` (cancellation has always worked here — runs on the main
elaboration thread). Sections 2 and 3 use `attempt_all_par` and `first_par`, which spawn the
tactic on a fresh `asTask` cancel token; before the propagation fix in `CoreM.asTask`, those
tasks would not see the parent's cancellation and the test would hang.
-/

/-! ## Sequential `first` -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : True := by
  wait_for_cancel_once_async
  try? => first
    | block_until_cancelled "first"

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! ## Parallel `attempt_all_par` -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : True := by
  wait_for_cancel_once_async
  try? => attempt_all_par
    | block_until_cancelled "attempt_all_par"

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! ## Parallel `first_par` -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : True := by
  wait_for_cancel_once_async
  try? => first_par
    | block_until_cancelled "first_par"
