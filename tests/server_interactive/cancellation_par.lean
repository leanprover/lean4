import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-!
Test that cancellation propagates into parallel tactic combinators (`attempt_all_par`,
`first_par`).

Per section, chronological flow:
1. `theorem t` elaborates; its body runs `try? => <combinator> | block_until_cancelled "<L>"`,
   which on the first invocation registers test task `"<L>"`, resolves sync promise `"<L>"`,
   and enters a `Core.checkInterrupted` loop.
2. The gate theorem (`tGate`) elaborates; `wait_for_sync "<L>"` returns immediately (sync was
   resolved in step 1), `trace "blocked"` emits the diagnostic the runner is waiting for.
3. Runner inserts `; skip`, triggers re-elab; `cancelRec` walks `t`'s snapshot tree, setting
   the cancel token of the `block_until_cancelled` subtask. The loop's `Core.checkInterrupted`
   throws, the `finally` resolves the test task, the second invocation's wait returns.

Section 1 uses sequential `first`; sections 2 and 3 use the parallel combinators
`attempt_all_par` and `first_par`, which spawn the inner tactic on a fresh `asTask` cancel
token. The fix in `CoreM.asTask` (#13428) propagates the parent token to those subtasks;
without it, `cancelRec` cannot reach the subtask's cancel token and the test times out.
-/

/-! ## Sequential `first` -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : True := by
  try? => first
    | block_until_cancelled "first"

theorem tGate : True := by
  wait_for_sync "first"
  trace "blocked"
  trivial

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
  try? => attempt_all_par
    | block_until_cancelled "attempt_all_par"

theorem tGate : True := by
  wait_for_sync "attempt_all_par"
  trace "blocked"
  trivial

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
  try? => first_par
    | block_until_cancelled "first_par"

theorem tGate : True := by
  wait_for_sync "first_par"
  trace "blocked"
  trivial
