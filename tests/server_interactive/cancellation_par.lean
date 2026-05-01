import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-!
Test contrasting cancellation behavior between sequential and parallel combinators.

Each section uses `check_cancel <label>`: on first invocation it loops checking
`Core.checkInterrupted`, waiting for the second invocation (triggered by re-elaboration) to
signal it. If the cancel token was properly set, `checkInterrupted` fires first and the tactic
is interrupted. Otherwise the signal arrives, the tactic finds `cancelTk` unset, and prints
`"{label}: leaked!"`.

**Sequential `first`** (section 1): runs on the main elaboration thread, sharing the command's
cancel token. On re-elaboration, `checkInterrupted` fires — no leak.

**Parallel `attempt_all_par`** (section 2): runs in a subtask via `asTask` with its own fresh
cancel token. Nobody sets that token on re-elaboration — **leak**.

**Parallel `first_par`** (section 3): same bug as `attempt_all_par`.
-/

/-! ## Sequential `first`: cancellation works -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : True := by
  wait_for_cancel_once_async
  try? => first
    | check_cancel first

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! ## Parallel `attempt_all_par`: cancellation is broken -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : True := by
  wait_for_cancel_once_async
  try? => attempt_all_par
    | check_cancel attempt_all_par

-- RESET
import Lean.Server.Test.Cancel
open Lean.Server.Test.Cancel

/-! ## Parallel `first_par`: cancellation is broken -/

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

theorem t : True := by
  wait_for_cancel_once_async
  try? => first_par
    | check_cancel first_par
