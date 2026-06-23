import Lean.Server.Test.Cancel
import Lean.Elab.Tactic.Try
open Lean Lean.Meta Lean.Elab Lean.Elab.Term Lean.Elab.Tactic
open Lean.Server.Test.Cancel

-- Diagnostic anchor: synchronous, fires exactly once at command-elab time
-- before any async task is spawned by the rest of the file. If a CI / stress
-- failure shows this line in `.out.produced`, the file worker at least got
-- past imports.
#eval (IO.eprintln "test: imports done" : IO Unit)

/-!
Test that `cancelRec` reaches the snapshot task spawned by
`elabEmptyByAsTry` on re-elaboration.

Chronological flow:
1. Empty-`by` example elaborates; `elabEmptyByAsTry` spawns a snapshot
   task with its own cancel token and returns.
2. The snapshot task's `try?` calls `tracerSuggestion`, which:
   - registers test task `"cancelTokenSet"`,
   - registers `cancelTk.onSet` to resolve it,
   - resolves sync promise `"tracerSuggestion"`,
   - returns `wait_for_test_task "cancelTokenSet"` as the candidate.
3. `try?` evaluates the candidate; it blocks on the test task.
4. `t1` elaborates: `wait_for_sync "tracerSuggestion"` returns
   immediately, `trace "blocked"` emits the diagnostic.
5. Runner inserts `; skip`, triggers re-elab; `cancelRec` sets the
   cancel token; `onSet` resolves the test task; the candidate's wait
   returns; the snapshot task body completes.

Failure modes:
- `cancelTk? := none` to `Core.logSnapshotTask`: `cancelRec` cannot
  reach the cancel token, the wait blocks, runner times out.
- `cancelTk? := none` to `wrapAsyncAsSnapshot`: `tracerSuggestion`
  sees no cancel token, doesn't register `onSet`; the promise drops;
  `wait_for_test_task` surfaces a `task dropped` diagnostic.

Ordering note: the empty-`by` example must precede `t1` because `try?`
inside the snapshot task library-searches the environment in a way
that synchronously waits on prior pending async theorem bodies. With
`t1` first, its `wait_for_sync` would block the snapshot's `try?`,
deadlocking. Likely a separate upstream issue.
-/

namespace TestEmptyBy

opaque UnsolvableProp : Prop

@[try_suggestion]
def tracerSuggestion (_goal : MVarId) (_info : Try.Info) :
    MetaM (Array (TSyntax `tactic)) := do
  -- Keep dbg_trace output here minimal and gated to the first invocation:
  -- this function runs in the snapshot task's stderr buffer, which interleaves
  -- non-deterministically with the main elab thread's output. Every additional
  -- trace point adds a potential race in `.out.expected`.
  if let some prom ← mkTestTask "cancelTokenSet" then
    if let some cancelTk := (← readThe Core.Context).cancelTk? then
      cancelTk.onSet do
        dbg_trace "cancelTokenSet"
        prom.resolve ()
    else
      dbg_trace "tracerSuggestion: no cancel token (unexpected -- test setup wrong?)"
    dbg_trace "tracerSuggestion ready"
  resolveSyncPromise "tracerSuggestion"
  return #[← `(tactic| wait_for_test_task "cancelTokenSet")]

end TestEmptyBy

set_option tactic.tryOnEmptyBy true
-- Skip the expensive built-in `try?` branches (`simp`/`grind`/`exact?`/…). The
-- test only cares about the user-registered `tracerSuggestion` running inside
-- the snapshot task; the library-search branches are pure overhead here.
set_option debug.tactic.try.onlyUserSuggestions true

example : True := by
  trivial
       --^ waitFor: blocked
       --^ insert: "; skip"
       --^ sync

example : TestEmptyBy.UnsolvableProp := by

theorem t1 : True := by
  wait_for_sync "tracerSuggestion"
  dbg_trace "sync received"
  trace "blocked"
  trivial
