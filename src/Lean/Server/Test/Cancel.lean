/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/
module

prelude
public import Lean.Elab.Command
public import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Command
public meta import Lean.Elab.Tactic.Basic

public section

/-!
Helpers for testing cancellation in interactive tests. Put here because of `initialize` restrictions
and to avoid repeated elaboration overhead per test.
-/

namespace Lean.Server.Test.Cancel

meta initialize onceRef : IO.Ref (Option (Task Unit)) ← IO.mkRef none

/--
On first invocation, sends a diagnostics "blocked", blocks until cancelled, and then eprints
"cancelled!"; further invocations complete when this wait is done but do not wait for their own
cancellation. Thus all document versions should complete strictly after the printing has completed
and we avoid terminating the server too early to see the message.
-/
scoped syntax "wait_for_cancel_once" : tactic
@[incremental]
elab_rules : tactic
| `(tactic| wait_for_cancel_once) => do
  let prom ← IO.Promise.new
  if let some t := (← onceRef.modifyGet (fun old => (old, old.getD prom.result!))) then
    IO.wait t
    return

  dbg_trace "blocked!"
  log "blocked"
  let ctx ← readThe Elab.Term.Context
  let some tacSnap := ctx.tacSnap? | unreachable!
  tacSnap.new.resolve {
    diagnostics := (← Language.Snapshot.Diagnostics.ofMessageLog (← Core.getMessageLog))
    stx := default
    finished := default
  }

  let ctx ← readThe Core.Context
  let some cancelTk := ctx.cancelTk? | unreachable!
  -- TODO: `CancelToken` should probably use `Promise`
  while true do
    if (← cancelTk.isSet) then
      break
    IO.sleep 30
  IO.eprintln "cancelled!"
  log "cancelled (should never be visible)"
  prom.resolve ()
  Core.checkInterrupted

-- CancelToken is Promise-based, so we can't create one during `initialize`
-- (task manager not yet ready). Create lazily on first use, atomically via `modifyGet`
-- to avoid two callers each constructing a token and only one being stored.
meta initialize unblockedCancelTkRef : IO.Ref (Option IO.CancelToken) ← IO.mkRef none

private meta def getUnblockedCancelTk : BaseIO IO.CancelToken := do
  let fresh ← IO.CancelToken.new
  unblockedCancelTkRef.modifyGet fun
    | some tk => (tk, some tk)
    | none    => (fresh, some fresh)

/--
Waits for `unblock` to be called, which is expected to happen in a subsequent document version that
does not invalidate this tactic. Complains if cancellation token was set before unblocking, i.e. if
the tactic was invalidated after all.
-/
scoped syntax "wait_for_unblock" : tactic
@[incremental]
elab_rules : tactic
| `(tactic| wait_for_unblock) => do
  let ctx ← readThe Core.Context
  let some cancelTk := ctx.cancelTk? | unreachable!

  dbg_trace "blocked!"
  log "blocked"
  let ctx ← readThe Elab.Term.Context
  let some tacSnap := ctx.tacSnap? | unreachable!
  tacSnap.new.resolve {
    diagnostics := (← Language.Snapshot.Diagnostics.ofMessageLog (← Core.getMessageLog))
    stx := default
    finished := default
  }

  while true do
    if (← (← getUnblockedCancelTk).isSet) then
      break
    IO.sleep 30
  if (← cancelTk.isSet) then
    IO.eprintln "cancelled!"
    log "cancelled (should never be visible)"

/--
Spawns a `logSnapshotTask` that waits for `unblock` to be called, which is expected to happen in a
subsequent document version that does not invalidate this tactic. Complains if cancellation token
was set before unblocking, i.e. if the tactic was invalidated after all.
-/
elab "wait_for_unblock_async" : tactic => do
  let cancelTk ← IO.CancelToken.new
  let act ← Elab.Term.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => do
    let ctx ← readThe Core.Context
    let some cancelTk := ctx.cancelTk? | unreachable!
    while true do
      if (← (← getUnblockedCancelTk).isSet) then
        break
      IO.sleep 30
    if (← cancelTk.isSet) then
      IO.eprintln "cancelled!"
      log "cancelled (should never be visible)"
  let t ← BaseIO.asTask (act ())
  Core.logSnapshotTask { stx? := none, task := t, cancelTk? := cancelTk }

  log "blocked"

/-- Unblocks a `wait_for_unblock*` task. -/
scoped elab "unblock" : tactic => do
  dbg_trace "unblocking!"
  (← getUnblockedCancelTk).set

/--
Like `wait_for_cancel_once` but does the waiting in a separate task and waits for its
cancellation.
-/
scoped syntax "wait_for_cancel_once_async" : tactic
@[incremental]
elab_rules : tactic
| `(tactic| wait_for_cancel_once_async) => do
  let prom ← IO.Promise.new
  if let some t := (← onceRef.modifyGet (fun old => (old, old.getD prom.result!))) then
    IO.wait t
    return

  let cancelTk ← IO.CancelToken.new
  let act ← Elab.Term.wrapAsyncAsSnapshot (cancelTk? := cancelTk) fun _ => do
    let ctx ← readThe Core.Context
    let some cancelTk := ctx.cancelTk? | unreachable!
    -- TODO: `CancelToken` should probably use `Promise`
    while true do
      if (← cancelTk.isSet) then
        break
      IO.sleep 30
    IO.eprintln "cancelled!"
    log "cancelled (should never be visible)"
    prom.resolve ()
    Core.checkInterrupted
  let t ← BaseIO.asTask (act ())
  Core.logSnapshotTask { stx? := none, task := t, cancelTk? := cancelTk }

  dbg_trace "blocked!"
  log "blocked"

/--
Like `wait_for_cancel_once_async` but waits for the main thread's cancellation token. This is useful
to test main thread cancellation in non-incremental contexts because we otherwise wouldn't be able
to send out the "blocked" message from there.
-/
scoped syntax "wait_for_main_cancel_once_async" : tactic
@[incremental]
elab_rules : tactic
| `(tactic| wait_for_main_cancel_once_async) => do
  let prom ← IO.Promise.new
  if let some t := (← onceRef.modifyGet (fun old => (old, old.getD prom.result!))) then
    IO.wait t
    return

  let some cancelTk := (← readThe Core.Context).cancelTk? | unreachable!
  let act ← Elab.Term.wrapAsyncAsSnapshot (cancelTk? := none) fun _ => do
    let ctx ← readThe Core.Context
    -- TODO: `CancelToken` should probably use `Promise`
    while true do
      if (← cancelTk.isSet) then
        break
      IO.sleep 30
    IO.eprintln "cancelled!"
    log "cancelled (should never be visible)"
    prom.resolve ()
    Core.checkInterrupted
  let t ← BaseIO.asTask (act ())
  Core.logSnapshotTask { stx? := none, task := t, cancelTk? := cancelTk }

  dbg_trace "blocked!"
  log "blocked"

meta initialize cmdOnceRef : IO.Ref (Option (Task Unit)) ← IO.mkRef none

/--
Like `wait_for_main_cancel_once_async` but for commands. Takes a `num` parameter so that its syntax
can be changed (via `change:`) to trigger re-elaboration. Sends "blocked" as a diagnostic and spawns
an async task that waits for the command's cancellation token to be set.
-/
scoped syntax "wait_for_cancel_once_command" num : command
elab_rules : command
| `(command| wait_for_cancel_once_command $_n) => Elab.Command.liftCoreM do
  let prom ← IO.Promise.new
  if let some t := (← cmdOnceRef.modifyGet (fun old => (old, old.getD prom.result!))) then
    IO.wait t
    return
  let some cancelTk := (← read).cancelTk? | unreachable!
  let act ← Core.wrapAsyncAsSnapshot (cancelTk? := none) fun _ => do
    while true do
      if (← cancelTk.isSet) then
        break
      IO.sleep 30
    IO.eprintln "cancelled!"
    logInfo "cancelled (should never be visible)"
    prom.resolve ()
    Core.checkInterrupted
  let t ← BaseIO.asTask (act ())
  (Core.logSnapshotTask { stx? := none, task := t, cancelTk? := cancelTk })
  logInfo "blocked"

/-- Registry of label-keyed `Task (Option Unit)` values for use by `mkTestTask` and
`wait_for_test_task`. The stored task is `prom.result?` of the promise returned by
`mkTestTask`; the registry itself does not keep that promise alive, so if no other
reference exists, the promise drops and the task fires `none`. -/
meta initialize testTasksRef : IO.Ref (Std.HashMap String (Task (Option Unit))) ← IO.mkRef {}

/-- Register a fresh test task under `label`, returning the underlying `IO.Promise`.
Returns `none` if a task is already registered under `label`. The caller is responsible
for keeping the returned promise alive and arranging its resolution -- typically by
capturing it in a `cancelTk.onSet` closure that calls `prom.resolve`. -/
meta def mkTestTask (label : String) : BaseIO (Option (IO.Promise Unit)) := do
  let prom ← IO.Promise.new
  testTasksRef.modifyGet fun m =>
    if m.contains label then (none, m) else (some prom, m.insert label prom.result?)

/-- Block until the test task named `label` fires. Prints a diagnostic to stderr if
the underlying promise was dropped without resolution, or if no task is registered for
`label`. The diagnostic uses stderr rather than `throwError` so that the failure is
visible even when this tactic is evaluated inside `try?` (or any other combinator that
swallows tactic errors). -/
scoped syntax "wait_for_test_task " str : tactic
elab_rules : tactic
| `(tactic| wait_for_test_task $label) => do
  let label := label.getString
  match (← testTasksRef.get).get? label with
  | none =>
    IO.eprintln s!"wait_for_test_task: no task registered for {label}"
  | some t =>
    match (← IO.wait t) with
    | some _ => return
    | none   => IO.eprintln s!"wait_for_test_task: task {label} dropped without resolution"

/-- Registry of label-keyed `IO.Promise Unit` for synchronization between cooperating
tactics/elaborators in tests. The promise is kept alive by the ref itself, so
`prom.result?` only fires on explicit `resolveSyncPromise` -- there is no drop signal.
Distinct from `testTasksRef`, which stores only the `Task` side and relies on caller
liveness to detect dropped-without-resolved. -/
meta initialize syncPromisesRef : IO.Ref (Std.HashMap String (IO.Promise Unit)) ← IO.mkRef {}

/-- Return the sync promise for `label`, creating it if no entry exists. All callers
receive the same promise. -/
meta def getSyncPromise (label : String) : BaseIO (IO.Promise Unit) := do
  let fresh ← IO.Promise.new
  syncPromisesRef.modifyGet fun m =>
    match m[label]? with
    | some prom => (prom, m)
    | none      => (fresh, m.insert label fresh)

/-- Resolve the sync promise for `label`. Idempotent (subsequent resolves are no-ops). -/
meta def resolveSyncPromise (label : String) : BaseIO Unit := do
  (← getSyncPromise label).resolve ()

/-- Block until `resolveSyncPromise label` has been called. Direct `IO.wait`, no polling. -/
scoped syntax "wait_for_sync " str : tactic
elab_rules : tactic
| `(tactic| wait_for_sync $label) => do
  let lbl := label.getString
  match (← IO.wait (← getSyncPromise lbl).result?) with
  | some _ => return
  | none   =>
    IO.eprintln s!"wait_for_sync: sync promise {lbl} dropped without resolution"

/--
Tactic for testing cancellation propagation. On the first invocation for a given `<label>`,
prints `<label>: blocked` to stderr, resolves the sync promise `<label>` (so a separate
theorem can gate the runner's `waitFor` on this invocation having actually started), and
loops on `Core.checkInterrupted` until the tactic's cancel token fires (at which point the
loop throws and `finally` resolves the shared task). Subsequent invocations (e.g. on
re-elaboration) wait on that task: they return as soon as the first invocation has actually
exited the loop, and hang otherwise. So if cancellation propagates correctly, the test
completes; if propagation is broken, the second invocation's wait blocks forever and the
test hangs (timeout = failure).
-/
scoped syntax "block_until_cancelled" str : tactic
elab_rules : tactic
| `(tactic| block_until_cancelled $label) => do
  let lbl := label.getString
  match (← mkTestTask lbl) with
  | none =>
    let some t := (← testTasksRef.get).get? lbl | unreachable!
    discard <| IO.wait t
  | some prom =>
    IO.eprintln s!"{lbl}: blocked"
    resolveSyncPromise lbl
    try
      while true do
        Core.checkInterrupted
        IO.sleep 10
    finally
      prom.resolve ()


