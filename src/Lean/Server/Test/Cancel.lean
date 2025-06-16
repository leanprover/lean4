/-
Copyright (c) 2025 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Sebastian Ullrich
-/
prelude
import Lean.Elab.Tactic.Basic

/-!
Helpers for testing cancellation in interactive tests. Put here because of `initialize` restrictions
and to avoid repeated elaboration overhead per test.
-/

namespace Lean.Server.Test.Cancel

initialize onceRef : IO.Ref (Option (Task Unit)) ← IO.mkRef none

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

-- can't use a naked promise in `initialize` as marking it persistent would block
initialize unblockedCancelTk : IO.CancelToken ← IO.CancelToken.new

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
    if (← unblockedCancelTk.isSet) then
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
      if (← unblockedCancelTk.isSet) then
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
  unblockedCancelTk.set

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
