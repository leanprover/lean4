import Std.Internal.UV

/-!
`Timer.cancel` and `Signal.cancel` released the pending promise before clearing the field holding
it. When the handle held the only reference, that release resolved the promise's `result?` to `none`
and ran a `(sync := true)` continuation inline, which re-entered `cancel` and found the handle still
running with the stale field. For a one-shot handle it then released the event loop's reference to
the handle object a second time, which this test detects.
-/

open Std.Internal.UV

/-- Leaves the handle holding the only reference to a pending promise. -/
def arm (next : IO (IO.Promise α)) (cancel : IO Unit) : IO Unit := do
  let pending ← next
  BaseIO.chainTask (sync := true) pending.result? fun _ => do
    let _ ← cancel.toBaseIO

def timerCancel : IO Unit := do
  for _ in [0:200] do
    let timer ← Timer.mk 3600000 false
    arm timer.next timer.cancel
    timer.cancel

/-- SIGWINCH is never sent here; the handler is only armed and cancelled. -/
def signalCancel : IO Unit := do
  for _ in [0:200] do
    let signal ← Signal.mk 28 false
    arm signal.next signal.cancel
    signal.cancel

def main : IO Unit := do
  timerCancel
  signalCancel
  IO.println "exiting"
