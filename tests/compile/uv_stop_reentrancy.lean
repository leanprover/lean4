import Std.Internal.UV

/-!
`Timer.stop` and `Signal.stop` release the pending promise, and when the handle holds the only
reference this runs a `(sync := true)` continuation inline. A nested `Signal.stop` there must not
release the event loop's reference to the signal a second time, and a nested one-shot `Timer.next`
must not return the promise being freed.
-/

open Std.Internal.UV

/-- Leaves the handle holding the only reference to a pending promise. -/
def arm (next : IO (IO.Promise α)) (onDrop : BaseIO Unit) : IO Unit := do
  let pending ← next
  BaseIO.chainTask (sync := true) pending.result? fun _ => onDrop

/-- SIGWINCH is never sent here; the handler is only armed and stopped. -/
def signalStop : IO Unit := do
  for _ in [0:200] do
    let signal ← Signal.mk 28 false
    arm signal.next (discard signal.stop.toBaseIO)
    signal.stop
    discard <| signal.next

def timerNext : IO Unit := do
  let promises ← IO.mkRef (#[] : Array (IO.Promise Unit))
  for _ in [0:200] do
    let timer ← Timer.mk 3600000 false
    arm timer.next do
      if let .ok p ← timer.next.toBaseIO then
        promises.modify (·.push p)
    timer.stop
  for p in ← promises.get do
    if ← IO.hasFinished p.result? then
      throw <| IO.userError "a stopped timer's promise resolved"

def main : IO Unit := do
  signalStop
  timerNext
  IO.println "exiting"
