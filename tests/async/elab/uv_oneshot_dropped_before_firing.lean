import Std.Async

/-!
A one-shot timer or signal that is dropped after `next`, keeping only its promise, is freed by the
event loop when it fires. The loop's reference is the last one, so the finalizer runs inside the
callback, before the promise is resolved. That must neither abort (an assertion that the finalizer
only drops settled promises) nor lose the wakeup. `Async.sleep` relies on this for every call.
-/

open Std Async

/-- Starts a one-shot timer and returns only its promise, so the loop holds the last reference. -/
def startDroppedTimer (ms : UInt64) : IO (IO.Promise Unit) := do
  let timer ← Internal.UV.Timer.mk ms false
  timer.next

/-- Same for a one-shot SIGWINCH waiter. -/
def startDroppedSignal : IO (AsyncTask Int) := do
  let waiter ← Signal.Waiter.mk .sigwinch false
  waiter.wait

/-- info: true -/
#guard_msgs in
#eval do
  let promise ← startDroppedTimer 10
  return (← IO.wait promise.result?).isSome

#eval show IO Unit from do
  for _ in [0:20] do
    (Async.sleep 1).block

#eval show IO Unit from do
  -- Signals cannot be sent with `kill` on Windows.
  unless System.Platform.isWindows do
    let task ← startDroppedSignal
    let pid ← IO.Process.getPID
    discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString pid] }
    match ← IO.wait task with
    | .ok _ => pure ()
    | .error e => throw <| IO.userError s!"one-shot signal failed: {e}"
