import Std.Internal.UV

/-!
One-shot timer and signal callbacks resolved their promise and only then stopped the handle and
released the event loop's reference. A `(sync := true)` continuation runs inside that resolve, on
the loop thread; a `cancel` or `stop` from it released the loop's reference as well, so the callback
released it a second time and used the freed handle.
-/

open Std.Internal.UV

def timerFromCallback (useStop : Bool) : IO Unit := do
  for _ in [0:200] do
    let timer ← Timer.mk 1 false
    let fired ← timer.next
    BaseIO.chainTask (sync := true) fired.result? fun _ => do
      let _ ← (if useStop then timer.stop else timer.cancel : IO _).toBaseIO
    let _ ← IO.wait fired.result?

/--
Sends SIGWINCH, whose default action is to ignore it, to a one-shot signal handler. `received` stays
referenced by the main thread, which only waits on `done`.
-/
def signalFromCallback (useStop : Bool) : IO Unit := do
  let pid ← IO.Process.getPID
  for _ in [0:30] do
    let signal ← Signal.mk 28 false
    let received ← signal.next
    let done ← IO.Promise.new
    BaseIO.chainTask (sync := true) received.result? fun _ => do
      let _ ← (if useStop then signal.stop else signal.cancel : IO _).toBaseIO
      done.resolve ()
    discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString pid] }
    let _ ← IO.wait done.result?
    let _ ← received.isResolved

def main : IO Unit := do
  timerFromCallback (useStop := false)
  timerFromCallback (useStop := true)
  -- Signals cannot be sent with `kill` on Windows.
  unless System.Platform.isWindows do
    signalFromCallback (useStop := false)
    signalFromCallback (useStop := true)
  IO.println "exiting"
