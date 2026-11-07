import Std.Internal.UV

/-!
Regression guard for repeating timers used from re-entrant and concurrent callers.

A `(sync := true)` continuation of a repeating timer's promise runs inside the firing callback's
resolve, and cancels, re-arms and stops the timer from there.

`Timer.next` must return the promise it read under the event loop lock rather than reading
`m_promise` again after unlocking, when a concurrent `cancel` may have cleared it. The promises it
creates are refcounted from the loop thread as well, so they must be marked multi-threaded.
-/

open Std.Internal.UV

/-- Cancels and re-arms a repeating timer from inside its own firing callback. -/
def repeatingTimerFromCallback : IO Unit := do
  for _ in [0:200] do
    let timer ← Timer.mk 1 true
    let fired ← timer.next
    BaseIO.chainTask (sync := true) fired.result? fun _ => do
      let _ ← (timer.cancel : IO _).toBaseIO
      let _ ← (timer.next : IO _).toBaseIO
      let _ ← (timer.stop : IO _).toBaseIO
      pure ()
    let _ ← IO.wait fired.result?

/--
Races `next` against `cancel` on a shared repeating timer. The promises are deliberately dropped
rather than awaited: `cancel` orphans the outstanding one, so waiting on it would block forever.
-/
def timerNextRacesCancel : IO Unit := do
  for _ in [0:100] do
    let timer ← Timer.mk 1 true
    let arming ← IO.asTask do
      for _ in [0:200] do
        let _ ← timer.next
        pure ()
    let cancelling ← IO.asTask do
      for _ in [0:200] do
        timer.cancel
    IO.ofExcept (← IO.wait arming)
    IO.ofExcept (← IO.wait cancelling)
    timer.stop

def main : IO Unit := do
  repeatingTimerFromCallback
  timerNextRacesCancel
  IO.println "exiting"
