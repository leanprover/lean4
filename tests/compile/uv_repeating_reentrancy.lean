import Std.Internal.UV

/-!
Regression guard for repeating uv handles and for `Timer.next` racing `cancel`.

`handle_timer_event`/`handle_signal_event` resolved `m_promise` while only borrowing it. A
`(sync := true)` continuation runs inside that resolve and a `cancel` from it releases exactly that
reference, so the loop finished resolving a promise it no longer held.

`Timer.next`/`Signal.next` also re-read `m_promise` after releasing the event loop lock, so a
concurrent `cancel` could null the field between the `lean_inc` and the read and hand Lean a null
promise. Those promises were never marked multi-threaded either, even though the loop thread
refcounts them.
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
