import Std.Async

/-!
Lifetime of a raw repeating `Std.Internal.UV.Signal` (#15667): the event loop keeps it alive and
listening exactly while a promise from `next` is pending. Dropped with a pending promise, it stays
until the signal arrives and is freed then; dropped with nothing pending (after a delivery, after a
signal that arrived between waits, after `cancel`, after `stop`), it is freed at once. Also checks
that a signal arriving with no promise pending makes the following `next` return a promise that is
already resolved, and that `next` after `stop` returns a promise that is never resolved.

To know that the loop has handled a SIGWINCH, each test waits on a second repeating SIGWINCH signal:
libuv dispatches one signal to all of its handles in the same loop iteration, under the loop lock.
-/

open Std.Internal.UV

/-- Waits up to `n * 10` ms for the event loop to have no live handles. -/
def waitForIdleLoop : Nat → IO Bool
  | 0 => return !(← Loop.alive)
  | n + 1 => do
    if ← Loop.alive then
      IO.sleep 10
      waitForIdleLoop n
    else
      return true

/-- Sends SIGWINCH, whose default action is to be ignored, to this process. -/
def sendWinch : IO Unit := do
  discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString (← IO.Process.getPID)] }

/-- Sends SIGWINCH and returns once the event loop has dispatched it to every SIGWINCH handle. -/
def sendWinchAndSettle : IO Unit := do
  let barrier ← Signal.mk 28 true
  let delivered ← barrier.next
  sendWinch
  unless (← IO.wait delivered.result?) == some 28 do
    throw <| IO.userError "barrier signal not delivered"

def check (cond : Bool) (msg : String) : IO Unit :=
  unless cond do throw <| IO.userError msg

/-- Starts a repeating signal and returns only its pending promise. -/
def startDroppedRepeating : IO (IO.Promise Int) := do
  let signal ← Signal.mk 28 true
  signal.next

-- A repeating signal dropped with a pending promise stays alive until it delivers, then is freed.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  check (← waitForIdleLoop 500) "loop not idle at start"
  let pending ← startDroppedRepeating
  IO.sleep 100
  check (← Loop.alive) "dropped signal with a pending promise stopped listening"
  check (!(← pending.isResolved)) "pending promise resolved without a signal"
  sendWinch
  check ((← IO.wait pending.result?) == some 28) "pending promise not resolved by the signal"
  check (← waitForIdleLoop 500) "signal not freed after delivering to its last promise"

-- A signal that arrived with nothing pending is kept, and the next `next` reports it at once.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  check (← waitForIdleLoop 500) "loop not idle at start"
  let signal ← Signal.mk 28 true
  let first ← signal.next
  sendWinch
  check ((← IO.wait first.result?) == some 28) "first promise not resolved"
  sendWinchAndSettle
  let second ← signal.next
  check (← second.isResolved) "a signal between two waits did not resolve the following `next` at once"
  check ((← IO.wait second.result?) == some 28) "second promise has the wrong value"
  let third ← signal.next
  check (!(← third.isResolved)) "a kept signal was reported twice"
  signal.stop
  check (← waitForIdleLoop 500) "loop not idle after stop"

/-- Dropped while a signal is kept (received with nothing pending), it is freed at once. -/
def keepReceivedThenDrop : IO Unit := do
  let signal ← Signal.mk 28 true
  let first ← signal.next
  sendWinch
  discard <| IO.wait first.result?
  sendWinchAndSettle

#eval show IO Unit from do
  if System.Platform.isWindows then return
  check (← waitForIdleLoop 500) "loop not idle at start"
  keepReceivedThenDrop
  check (← waitForIdleLoop 500) "signal with a kept delivery not freed once dropped"

/-- `cancel` then drop: the loop lets go of it and the finalizer closes the handle. -/
def cancelThenDrop : IO Unit := do
  let signal ← Signal.mk 28 true
  discard <| signal.next
  signal.cancel

#eval show IO Unit from do
  if System.Platform.isWindows then return
  check (← waitForIdleLoop 500) "loop not idle at start"
  cancelThenDrop
  check (← waitForIdleLoop 500) "cancelled signal still listening after it was dropped"

-- After `cancel` it keeps listening: a signal that arrives is reported by the following `next`.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  check (← waitForIdleLoop 500) "loop not idle at start"
  let signal ← Signal.mk 28 true
  discard <| signal.next
  signal.cancel
  sendWinchAndSettle
  let afterCancel ← signal.next
  check (← afterCancel.isResolved) "signal after `cancel` not reported by the following `next`"
  signal.stop
  check (← waitForIdleLoop 500) "loop not idle after stop"

-- `stop` then `next`: the promise is never resolved, and the signal no longer listens.
#eval show IO Unit from do
  if System.Platform.isWindows then return
  check (← waitForIdleLoop 500) "loop not idle at start"
  let signal ← Signal.mk 28 true
  let beforeStop ← signal.next
  signal.stop
  check (!(← Loop.alive)) "stopped signal still listening"
  let afterStop ← signal.next
  sendWinchAndSettle
  check (!(← beforeStop.isResolved)) "promise pending at `stop` was resolved"
  check (!(← afterStop.isResolved)) "promise from `next` after `stop` was resolved"
  -- Nothing resolves it, so dropping it is the only way its result finishes.
  let result := (← signal.next).result?
  check ((← IO.wait result) == none) "dropped promise from `next` after `stop` has a value"
  check (← waitForIdleLoop 500) "loop not idle after stop"
