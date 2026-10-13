import Std.Async

/-!
Checks that a repeating timer or signal that nothing waits on stops once it is dropped without `stop`:
the event loop holds no reference to it once its last promise has resolved.
-/

open Std Async Std.Internal.UV

/-- Waits up to `n * 10` ms for the event loop to have no live handles. -/
def waitForIdleLoop : Nat → IO Bool
  | 0 => return !(← Loop.alive)
  | n + 1 => do
    if ← Loop.alive then
      IO.sleep 10
      waitForIdleLoop n
    else
      return true

def tickRawTimer (period : UInt64) : IO Unit := do
  let timer ← Timer.mk period true
  discard <| IO.wait (← timer.next).result?
  discard <| IO.wait (← timer.next).result?

/-- Sends SIGWINCH, whose default action is to be ignored, to this process. -/
def sendWinch : IO Unit := do
  discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString (← IO.Process.getPID)] }

/-- A repeating signal that delivered once and was then dropped. -/
def deliverRawSignal : IO Unit := do
  let signal ← Signal.mk 28 true
  let delivered ← signal.next
  sendWinch
  discard <| IO.wait delivered.result?

/--
A repeating signal whose second delivery arrives with no promise pending, so that the following
`next` returns a promise that is already resolved.
-/
def receiveBetweenWaits : IO Unit := do
  let signal ← Signal.mk 28 true
  let first ← signal.next
  sendWinch
  discard <| IO.wait first.result?
  sendWinch
  IO.sleep 100
  discard <| IO.wait (← signal.next).result?

/-- A repeating signal whose promise its holder resolved before a signal arrived. -/
def resolveOwnPromise : IO Unit := do
  let signal ← Signal.mk 28 true
  let pending ← signal.next
  pending.resolve 0
  sendWinch

def tickInterval : IO Unit := do
  let interval ← Interval.mk 5
  interval.tick.block
  interval.tick.block

/-- info: true -/
#guard_msgs in
#eval do tickRawTimer 0; waitForIdleLoop 500

/-- info: true -/
#guard_msgs in
#eval do tickInterval; waitForIdleLoop 500

/-- info: true -/
#guard_msgs in
#eval do
  -- `kill` is POSIX-only.
  if System.Platform.isWindows then return true
  deliverRawSignal
  waitForIdleLoop 500

/-- info: true -/
#guard_msgs in
#eval do
  if System.Platform.isWindows then return true
  receiveBetweenWaits
  waitForIdleLoop 500

/-- info: true -/
#guard_msgs in
#eval do
  if System.Platform.isWindows then return true
  resolveOwnPromise
  waitForIdleLoop 500
