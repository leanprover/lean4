import Std.Async

/-!
Checks that a repeating timer that nothing waits on stops once it is dropped without `stop`. The
event loop used to keep it alive and ticking for the rest of the process, every millisecond for a
raw timer with a period of 0.
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
