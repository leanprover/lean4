module

import Std.Internal.UV.Signal

/-!
Tests that a signal handler can retry after libuv rejects starting it.
-/

open Std.Internal.UV

def startFails (signal : @& Signal) : IO Bool := do
  try
    discard signal.next
    return false
  catch _ =>
    return true

def test : IO (Bool × Bool) := do
  let signal ← Signal.mk 0 false
  let first ← startFails signal
  let second ← startFails signal
  signal.cancel
  return (first, second)

/-- info: (true, true) -/
#guard_msgs in
#eval test
