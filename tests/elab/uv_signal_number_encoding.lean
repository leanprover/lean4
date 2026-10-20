import Std.Async

/-!
A `Signal.Waiter` completes with the signal number in the encoding of `Signal.toInt32`, which is
Linux's, also on platforms whose native number for the signal differs.
-/

open Std Async

#eval show IO Unit from do
  -- Signals cannot be sent with `kill` on Windows.
  if System.Platform.isWindows then return
  let waiter ← Signal.Waiter.mk .sigusr1 false
  let received ← waiter.wait
  let pid ← IO.Process.getPID
  discard <| IO.Process.output { cmd := "kill", args := #["-USR1", toString pid] }
  let signum ← received.block
  unless signum == 10 do
    throw <| IO.userError s!"received signal number {signum}, expected 10"
