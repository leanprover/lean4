import Std.Async

/-!
A raw repeating `Std.Internal.UV.Signal` whose promise from `next` its holder resolved, and which is
then dropped, keeps listening until the signal next arrives, as the docs of `Signal.mk` and
`Signal.next` say (#15667): a resolved promise counts as pending until then. Calling `cancel` before
dropping it releases it at once.
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

def resolveAndDrop (cancelFirst : Bool) : IO Unit := do
  let signal ← Signal.mk 28 true
  let pending ← signal.next
  pending.resolve 0
  if cancelFirst then
    signal.cancel

/-- info: (false, true) -/
#guard_msgs in
#eval show IO (Bool × Bool) from do
  if System.Platform.isWindows then return (false, true)
  resolveAndDrop (cancelFirst := false)
  -- Before any signal arrives the handler is still installed.
  let releasedAtOnce ← waitForIdleLoop 50
  sendWinch
  let releasedAfterSignal ← waitForIdleLoop 500
  return (releasedAtOnce, releasedAfterSignal)

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  if System.Platform.isWindows then return true
  resolveAndDrop (cancelFirst := true)
  waitForIdleLoop 50
