import Std.Internal.UV

/-!
A one-shot libuv timer or signal whose promise the caller resolved before it fired (#14202).

`IO.Promise.resolve` is available to whoever holds the promise returned by `next`, so the loop must
treat an already-resolved promise as settled when the timer fires or the signal arrives. Builds
with assertions enabled used to abort in the callback instead.
-/

open Std.Internal.UV

/-- Waits for a later timer; timers fire in order, so the earlier one has fired by then. -/
def settle (ms : UInt64) : IO Unit := do
  let later ← Timer.mk ms false
  discard <| IO.wait (← later.next).result?

#eval show IO Unit from do
  let timer ← Timer.mk 5 false
  let fired ← timer.next
  fired.resolve ()
  settle 50
  -- The timer finished on its own; `next` still hands out the promise the caller resolved.
  unless ← (← timer.next).isResolved do
    throw <| IO.userError "timer promise not resolved"
  timer.stop

#eval show IO Unit from do
  -- Signals cannot be sent with `kill` on Windows.
  if System.Platform.isWindows then return
  -- SIGWINCH, whose default action is to ignore it.
  let signal ← Signal.mk 28 false
  let received ← signal.next
  received.resolve 0
  discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString (← IO.Process.getPID)] }
  settle 200
  match ← IO.wait received.result? with
  | some 0 => pure ()
  | r => throw <| IO.userError s!"unexpected signal result {r}"
  signal.stop
