import Std.Async

/-!
A `Signal.Waiter` whose selector lost a `Selectable.one` must keep listening, so that a signal that
arrives before the next select is still delivered to it. Covers one-shot and repeating waiters.
SIGWINCH is used because its default action is to ignore it.
-/

open Std Async

def receivesBetweenSelects (repeating : Bool) : Async Bool := do
  let waiter ← Signal.Waiter.mk .sigwinch repeating
  let first ← Selectable.one #[
    .case waiter.selector (fun _ => pure true),
    .case (← Selector.sleep 50) (fun _ => pure false)]
  if first then
    throw <| IO.userError "received a signal before one was sent"
  let pid ← IO.Process.getPID
  discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString pid] }
  Async.sleep 200
  let second ← Selectable.one #[
    .case waiter.selector (fun _ => pure true),
    .case (← Selector.sleep 1000) (fun _ => pure false)]
  waiter.stop
  return second

#eval show IO Unit from do
  -- Signals cannot be sent with `kill` on Windows.
  unless System.Platform.isWindows do
    for repeating in [false, true] do
      unless ← (receivesBetweenSelects repeating).block do
        throw <| IO.userError s!"signal sent between selects was lost (repeating := {repeating})"
