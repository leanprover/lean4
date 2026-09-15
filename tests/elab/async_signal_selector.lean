import Std.Async

/-!
`Signal.Waiter.selector` against a competing sleep (#14202): with no signal sent the sleep must win,
and once the process sends itself the signal the waiter must win. Covers one-shot and repeating
waiters. SIGWINCH is used because its default action is to ignore it.
-/

open Std Async

def race (repeating : Bool) (sendSignal : Bool) : Async Bool := do
  let waiter ← Signal.Waiter.mk .sigwinch repeating
  if sendSignal then
    let pid ← IO.Process.getPID
    discard <| IO.asTask do
      IO.sleep 100
      discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString pid] }
  let sleep ← Selector.sleep (if sendSignal then 10000 else 200)
  let won ← Selectable.one #[
    .case waiter.selector (fun _ => pure true),
    .case sleep (fun _ => pure false)]
  waiter.stop
  return won

def test : IO (List Bool) := do
  -- Signals cannot be sent with `kill` on Windows; report the expected outcome.
  if System.Platform.isWindows then
    return [false, false, true, true]
  (do return [← race false false, ← race true false, ← race false true, ← race true true]
    : Async (List Bool)).block

/-- info: [false, false, true, true] -/
#guard_msgs in
#eval test
