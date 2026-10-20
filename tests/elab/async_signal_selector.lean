import Std.Async

/-!
`Signal.Waiter.selector` against a competing sleep: with no signal sent the sleep must win, and once
the process sends itself the signal the waiter must win. Covers one-shot and repeating waiters. Also
checks that `Selectable.tryOne` reports a one-shot waiter that has already received its signal as
ready; `tryFn` used to test whether a task it had just spawned had finished, and so returned `none`.
SIGWINCH is used because its default action is to ignore it.
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

/-- Counts how many of 20 one-shot waiters `tryOne` reports as ready after their signal arrived. -/
def tryOneAfterDelivery : IO Nat := do
  if System.Platform.isWindows then
    return 20
  let pid ← IO.Process.getPID
  let mut ready := 0
  for _ in [0:20] do
    let waiter ← Signal.Waiter.mk .sigwinch false
    let delivered ← waiter.wait
    discard <| IO.Process.output { cmd := "kill", args := #["-WINCH", toString pid] }
    discard <| IO.wait delivered
    let r ← (Selectable.tryOne #[.case waiter.selector (fun _ => pure ())]).block
    waiter.stop
    if r.isSome then
      ready := ready + 1
  return ready

/-- info: 20 -/
#guard_msgs in
#eval tryOneAfterDelivery
