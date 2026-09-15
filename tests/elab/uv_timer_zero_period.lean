import Std.Internal.UV

/-!
A repeating timer with a 0 ms period keeps ticking instead of firing once. libuv treats a repeat
period of 0 as a one-shot timer, so every promise after the 0th used to stay pending forever.
-/

open Std.Internal.UV

/-- Waits for `p`, failing after 5 s instead of hanging the test. -/
def awaitBounded {α : Type} (what : String) (p : IO.Promise α) : IO Unit := do
  let deadlineTimer ← Timer.mk 5000 false
  let deadline ← deadlineTimer.next
  let resolved ← IO.waitAny [p.result?.map (·.isSome), deadline.result?.map (fun _ => false)]
  deadlineTimer.cancel
  unless resolved do
    throw <| IO.userError s!"{what}: not resolved within 5 s"

#eval show IO Unit from do
  let zero ← Timer.mk 0 true
  for i in [0:5] do
    awaitBounded s!"0 ms period, tick {i}" (← zero.next)
  zero.stop
