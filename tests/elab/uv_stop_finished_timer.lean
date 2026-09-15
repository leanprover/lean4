import Std.Internal.UV

/-!
`stop` on a one-shot timer that has already fired is a no-op: `next` keeps returning the resolved
promise. `stop` used to drop that promise even though the timer was no longer running, so a later
`next` handed out a fresh promise that is never resolved.
-/

open Std.Internal.UV

/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  let timer ← Timer.mk 1 false
  let fired ← timer.next
  discard <| IO.wait fired.result?
  timer.stop
  let again ← timer.next
  again.isResolved
