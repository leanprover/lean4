import Std.Internal.UV

/-!
`Loop.alive` reports whether the event loop has anything to do: it is `false` while nothing is
pending, `true` while a timer runs, and `false` again once the timer is stopped.
-/

open Std.Internal.UV

#eval show IO Unit from do
  if ← Loop.alive then
    throw <| IO.userError "alive with nothing pending"
  let timer ← Timer.mk 100000 false
  discard <| timer.next
  unless ← Loop.alive do
    throw <| IO.userError "not alive while a timer runs"
  timer.stop
  if ← Loop.alive then
    throw <| IO.userError "alive after the timer was stopped"
  -- Keeps `timer` referenced until here, so its finalizer does not close the handle before the
  -- check above and leave it in the loop's closing list.
  discard <| timer.next
