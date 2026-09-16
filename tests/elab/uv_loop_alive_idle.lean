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
  -- Lets the loop finish anything a stop leaves behind, e.g. closing a handle that was freed.
  IO.sleep 100
  if ← Loop.alive then
    throw <| IO.userError "alive after the timer was stopped"
  discard <| timer.next
