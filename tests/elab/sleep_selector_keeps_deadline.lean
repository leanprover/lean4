import Std.Async

/-!
Selecting on a `Sleep` must not restart it: a `Sleep` used as a deadline across several
`Selectable.one` calls fires once its duration has elapsed since it started.
-/

open Std Async

#eval show IO Unit from do
  let won ← (do
    let deadline ← Sleep.mk 300
    let mut won := false
    for _ in [0:20] do
      let tick ← Selector.sleep 50
      if ← Selectable.one #[
          .case deadline.selector (fun _ => pure true),
          .case tick (fun _ => pure false)] then
        won := true
        break
    return won : Async Bool).block
  unless won do
    throw <| IO.userError "the deadline never fired while it was being selected on"
