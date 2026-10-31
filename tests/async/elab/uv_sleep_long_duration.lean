import Std.Async

/-!
A `Sleep` longer than a `UInt64` of milliseconds is clamped rather than wrapped, so it does not fire
early.
-/

open Std Async

#eval show IO Unit from do
  let fired ← (do
    -- 2^64 + 50 ms, which wraps to 50 ms.
    let long ← Sleep.mk ⟨2 ^ 64 + 50⟩
    Selectable.one #[
      .case long.selector (fun _ => pure true),
      .case (← Selector.sleep 500) (fun _ => pure false)] : Async Bool).block
  if fired then
    throw <| IO.userError "a sleep of more than 2^64 ms fired early"
