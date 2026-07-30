import Std.Async
import Std.Sync.Channel

/-!
Exercises libuv event-loop teardown (`finalize_libuv`) with a `Selectable.one` still pending in a
detached task at process exit.
-/

open Std.Async Std

def pendingSelect : Async Unit := do
  let ch ← Std.Channel.new (α := Nat)
  Selectable.one #[
    .case ch.recvSelector (fun _ => pure ()),
    .case (← Selector.sleep 3600000) (fun _ => pure ())
  ]

#eval Async.block do
  discard <| pendingSelect.asTask
  pure ()
