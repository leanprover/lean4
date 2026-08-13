import Std.Async
import Std.Sync.Channel

/-!
Exercises libuv event-loop teardown (`finalize_libuv`) with a `Selectable.one` still pending in a
detached task at process exit.

The select is only pending once the sleep arm has registered, which is what arms the underlying
timer. Detaching the task and exiting immediately would leave that unsynchronized, so the sleep
selector is wrapped to resolve `registered` right after its `registerFn` returns, and the main
computation blocks on that before finishing.
-/

open Std.Async Std

/--
Wraps `s` so that `p` is resolved once `s` has registered its `Waiter`.
-/
def afterRegister (s : Selector α) (p : IO.Promise Unit) : Selector α where
  tryFn := s.tryFn
  registerFn w := do
    s.registerFn w
    p.resolve ()
  unregisterFn := s.unregisterFn

def pendingSelect (registered : IO.Promise Unit) : Async Unit := do
  let ch ← Std.Channel.new (α := Nat)
  let sleeping ← Selector.sleep 3600000
  Selectable.one #[
    .case ch.recvSelector (fun _ => pure ()),
    .case (afterRegister sleeping registered) (fun _ => pure ())
  ]

#eval Async.block do
  let registered ← IO.Promise.new
  discard <| (pendingSelect registered).asTask
  Async.ofPurePromise (pure registered)
