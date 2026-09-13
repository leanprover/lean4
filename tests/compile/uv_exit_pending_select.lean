import Std.Async
import Std.Sync.Channel

/-!
A `Selectable.one` still pending in a detached task when the program exits. Its waiters reference
each other through the pending sleep promise, so teardown has to keep that promise rather than drop
it; dropping it leaves the whole cycle unreachable, which leak checkers report.

The select is only pending once the sleep arm has registered, which is what arms the underlying
timer, so the sleep selector is wrapped to resolve `registered` right after its `registerFn`
returns, and `main` blocks on that before returning.
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

def main : IO Unit := do
  Async.block do
    let registered ← IO.Promise.new
    discard <| (pendingSelect registered).asTask
    Async.ofPurePromise (pure registered)
  IO.println "exiting"
