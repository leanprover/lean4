import Std.Async

/-!
A detached `Async` loop that retries on errors must not spin once `main` has returned.

Its `sleep` is still pending when the event loop is torn down, and must stay pending rather than
fail: a failed sleep would be retried at once, every retry would fail because the loop is gone, and
the loop would recurse until the stack overflowed.
-/

open Std.Async

partial def heartbeat (retries : IO.Ref Nat) : Async Unit := do
  try
    sleep 1000
  catch _ =>
    retries.modify (· + 1)
  heartbeat retries

def main : IO Unit := do
  let retries ← IO.mkRef 0
  discard <| (heartbeat retries).asTask
  IO.sleep 100
  IO.println "exiting"
