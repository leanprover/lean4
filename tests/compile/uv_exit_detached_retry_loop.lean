import Std.Async

/-!
A detached `Async` loop that retries on errors must not spin once `main` has returned.

Stopping the event loop used to drop the pending `sleep` promise, failing it. Every retry then
failed at once because the loop was gone, and the loop recursed until the stack overflowed.
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
