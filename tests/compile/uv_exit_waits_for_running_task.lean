import Std.Internal.UV

/-!
Returning from `main` waits for the running tasks with the event loop still up, so a task blocked
on a libuv promise completes once that promise resolves.

Stopping the loop before the tasks finished used to leave the promise pending forever while the
task kept it referenced: the task never woke, and the process waited for it forever.
-/

open Std.Internal.UV

def main : IO Unit := do
  let timer ← Timer.mk 200 false
  let fired ← timer.next
  let started ← IO.Promise.new
  let _ ← IO.asTask do
    started.resolve ()
    let woke ← IO.wait fired.result?
    IO.println s!"woke: {woke.isSome}"
    -- Keeps `fired` referenced across the wait.
    fired.resolve ()
  discard <| IO.wait started.result?
