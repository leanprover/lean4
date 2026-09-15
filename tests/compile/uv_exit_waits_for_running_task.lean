import Std.Internal.UV

/-!
Returning from `main` waits for the running tasks with the event loop still up, so a task blocked
on a libuv promise completes once that promise resolves.

If the loop stopped first, the promise would stay pending while the task kept it referenced, and
the process would wait for that task forever.
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
