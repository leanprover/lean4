import Std.Internal.UV

open Std.Internal.UV

/-!
When `main` returns, libuv stops taking new work before the task manager waits for the tasks that
are still running: a libuv operation they start fails with `UV_ECANCELED`. The event loop keeps
running, so an operation started before `main` returned still completes.
-/

def main : IO Unit := do
  let pending ← (← Timer.mk 300 false).next
  discard <| IO.asTask (prio := .dedicated) do
    -- `main` has returned by then.
    IO.sleep 200
    match ← (do (← Timer.mk 10 false).next).toBaseIO with
    | .ok _ => IO.println "timer started after main returned: started"
    | .error _ => IO.println "timer started after main returned: failed"
    match ← IO.wait pending.result? with
    | some (.ok ()) => IO.println "timer started before main returned: fired"
    | _ => IO.println "timer started before main returned: did not fire"
  IO.println "main returns"
