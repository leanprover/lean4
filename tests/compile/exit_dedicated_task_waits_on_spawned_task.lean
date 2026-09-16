import Std.Internal.UV

/-!
Returning from `main` must not hang while a dedicated task spawns a regular task and waits for it.

The standard workers have already exited when the task is spawned, and waiting from a dedicated task
never adds a worker, so nothing runs the spawned task and exit keeps waiting for the dedicated one.
-/

/-- Exits with status 1 if the process still runs after 5 s. Exit does not wait for a pending timer. -/
def watchdog : IO Unit := do
  let fired ← (← Std.Internal.UV.Timer.mk 5000 false).next
  discard <| IO.mapTask (t := fired.result?) (sync := true) fun _ => do
    IO.println "watchdog: timed out"
    (← IO.getStdout).flush
    (IO.Process.exit 1 : IO Unit)

def main : IO Unit := do
  watchdog
  discard <| IO.asTask (prio := .dedicated) do
    IO.sleep 300
    let spawned ← IO.asTask (pure 42)
    IO.println s!"spawned task: {(← IO.wait spawned).toOption}"
