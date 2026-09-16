import Std.Internal.UV

/-!
Returning from `main` must not hang while a running task spawns a task and waits for it.

Exit stops spawning workers, and the idle ones exit once the queue is empty. The spawned task is
queued after that, and the only worker left is the one blocked waiting for it.
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
  let started ← IO.Promise.new
  discard <| IO.asTask do
    started.resolve ()
    IO.sleep 300
    let spawned ← IO.asTask (pure 42)
    IO.println s!"spawned task: {(← IO.wait spawned).toOption}"
  discard <| IO.wait started.result?
