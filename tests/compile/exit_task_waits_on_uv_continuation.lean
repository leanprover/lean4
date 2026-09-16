import Std.Internal.UV

/-!
Returning from `main` must not hang while a running task waits on a continuation of a libuv promise
that resolves during shutdown.

The workers shut down with the event loop still running, so the timer fires, but its continuation is
queued after the idle workers have exited and nothing runs it. The task's worker then never finishes
and joining it hangs.
-/

open Std.Internal.UV

/-- Exits with status 1 if the process still runs after 5 s. Exit does not wait for a pending timer. -/
def watchdog : IO Unit := do
  let fired ← (← Timer.mk 5000 false).next
  discard <| IO.mapTask (t := fired.result?) (sync := true) fun _ => do
    IO.println "watchdog: timed out"
    (← IO.getStdout).flush
    (IO.Process.exit 1 : IO Unit)

def main : IO Unit := do
  watchdog
  let fired ← (← Timer.mk 300 false).next
  let started ← IO.Promise.new
  discard <| IO.asTask do
    started.resolve ()
    let continuation ← IO.mapTask (fun _ => pure ()) fired.result?
    discard <| IO.wait continuation
    IO.println "continuation ran"
  discard <| IO.wait started.result?
