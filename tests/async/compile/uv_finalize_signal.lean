import Std.Async.Basic
import Std.Internal.UV

open Std Async Internal.UV

/-!
A signal that the program handles must not kill it when it arrives while the program finishes.
Finalization fails the pending wait on the handler, but leaves it installed: stopping or closing it
would restore the signal's default action, which for `SIGUSR1` terminates the program. Here the
signal arrives about 0.5 s after `main` returns, while a task keeps the program from exiting.
-/

/-- `SIGUSR1` in the numbering of `Signal`. -/
def sigusr1 : Int32 := 10

def main : IO Unit := do
  -- Signals cannot be sent with `kill` on Windows.
  if System.Platform.isWindows then
    IO.println "main returns"
    IO.println "wait: canceled"
    IO.println "survived the signal"
    return
  let handler ← Signal.mk sigusr1 false
  let received ← handler.nextResult
  let pid ← IO.Process.getPID
  discard <| IO.Process.spawn { cmd := "sh", args := #["-c", s!"sleep 0.5; kill -USR1 {pid}"] }
  discard <| IO.asTask (prio := .dedicated) do
    match (← IO.wait received.result?) with
    | some (.error e) => IO.println s!"wait: {if e.isCanceled then "canceled" else toString e}"
    | some (.ok _) => IO.println "wait: received"
    | none => IO.println "wait: dropped"
    IO.sleep 1500
    IO.println "survived the signal"
  IO.println "main returns"
