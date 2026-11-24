import Std.Internal.UV

open Std.Internal.UV

/-!
Finalization fails the pending wait on a signal handler but leaves the handler installed, so a
`SIGUSR1` arriving after `main` returns, while a task keeps the program running, does not kill it.
-/

def main : IO Unit := do
  -- Signals cannot be sent with `kill` on Windows.
  if System.Platform.isWindows then
    IO.println "main returns\nwait: canceled\nsurvived the signal"
    return
  -- SIGUSR1
  let received ← (← Signal.mk 10 false).nextResult
  let pid ← IO.Process.getPID
  discard <| IO.Process.spawn { cmd := "sh", args := #["-c", s!"sleep 0.5; kill -USR1 {pid}"] }
  discard <| IO.asTask (prio := .dedicated) do
    match (← IO.wait received.result?) with
    | some (.error e) => IO.println s!"wait: {if e.isCanceled then "canceled" else toString e}"
    | r => IO.println s!"wait: {if r.isSome then "received" else "dropped"}"
    IO.sleep 1500
    IO.println "survived the signal"
  IO.println "main returns"
