import Std.Async

/-!
A program that exits while libuv still watches child processes exits cleanly: the teardown of the
event loop at exit closes their handles. Covered: a running child whose `Child` is still referenced,
an exited child whose `Child` is still referenced, and a running child whose `Child` was dropped,
which only the loop still knows.

Each `cat` runs until its stdin closes, which happens when this process exits.
-/

open Std.Internal.UV

def main : IO Unit := do
  let running ← IO.Process.spawn { cmd := "cat", stdin := .piped }
  let exited ← IO.Process.spawn { cmd := "sh", args := #["-c", "exit 3"] }
  IO.println s!"exited with {← exited.wait}"

  let (stdin, dropped) ← (← IO.Process.spawn { cmd := "cat", stdin := .piped }).takeStdin
  if (← dropped.tryWait).isSome then
    throw <| IO.userError "the dropped child exited before exit, so the test no longer covers it"

  -- The continuation of a timer that is still pending at exit keeps these referenced. If it ever runs,
  -- the dropped `cat` echoes what it writes.
  let timer ← Timer.mk 3600000 false
  let fired ← timer.next
  discard <| IO.mapTask (fun _ => stdin.putStrLn s!"kept {running.pid} {exited.pid}") fired.result?
  IO.println "exiting"
