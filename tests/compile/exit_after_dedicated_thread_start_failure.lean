module
import all Lean.Shell
import Std.Internal.UV

/-!
Exit must not hang after a dedicated task's thread failed to start.

The thread is made to fail by requesting an impossibly large stack. The error message is
platform-specific, so only the exit code is checked. A timer exits with status 2 if exit is instead
still waiting after 3 s.

Not compiled: the error is a C++ exception, which cannot unwind through a compiled `main`.
-/

open Std.Internal.UV

public def main : IO Unit := do
  let timer ← Timer.mk 3000 false
  let fired ← timer.next
  discard <| IO.mapTask (t := fired.result?) (sync := true) fun _ => do
    IO.println "exit is still waiting"
    (← IO.getStdout).flush
    (IO.Process.exit 2 : IO Unit)
  Lean.Internal.setThreadStackSize ((1 : USize) <<< 60)
  discard <| IO.asTask (prio := .dedicated) (pure ())
