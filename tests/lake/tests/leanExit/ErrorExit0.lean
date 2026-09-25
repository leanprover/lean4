import Lean

open Lean Elab Command in
-- Lean will not reliably report messages before an early exit
-- via `IO.Process.exit`, so we fabricate the desired behavior.
-- `#exit` is reliable, but it does not accept an exit code.
run_cmd
  let log ← liftCoreM do
    logError "Type mismatch"
    Core.getAndEmptyMessageLog
  -- We escape `run_cmd` capturing output by spawning a task
  -- https://github.com/leanprover/lean4/issues/426
  -- If fixed, stdout could also be hackily acquired on import by
  -- `initialize realStdout : IO.FS.Stream ← IO.getStdout`
  let t ← IO.asTask <| log.unreported.forM fun msg => do
    IO.println (← msg.toJson).compress
  IO.ofExcept (← IO.wait t)
  IO.Process.exit (α := Unit) 0
