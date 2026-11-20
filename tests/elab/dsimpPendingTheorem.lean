import Lean

/-!
Tests that `dsimp` on a term mentioning a theorem does not wait for the proof of that theorem. The
proof below finishes only after a signal that is sent after the `dsimp` call, so it times out if
`dsimp` waits for it.
-/

open Lean Elab Command Tactic

run_cmd do
  let dir ← IO.FS.createTempDir
  elabCommand (← `(def $(mkIdent `signalDir) : System.FilePath := $(quote dir.toString)))

def signalFile : System.FilePath := signalDir / "signal"

elab "wait_for_signal" : tactic => do
  for _ in [0:300] do
    if ← signalFile.pathExists then return
    IO.sleep 100
  throwError "timeout: a later command waited for this proof"

/-- Like `run_cmd`, which waits for all earlier declarations in order to check for `sorry`. -/
elab "send_signal" : command => IO.FS.writeFile signalFile ""

theorem pendingLt : 0 < 1 := by wait_for_signal; decide

example : (⟨0, pendingLt⟩ : Fin 1).val = 0 := by dsimp

send_signal

run_cmd IO.FS.removeDirAll signalDir
