-- `lake check` re-checks everything in scope, so import only what `run_elab` needs.
import Lean.Elab.BuiltinEvalCommand

/-!
Probes the sandbox of `lake check` from inside the build: elaboration fails if anything the sandbox
is meant to deny succeeds.
-/

def mustFail (what : String) (act : IO Unit) : IO Unit := do
  let escaped ← try act; pure true catch _ => pure false
  if escaped then
    throw <| .userError s!"sandbox escape: {what}"

run_elab show IO Unit from do
  mustFail "wrote to the project directory" <| IO.FS.writeFile "_tmp_escape" ""
  if System.Platform.isOSX then
    mustFail "listed the home directories" <| discard <| System.FilePath.readDir "/Users"
    mustFail "listed the temporary directory" <| discard <| System.FilePath.readDir "/private/tmp"
    mustFail "wrote to the terminal" <| IO.FS.writeFile "/dev/tty" ""
  -- What the build itself needs still works.
  discard <| IO.FS.readFile "lakefile.toml"
  IO.FS.withTempFile fun _ _ => pure ()

theorem comm (n m : Nat) : n + m = m + n := Nat.add_comm n m
