-- `lake check` re-checks everything in scope, so import only the module that `run_elab` needs.
import Lean.Elab.BuiltinEvalCommand

/-!
Probes the sandbox of `lake check` from inside the build: elaboration fails if anything the sandbox
is meant to deny succeeds.
-/

def mustFail (action : String) (act : IO Unit) : IO Unit := do
  let escaped ← try act; pure true catch _ => pure false
  if escaped then
    throw <| .userError s!"sandbox escape: {action}"

/-- A file that `test.sh` creates in a directory that the sandbox hides. -/
def secret : System.FilePath := "/private/tmp/_tmp_lake_check_sandbox_secret"

run_elab show IO Unit from do
  mustFail "wrote to the project directory" <| IO.FS.writeFile "_tmp_escape" ""
  if System.Platform.isOSX then
    mustFail "listed the home directories" <| discard <| System.FilePath.readDir "/Users"
    mustFail "listed the temporary directory" <| discard <| System.FilePath.readDir "/private/tmp"
    mustFail "read a hidden file" <| discard <| IO.FS.readFile secret
    -- A hidden file must not become readable under a name in a writable directory.
    for (how, args) in [("hard link", #[]), ("symbolic link", #["-s"])] do
      let link : System.FilePath := ".lake" / "_tmp_link"
      let ln := { cmd := "/bin/ln", args := args ++ #[secret.toString, link.toString] }
      discard <| (IO.Process.output ln).toBaseIO
      mustFail s!"read a hidden file through a {how}" <| discard <| IO.FS.readFile link
      discard <| (IO.FS.removeFile link).toBaseIO
    mustFail "moved a hidden file" <| IO.FS.rename secret (".lake" / "_tmp_moved")
    mustFail "wrote to the terminal" <| IO.FS.writeFile "/dev/tty" ""
  -- The sandbox still allows the accesses that a build needs.
  discard <| IO.FS.readFile "lakefile.toml"
  IO.FS.withTempFile fun _ _ => pure ()

theorem comm (n m : Nat) : n + m = m + n := Nat.add_comm n m
