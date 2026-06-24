import Lean

/-!
Regression test for `--incr-load` snapshots whose imported module artifacts changed after the
snapshot was saved. Loading such a snapshot must fail instead of reusing stale imported data.
-/

def runLean (leanPath : System.SearchPath) (args : Array String) : IO IO.Process.Output :=
  IO.Process.output { cmd := "lean", args, env := #[("LEAN_PATH", some leanPath.toString)] }

def requireSuccess (what : String) (out : IO.Process.Output) : IO Unit := do
  unless out.exitCode == 0 do
    throw <| IO.userError
      s!"{what} failed (exit {out.exitCode}):\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}"

def cleanup (tmpDir : System.FilePath) : IO Unit := do
  try IO.FS.removeDirAll tmpDir catch _ => pure ()

def main : IO UInt32 := do
  let tmpDir : System.FilePath := "./_tmp_incr_stale_import"
  cleanup tmpDir
  IO.FS.createDirAll tmpDir
  try
    let depSrc := tmpDir / "TmpIncrStaleImportDep.lean"
    let depOlean := tmpDir / "TmpIncrStaleImportDep.olean"
    let src := tmpDir / "Main.lean"
    let snap := tmpDir / "snapshot"
    let baseLeanPath := match (← IO.getEnv "LEAN_PATH") with
      | some paths => System.SearchPath.parse paths
      | none => []
    let leanPath : System.SearchPath := tmpDir :: baseLeanPath
    let baseArgs : Array String := #[
      "-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true"]

    IO.FS.writeFile depSrc "def staleValue : Nat := 1\n"
    requireSuccess "initial dependency build" (← runLean leanPath (baseArgs ++ #[
      "-o", depOlean.toString, depSrc.toString]))

    IO.FS.writeFile src "import TmpIncrStaleImportDep\n#check staleValue\n"
    requireSuccess "`--incr-header-save`" (← runLean leanPath (baseArgs ++ #[
      s!"--incr-header-save={snap}", src.toString]))

    IO.FS.writeFile depSrc "def staleValue : Nat := 2\n"
    requireSuccess "updated dependency build" (← runLean leanPath (baseArgs ++ #[
      "-o", depOlean.toString, depSrc.toString]))

    let loadOut ← runLean leanPath (baseArgs ++ #[s!"--incr-load={snap}", src.toString])
    unless loadOut.exitCode != 0 do
      throw <| IO.userError "`--incr-load` unexpectedly accepted a stale imported module"
    unless (loadOut.stderr.splitOn "incremental snapshot dependency has changed").length > 1 do
      throw <| IO.userError
        s!"`--incr-load` failed for the wrong reason:\nstdout:\n{loadOut.stdout}\nstderr:\n{loadOut.stderr}"
    return 0
  finally
    cleanup tmpDir
