import Lean.CompactedRegion

open Lean

/-!
Header-mismatch fallback: save a snapshot from a file whose header is `import Lean`, then load
it on a file with a different (empty) header. The mismatch must be detected and the loader must
fall through to the regular import path, rather than silently reusing an incompatible snapshot.

The loader source redefines `Lean.Elab.runFrontend`, a constant only present when `import Lean`
is in scope (note: a few `Lean.*` names like `Lean.Name` are bootstrapped into `Init` and so
exist even without `import Lean`). Under the *correct* fallback path the env is fresh
(auto-imported `Init` only), `Lean.Elab.runFrontend` is a brand-new name, and the def succeeds.
Under *incorrect* reuse the snapshot's env already contains `Lean.Elab.runFrontend`, and the
def would error as a redeclaration.
-/
unsafe def main : IO Unit := do
  let snap : System.FilePath := "./_tmp_incr_mismatch.snap"
  let deps := snap.addExtension "deps"
  let srcSave : System.FilePath := "./_tmp_incr_mismatch_save.lean"
  let srcLoad : System.FilePath := "./_tmp_incr_mismatch_load.lean"

  IO.FS.writeFile srcSave "import Lean\n"
  IO.FS.writeFile srcLoad "def Lean.Elab.runFrontend : Nat := 1\n"

  let baseArgs : Array String := #[
    "-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true"]

  let saveOut ← IO.Process.output {
    cmd := "lean"
    args := baseArgs ++ #[s!"--incr-header-save={snap}", srcSave.toString]
  }
  unless saveOut.exitCode = 0 do
    throw <| IO.userError
      s!"`--incr-header-save` failed (exit {saveOut.exitCode}):\nstdout:\n{saveOut.stdout}\nstderr:\n{saveOut.stderr}"

  let loadOut ← IO.Process.output {
    cmd := "lean"
    args := baseArgs ++ #[s!"--incr-load={snap}", srcLoad.toString]
  }
  unless loadOut.exitCode = 0 do
    throw <| IO.userError
      s!"`--incr-load` on mismatched header crashed (exit {loadOut.exitCode}):\nstdout:\n{loadOut.stdout}\nstderr:\n{loadOut.stderr}"

  IO.FS.removeFile snap
  IO.FS.removeFile deps
  IO.FS.removeFile srcSave
  IO.FS.removeFile srcLoad
