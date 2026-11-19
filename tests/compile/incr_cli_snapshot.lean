import Lean.CompactedRegion

open Lean

/-!
End-to-end CLI test of `--incr-save` and `--incr-load`. Saves a snapshot containing two
`#eval`s and loads it on a source where only the *second* eval was changed, asserting that
`Language.Lean.process`'s unchanged-syntax fast path is **command-granular**: the unchanged
first command is reused (no re-print of its marker) while the changed second command is
re-elaborated (new marker prints).
-/
unsafe def main : IO Unit := do
  let snap : System.FilePath := "./_tmp_incr_cli.snap"
  let deps := snap.addExtension "deps"
  let src  : System.FilePath := "./_tmp_incr_cli_src.lean"

  -- Probe re-elaboration via `IO.eprintln`: with `stderrAsMessages=false` the captured-output
  -- replay path is bypassed (`withIsolatedStreams` doesn't capture stderr), so a marker only
  -- appears on actual `#eval` execution, not when a saved snapshot is reused.
  let baseArgs : Array String := #[
    "-DprintMessageEndPos=true", "-Dlinter.all=false", "-DElab.inServer=true",
    "-DstderrAsMessages=false"]
  IO.FS.writeFile src
    "#eval IO.eprintln \"first\"\n\
     #eval IO.eprintln \"second\"\n"

  let saveOut ← IO.Process.output {
    cmd  := "lean"
    args := baseArgs ++ #[s!"--incr-save={snap}", src.toString]
  }
  unless saveOut.exitCode = 0 do
    throw <| IO.userError
      s!"`--incr-save` failed (exit {saveOut.exitCode}):\n\
        stdout:\n{saveOut.stdout}\nstderr:\n{saveOut.stderr}"
  unless (saveOut.stderr.splitOn "first").length > 1 && (saveOut.stderr.splitOn "second").length > 1 do
    throw <| IO.userError
      s!"save run should print both `first` and `second` to stderr (sanity check); got:\n\
        stdout:\n{saveOut.stdout}\nstderr:\n{saveOut.stderr}"

  -- Change only the second command. The first should still be reused; the second re-elaborated.
  IO.FS.writeFile src
    "#eval IO.eprintln \"first\"\n\
     #eval IO.eprintln \"changed\"\n"

  let loadOut ← IO.Process.output {
    cmd  := "lean"
    args := baseArgs ++ #[s!"--incr-load={snap}", src.toString]
  }
  unless loadOut.exitCode = 0 do
    throw <| IO.userError
      s!"`--incr-load` failed (exit {loadOut.exitCode}):\n\
        stdout:\n{loadOut.stdout}\nstderr:\n{loadOut.stderr}"
  if (loadOut.stderr.splitOn "first").length > 1 then
    throw <| IO.userError
      s!"`--incr-load` should reuse the unchanged first `#eval`, but `first` was re-emitted \
        on stderr:\n{loadOut.stderr}"
  unless (loadOut.stderr.splitOn "changed").length > 1 do
    throw <| IO.userError
      s!"`--incr-load` should re-elaborate the changed second `#eval`, but `changed` was \
        not emitted on stderr:\n{loadOut.stderr}"

  IO.FS.removeFile snap
  IO.FS.removeFile deps
  IO.FS.removeFile src
