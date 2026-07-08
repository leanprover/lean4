/-!
Bench: time `lean --incr-load=…` reusing a pre-saved snapshot whose header is `import Lean`.
The snapshot is pre-created by `.before.sh` so that the measurement only covers loading,
not the cost of producing the snapshot.
-/

unsafe def main : IO Unit := do
  let src  : System.FilePath := "_tmp_incr_header_load_src.lean"
  let snap : System.FilePath := "_tmp_incr_header_load.snap"
  let deps := snap.addExtension "deps"

  let _ ← IO.Process.run {
    cmd  := "lean"
    args := #[s!"--incr-load={snap}", src.toString]
  }

  IO.FS.removeFile src
  IO.FS.removeFile snap
  IO.FS.removeFile deps
