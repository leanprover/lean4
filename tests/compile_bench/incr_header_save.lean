/-!
Bench: time `lean --incr-header-save=…` on a source whose header is a real `import Lean`.
This measures the cost of compacting and writing the post-import snapshot (plus its
`.deps` sidecar), which is what a downstream `--incr-load` later reuses to skip
re-importing `Lean`.
-/

unsafe def main : IO Unit := do
  let src  : System.FilePath := "_tmp_incr_header_save_src.lean"
  let snap : System.FilePath := "_tmp_incr_header_save.snap"
  let deps := snap.addExtension "deps"

  IO.FS.writeFile src "import Lean\n"

  let _ ← IO.Process.run {
    cmd  := "lean"
    args := #[s!"--incr-header-save={snap}", src.toString]
  }

  let snapSize ← snap.metadata.map (·.byteSize)
  IO.println s!"measurement: snap-size {snapSize} B"

  IO.FS.removeFile src
  IO.FS.removeFile snap
  IO.FS.removeFile deps
