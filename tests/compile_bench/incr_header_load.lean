/-!
Bench: time `lean --incr-load=…` reusing a pre-saved snapshot whose header is `import Lean`.
The snapshot is pre-created by `.before.sh` so that the measurement only covers loading,
not the cost of producing the snapshot. The snapshot is read-only and left in place (rather
than deleted here) so it can be reused across this benchmark's repeated invocations.
-/

unsafe def main : IO Unit := do
  let src  : System.FilePath := "_tmp_incr_header_load_src.lean"
  let snap : System.FilePath := "_tmp_incr_header_load.snap"

  let _ ← IO.Process.run {
    cmd  := "lean"
    args := #[s!"--incr-load={snap}", src.toString]
  }
