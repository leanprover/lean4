/-! Test that `IO.setStdout` works in emitted Zig executables. -/

def main : IO Unit := do
  let out ← IO.getStdout
  let _ ← IO.setStdout (← IO.getStderr)
  IO.println "redirected"
  let _ ← IO.setStdout out
  IO.println "restored"
