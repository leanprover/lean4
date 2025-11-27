/-!
Regression test for issue #11393.
PR #11362 introduced a bug where `addChoice` could panic when `merge` returns `top`.
-/

def test (s : String) : IO Bool := do
  if s.startsWith "x" then return true
  let b ← IO.Process.output {cmd := "true", args := #[]}
  return b.exitCode == 0

def main : IO Unit := do
  let _ ← test ""
  IO.println "ok"
