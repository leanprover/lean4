/-!
Regression tests for #11393 and #11389
-/

#guard_msgs in
open System in
def loadModuleContent : IO Unit := do
  let lakefile : FilePath := "lakefile.lean"

  if !(← lakefile.pathExists) then
    IO.println "nope"

  discard <| IO.Process.output {
    cmd := "ls", args := #[]
  }

#guard_msgs in
def test (s : String) : IO Bool := do
  if s.startsWith "x" then return true
  let b ← IO.Process.output {cmd := "true", args := #[]}
  return b.exitCode == 0
