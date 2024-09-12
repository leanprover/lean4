def test : IO Unit := do
  let cwd ← IO.Process.getCurrentDir
  IO.println cwd
  IO.Process.setCurrentDir ".."
  let cwd' ← IO.Process.getCurrentDir
  IO.println cwd'
  let actual := cwd'.normalize
  let expected := cwd.normalize.parent.getD
    (cwd.components[0]!.push System.FilePath.pathSeparator)
  unless expected == actual do
    throw <| IO.userError s!"expected {expected}, got {actual}"

-- Ensures this test is idempotent in an interactive session.
def withoutModifyingCurrentDir (x : IO α) : IO α := do
  let cwd ← IO.Process.getCurrentDir
  try x finally IO.Process.setCurrentDir cwd

#eval withoutModifyingCurrentDir test
