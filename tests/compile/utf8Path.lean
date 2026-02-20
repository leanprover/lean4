/-! Lean executables should be able to handle UTF 8 paths. -/

def main : IO Unit := do
  assert! (← System.FilePath.pathExists "utf8Path.lean.英語")
