/-! Lean executables should be able to handle UTF 8 paths. -/

def main : IO Unit := do
  assert! (← System.FilePath.pathExists "../lean/run/utf8英語.lean")
