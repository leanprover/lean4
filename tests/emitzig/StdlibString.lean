import Init.Data.String.Basic
/-! End-to-end smoke test that imports a real stdlib module. -/

def main : IO Unit := do
  let s := "abc"
  IO.println s.length
  let t := "def"
  if s < t then
    IO.println "less"
  else
    IO.println "not less"
