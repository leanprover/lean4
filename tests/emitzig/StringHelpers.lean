/-! String helper smoke test for the Zig runtime. -/

def main : IO Unit := do
  let s := "abc"
  IO.println s.length
  let t := "def"
  if s < t then
    IO.println "less"
  else
    IO.println "not less"
