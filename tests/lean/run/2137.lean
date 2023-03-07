def makeProc : IO Unit := do
  let child ← IO.Process.spawn {
    cmd := "cat"
    args := #[]
    stdin := .piped
    stdout := .piped
  }
  IO.print (← child.stdout.getLine)

def main (_ : List String) : IO UInt32 := do
  IO.println "test"
  makeProc
  IO.println "done test"

  for _ in [0:6] do
    let _ ← IO.asTask makeProc

  return 0
