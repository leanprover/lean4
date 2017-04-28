import system.io

variable [io.interface]

def main : io unit := do
  out ← io.cmd {cmd := "echo", args := ["Hello World!"]},
  io.put_str out,
  return ()

#eval main
