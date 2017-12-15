import system.io

variable [io.interface]

def main : io unit := do
  handle ← io.cmd {cmd := "echo", args := ["Hello World!"]},
  io.put_str handle,
  return ()

#eval main
