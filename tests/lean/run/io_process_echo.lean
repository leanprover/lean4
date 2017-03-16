import system.io
import system.process

open process

variable [io.interface]

def main : io unit := do
  out ← io.cmd "echo" ["Hello World!"],
  io.put_str out,
  return ()

#eval main
