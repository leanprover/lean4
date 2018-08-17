import system.io
open io

def main : io unit := do
  println "t1",
  (x, y) ← return ((1 : nat), (2 : ℕ)),
  println "t2"

#eval main
