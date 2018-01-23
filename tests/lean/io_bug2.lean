import system.io
open io

def main : io unit := do
  print_ln "t1",
  (x, y) ← return ((1 : nat), (2 : ℕ)),
  print_ln "t2"

#eval main
