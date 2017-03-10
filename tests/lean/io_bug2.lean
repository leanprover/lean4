import system.io
open io

def main : io unit := do
  put_ln "t1",
  (x, y) ← return ((1 : nat), (2 : ℕ)),
  put_ln "t2"

#eval main
