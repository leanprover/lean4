import system.io

def main : io unit := do
  put_str_ln "t1",
  (x, y) ← return ((1 : nat), (2 : ℕ)),
  put_str_ln "t2"

vm_eval main
