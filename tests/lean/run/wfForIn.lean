inductive Term where
  | app (f : String) (args : List Term)

def printFns : Term → IO Unit
  | Term.app f args => do
     IO.println f
     for h : arg in args do
       have : sizeOf arg < 1 + sizeOf f + sizeOf args := Nat.lt_trans (List.sizeOf_lt_of_mem h) (by simp +arith)
       printFns arg
