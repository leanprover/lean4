def badLt (a b : Nat) : Bool :=
a != b

def main : IO Unit :=
let xs := [1, 2].toArray;
IO.println $ xs.qsort badLt
