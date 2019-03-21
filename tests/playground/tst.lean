def tst (n : Nat) : Nat :=
let xs := List.repeat 1 n in
xs.foldl (+) 0

def perf (n : Nat) : IO Unit :=
do v ← pure $ tst n,
   IO.println ("Result " ++ toString v)

def main (xs : List String) : IO UInt32 :=
timeit "tst" (perf xs.head.toNat) *>
pure 0
