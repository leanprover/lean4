def tst (n : nat) : nat :=
let xs := list.repeat 1 n in
xs.foldl (+) 0

def perf (n : nat) : io unit :=
do v ← pure $ tst n,
   io.println ("result " ++ to_string v)

def main (xs : list string) : io uint32 :=
timeit "tst" (perf xs.head.to_nat) *>
pure 0
