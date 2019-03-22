def initX : IO (IO.Ref Nat) :=
IO.mkRef 0

@[init initX] constant x : IO.Ref Nat := default _

def inc : IO Unit :=
do v ← x.get,
   x.set (v+1),
   IO.println (">> " ++ toString v)

def main (xs : List String) : IO Unit :=
do let n := xs.head.toNat,
   n.mrepeat (λ _, inc)
