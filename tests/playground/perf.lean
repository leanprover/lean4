def g (a : Nat) (n : Nat) : List Nat :=
let xs := List.repeat a n in
xs.map (+2)

def h (xs : List Nat) : Nat :=
xs.foldl (+) 0

def rep (n : Nat) : Nat :=
n.repeat (λ i r, h (g i n)) 0

def act (n : Nat) : IO Unit :=
IO.println (toString (rep n))

def main : IO UInt32 :=
act 5000 *> pure 0
