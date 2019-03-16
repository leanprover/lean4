def g (a : nat) (n : nat) : list nat :=
let xs := list.repeat a n in
xs.map (+2)

def h (xs : list nat) : nat :=
xs.foldl (+) 0

def rep (n : nat) : nat :=
n.repeat (λ i r, h (g i n)) 0

def act (n : nat) : io unit :=
io.println (to_string (rep n))

def main : io uint32 :=
act 5000 *> pure 0
