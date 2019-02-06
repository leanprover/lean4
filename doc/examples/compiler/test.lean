def Sum (xs : list nat) : nat :=
xs.foldl (+) 0

def foo (n : nat) : string :=
to_string $ Sum (list.iota n)
