--

def f (xs : List Nat) : List Nat :=
  xs.map (fun x => x + 1) [1]
