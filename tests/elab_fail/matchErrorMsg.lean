def f (x : Nat × Nat) : Nat :=
 match x with
 | (0, 0) => 1
 | (x+1, _) => 2
