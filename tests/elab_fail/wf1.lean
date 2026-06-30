def g (x : Nat) (y : Nat) : Nat :=
  if x < y then
    2 * id (g (x-1)) y
  else
    0
