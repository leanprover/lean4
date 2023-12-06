def g (x : Nat) (y : Nat) : Nat :=
  if x < y then
    2 * g (x-1) y -- Error here
  else
    0
termination_by g x y => x
