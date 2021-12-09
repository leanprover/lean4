def f (x : Nat) (y? : Option Nat := none) :=
  if let some y := y? then
    x*y + y
  else
    x

variable (a : Nat)

#check f 1 Nat.zero

#check f 1 a

#check f 1 0
