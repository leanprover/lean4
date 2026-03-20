theorem t1 : True := _
theorem t2 : True := t1

def f (x : Nat) : Nat := x + _

#check f

def g (x : Nat) : Nat :=
  f (x + x)

#eval g 0
