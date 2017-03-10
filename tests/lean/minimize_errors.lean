def f : nat → nat → nat :=
λ a, a

#check f

def g : nat → nat → nat :=
f

#check g

#print g

def h : nat → nat → nat
| x y := g x y + f y x

#print h
