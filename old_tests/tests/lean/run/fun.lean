open function bool


constant f : nat → bool
constant g : nat → nat

#check f ∘ g ∘ g

#check (id : nat → nat)

constant h : nat → bool → nat

#check swap h
#check swap h ff nat.zero

#check (swap h ff nat.zero : nat)

constant f1 : nat → nat → bool
constant f2 : bool → nat

#check (f1 on f2) ff tt
