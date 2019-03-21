open Function Bool


constant f : Nat → Bool := default _
constant g : Nat → Nat := default _

#check f ∘ g ∘ g

#check (id : Nat → Nat)

constant h : Nat → Bool → Nat := default _

#check swap h
#check swap h false Nat.zero

#check (swap h false Nat.zero : Nat)

constant f1 : Nat → Nat → Bool := default _
constant f2 : Bool → Nat := default _

#check (f1 on f2) false true
