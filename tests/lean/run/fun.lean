open Function Bool


constant f : Nat → Bool
constant g : Nat → Nat

#check f ∘ g ∘ g

#check (id : Nat → Nat)

constant h : Nat → Bool → Nat

#check swap h
#check swap h ff Nat.zero

#check (swap h ff Nat.zero : Nat)

constant f1 : Nat → Nat → Bool
constant f2 : Bool → Nat

#check (f1 on f2) ff tt
