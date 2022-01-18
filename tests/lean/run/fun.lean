open Function Bool


constant f : Nat → Bool := default
constant g : Nat → Nat := default

#check f ∘ g ∘ g

#check (id : Nat → Nat)

constant h : Nat → Bool → Nat := default


constant f1 : Nat → Nat → Bool := default
constant f2 : Bool → Nat := default
