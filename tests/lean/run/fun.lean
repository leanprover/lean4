open Function Bool


constant f : Nat → Bool := arbitrary
constant g : Nat → Nat := arbitrary

#check f ∘ g ∘ g

#check (id : Nat → Nat)

constant h : Nat → Bool → Nat := arbitrary


constant f1 : Nat → Nat → Bool := arbitrary
constant f2 : Bool → Nat := arbitrary
