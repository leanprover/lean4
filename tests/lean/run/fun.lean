open Function Bool


constant f : Nat → Bool := arbitrary _
constant g : Nat → Nat := arbitrary _

#check f ∘ g ∘ g

#check (id : Nat → Nat)

constant h : Nat → Bool → Nat := arbitrary _


constant f1 : Nat → Nat → Bool := arbitrary _
constant f2 : Bool → Nat := arbitrary _
