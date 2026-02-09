open Function Bool


opaque f : Nat → Bool := default
opaque g : Nat → Nat := default

#check f ∘ g ∘ g

#check (id : Nat → Nat)

opaque h : Nat → Bool → Nat := default


opaque f1 : Nat → Nat → Bool := default
opaque f2 : Bool → Nat := default
