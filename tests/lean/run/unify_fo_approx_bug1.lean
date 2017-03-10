#check ( return (1, 1) : list (nat × nat) )

constant A : Type
constant B : Type

set_option pp.binder_types true
set_option pp.universes true

#check λ (A : Type) (B : Type) (a : A) (b : B), (return (a, b) : list (A × B))

#check λ (A : Type) (B : Type) (C : Type) (a : A) (b : B) (c : C), (return (a, b, a, c) : list (A × B × A × C))
