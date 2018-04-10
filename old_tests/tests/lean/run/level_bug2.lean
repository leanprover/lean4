definition f (a : Type) := Π r : Type, (a → r) → r

definition blah2 {a  : Type} {r  : Type} (sa : f a) (k  : a → r) : sa r k = sa r k :=
rfl
