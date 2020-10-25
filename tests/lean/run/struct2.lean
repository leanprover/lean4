

universe u

structure A (α : Type u) :=
(f : (β : Type u) → α → β → α)

set_option pp.all true

structure B (α : Type u) extends A α :=
(x : Nat)
(f := fun β a b => a)

#check B.f._default

#check { x := 10 : B Nat}
