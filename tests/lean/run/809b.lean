import algebra.ring data.finset
open finset nat algebra

constant A : Type₁
constants a b : A
axiom decA : decidable_eq A
attribute decA [instance]
notation 5 := a
notation 5 := b

definition foo1 : finset nat :=
'{ 1, 2, 5, 5 }

definition foo2 : finset nat :=
'{ 1, 2, 3 }

definition foo3 : finset nat :=
'{ 1 }

noncomputable definition foo4 : finset A :=
'{ 5, 5, b }
