import logic

definition f {A : Type} {B : Type} (f : A → B → Prop) ⦃C : Type⦄ {R : C → C → Prop} {c : C} (H : R c c) : R c c
:= H

constant g : Prop → Prop → Prop
constant H : true ∧ true

check f g H
