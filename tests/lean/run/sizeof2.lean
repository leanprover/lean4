open tactic

example : sizeof (λ a : nat, a) = 0 :=
rfl

example : sizeof Type = 0 :=
rfl

example : sizeof Prop = 0 :=
rfl

example (p : Prop) (H : p) : sizeof H = 0 :=
rfl

example (A : Type) (a b : A) : sizeof [a, b] = 3 :=
rfl

example : sizeof [(1:nat), 4] = 8 :=
rfl

example : sizeof [tt, ff, tt] = 7 :=
rfl

set_option pp.implicit true

#check sizeof Prop
#check sizeof [tt, ff, tt]
#check λ (A : Type) (a b : A), sizeof [a, b]
