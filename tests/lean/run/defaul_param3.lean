meta constant f (a : nat) (b : nat := 10) : tactic unit

meta example : tactic unit :=
f 10

constant g (a : nat) (b : nat := 10) (c : nat) : nat

example : g 0 = g 0 10 :=
rfl

noncomputable example : nat :=
g 0 1 2

noncomputable example : nat → nat :=
g 0
