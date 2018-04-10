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

noncomputable def foo : nat → nat → nat :=
g

example : foo = (λ (a : nat), g a 10) :=
rfl

example : (λ (a : nat), g a 10) = g :=
rfl

example : g = (λ (a : nat), g a 10) :=
rfl

constant h (a : nat) (b := 10) (c : int) (d := 20) (v : bool) (w : char) : nat

example : h = (λ x y, h x 10 y 20) :=
rfl

example : (λ x y, h x 10 y 20) = h :=
rfl

noncomputable example : nat → int → bool → char → nat :=
h
