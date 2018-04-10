def f : nat → option nat → nat
| a none     := a
| a (some b) := a + b

example (a b : nat) : f a b = a + b :=
rfl

example (a b : nat) : f a b = f a (some b) :=
rfl

example : f 1 (1:nat) = 2 :=
rfl
