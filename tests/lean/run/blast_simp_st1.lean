import data.nat
open algebra nat

section
open nat
set_option blast.strategy "preprocess" -- make sure simplifier is not used by default

attribute add.comm      [simp]
attribute add.assoc     [simp]
attribute add.left_comm [simp]

example (a b c : nat) : a + b + b + c = c + b + a + b :=
by simp

example (a b c : nat) : a = b → a + c = c + b :=
by simp

definition f : nat → nat := sorry

example (a b c : nat) : f a = f b → f a + c = c + f b :=
by simp

end
