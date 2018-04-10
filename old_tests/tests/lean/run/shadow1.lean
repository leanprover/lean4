variable a : nat

definition f : nat → nat
| (nat.succ a) := a
| nat.zero     := nat.zero

example : f 3 = 2 :=
rfl

definition g : nat → nat
| a := a

example (a : nat) : g a = a :=
rfl

definition h (a : nat) : nat → nat
| a := a

example (a b : nat) : h a b = b :=
rfl

definition o : nat := 0

definition f2 : nat → nat
| o  := 0

example (a : nat) : f2 a = 0 := rfl

definition f3 : nat → nat
| (a+1) := a
| nat.zero  := nat.zero

example : f3 10 = 9 := rfl
