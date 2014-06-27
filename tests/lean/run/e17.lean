inductive nat : Type :=
| zero : nat
| succ : nat → nat

inductive list (A : Type) : Type :=
| nil  : list A
| cons : A → list A → list A

inductive int : Type :=
| of_nat : nat → int
| neg : nat → int

coercion of_nat

variables n m : nat
variables i j : int

check cons i (cons i nil)
check cons n (cons n nil)
check cons i (cons n nil)
check cons n (cons i nil)
check cons n (cons i (cons m (cons j nil)))