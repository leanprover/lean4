import data.nat
open nat

definition foo (a b : nat) := a * b

example (a : nat) : foo a 0 = 0 :=
calc a * 0 = 0 : by rewrite mul_zero
