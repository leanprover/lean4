import data.nat.basic
open nat

definition pred (a : nat) : nat :=
nat.cases_on a
  zero
  (fun a₁, a₁)

example : pred 1 = 0 :=
rfl

print definition pred
