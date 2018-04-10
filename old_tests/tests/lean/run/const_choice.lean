open nat

definition mypred (a : nat) : nat :=
nat.cases_on a
  0
  (fun a₁, a₁)

example : mypred 1 = 0 :=
rfl
