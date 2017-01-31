constant foo (a : nat) (b : bool := tt) : nat
axiom fooAx : foo 0 = 0

example : foo 0 = foo 0 tt :=
rfl
