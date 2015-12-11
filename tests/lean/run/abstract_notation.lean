import data.nat
open nat

notation `$`:max := abstract by blast end

definition foo (a b : nat) : a + b = b + a ∧ a = 0 + a :=
and.intro $ $

check foo_1
check foo_2
print foo
