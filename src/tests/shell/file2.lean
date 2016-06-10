import data.nat
check nat
check nat.add_zero
check nat.zero_add
-- check finset

open nat
example (a b : nat) : a = 0 → b = 0 → a = b :=
assume h1 h2, eq.subst (eq.symm h1) (eq.subst (eq.symm h2) (eq.refl 0))
