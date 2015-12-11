import data.nat
open nat

constant f : nat → nat
definition g (a : nat) := a


example (a b : nat) : a + 0 = 0 + g b → f (f b) = f (f a) :=
suppose a + 0 = 0 + g b,
assert a = b, by unfold g at *; simp,
by simp

attribute g [reducible]
example (a b : nat) : a + 0 = 0 + g b → f (f b) = f (f a) :=
by simp
