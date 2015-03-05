constant g : nat → nat

definition f [reducible] := g

example (a : nat) (H : f a = a) : g a = a :=
by rewrite H

attribute f [quasireducible]

example (a : nat) (H : f a = a) : g a = a :=
by rewrite H -- error

attribute f [semireducible]

example (a : nat) (H : f a = a) : g a = a :=
by rewrite H -- error

attribute f [reducible]

example (a : nat) (H : f a = a) : g a = a :=
by rewrite H -- error
