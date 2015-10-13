import data.nat
open nat

example (a b : nat) (f : nat → nat) (h : f (succ a) = 0) : f (a+1) = 0 :=
by rewrite [add_one, h]

example (a b : nat) (f : nat → nat) (h : f (succ a) = 0) : f (a+1) = 0 :=
by krewrite h

definition g (a : nat) := a + 1
definition h (a : nat) := a

example (a b : nat) (f : nat → nat) (h : f (g (h a)) = 0) : f (a+1) = 0 :=
by krewrite h
