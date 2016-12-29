open tactic

example (a b c : nat) (f : nat → nat) : f (a + b + c) = f (c + b + a) :=
by cc

example (a b c : nat) (f : nat → nat) : a + b = c → f (c + c) = f (a + b + c) :=
by cc
