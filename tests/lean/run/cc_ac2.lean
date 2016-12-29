open tactic

example (a b c d : nat) (f : nat → nat → nat) : b + a = d → f (a + b + c) a = f (c + d) a :=
by cc
