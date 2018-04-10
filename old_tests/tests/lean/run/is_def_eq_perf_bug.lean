definition f (n : nat) : nat :=
if n = 100000 then 1 else 0

open tactic

example (n : nat) : f 100000 = (if (100000 : nat) = 100000 then 1 else 0) :=
by reflexivity
