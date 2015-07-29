open nat

axiom n : nat

definition f (x : nat) :=  -- Error this is not computable
x + n

noncomputable definition f (x : nat) := x + n
