open tactic nat

constant zadd (a : nat) : 0 + a = a
constant le.refl (a : nat) : a ≤ a
attribute [simp] zadd

example (a : nat) : 0 + a ≤ a :=
by do simp

example (a : nat) : 0 + a ≥ a :=
by do simp
