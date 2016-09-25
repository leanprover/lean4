open tactic nat

constant zero_add (a : nat) : 0 + a = a
constant le.refl (a : nat) : a ≤ a
attribute [simp] zero_add

example (a : nat) : 0 + a ≤ a :=
by do simp, trace_state, mk_const `le.refl >>= apply

example (a : nat) : 0 + a ≥ a :=
by do simp, trace_state, mk_const `le.refl >>= apply
