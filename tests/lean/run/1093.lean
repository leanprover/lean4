open tactic nat

constant zero_add (a : nat) : 0 + a = a
constant le.refl (a : nat) : a ≤ a
attribute zero_add [simp]

example (a : nat) : 0 + a ≤ a :=
by do simp, trace_state, mk_const `le.refl >>= apply

example (a : nat) : 0 + a ≥ a :=
by do simp, trace_state, mk_const `le.refl >>= apply
