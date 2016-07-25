import data.nat
open tactic nat

attribute zero_add [simp]

example (a : nat) : 0 + a ≤ a :=
by do simp, trace_state, mk_const `le.refl >>= apply

example (a : nat) : 0 + a ≥ a :=
by do simp, trace_state, mk_const `le.refl >>= apply
