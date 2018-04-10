open tactic

example (a b : nat) : ((a + 1, b).1) = a + 1 :=
by do
  dsimp_target,
  trace_state,
  reflexivity
