open tactic

example (a b c : nat) (H1 : a = b) (H2 : b = c) : a = c :=
by do
   refine ```(eq.trans H1 _),
   trace_state,
   assumption
