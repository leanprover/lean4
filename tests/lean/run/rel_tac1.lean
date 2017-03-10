open tactic

example (a b : nat) : a = a :=
by reflexivity

example (a : nat) (b : bool) : a == b → b == a :=
by do intros, symmetry, trace_state, assumption

#print "-----------"

example (a : nat) (b : bool) (c : string) : a == b → b == c → a == c :=
by do
  intro_lst [`H1, `H2],
  transitivity,
  trace_state,
  get_local `H1 >>= exact,
  assumption

example (a b : bool) : a == a :=
by reflexivity
