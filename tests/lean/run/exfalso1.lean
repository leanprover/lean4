open tactic nat

example (a b : nat) : a = 0 → b = 1 → a = b → a + b * b ≤ 10000 :=
by do
  intro_lst [`a0, `a1, `ab],
  exfalso,
  trace_state,
  get_local `a >>= subst,
  get_local `b >>= subst,
  trace_state,
  contradiction
