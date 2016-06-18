open tactic nat

example (a b : nat) : a = 0 → b = 1 → a = b → a + b * b ≤ 10000 :=
by do
  intro_lst ["a0", "a1", "ab"],
  exfalso,
  trace_state,
  subst "a",
  subst "b",
  trace_state,
  contradiction
