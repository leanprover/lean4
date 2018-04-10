open tactic

example (a b c : nat) : a = c → a + b = b + c :=
by do
  n1 ← get_unused_name `a,
  n2 ← get_unused_name `b,
  n3 ← get_unused_name `c,
  n4 ← get_unused_name `d,
  intro n1,
  n5 ← get_unused_name `a,
  trace n1 >> trace n2 >> trace n3 >> trace n4 >> trace n5,
  get_local `a >>= subst,
  `[apply add_comm]
