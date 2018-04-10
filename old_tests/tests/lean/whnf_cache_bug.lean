open tactic

example : true :=
by do
  N ← to_expr ``(nat),
  e ← mk_meta_var N,
  whnf e >>= trace,
  s ← to_expr ``(1 + 1),
  unify e s,
  whnf e >>= trace,
  constructor
