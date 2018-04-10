open tactic

set_option pp.all true

example (a b c : nat) : true :=
by do
  x ← to_expr ```(a + b),
  trace x, infer_type x >>= trace,
  constructor

example (a b c : nat) : true :=
by do
  x ← get_local `a,
  x ← mk_app `nat.succ [x],
  r ← to_expr ```(%%x + b),
  trace r, infer_type r >>= trace,
  constructor
