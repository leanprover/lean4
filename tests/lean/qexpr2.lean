open tactic

set_option pp.all true

example (a b c : nat) : true :=
by do
  x ← to_expr `(_ + b) tt,
  trace x, infer_type x >>= trace,
  constructor,
  -- fill hole with 'c'
  get_local `c >>= exact,
  trace "------ after instantiate_mvars",
  instantiate_mvars x >>= trace
