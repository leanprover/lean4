open tactic expr

set_option pp.all true

example (a b c x y : nat) (H : nat.add (nat.add x y) y = 0) : true :=
by do
  a ← get_local `a, b ← get_local `b, c ← get_local `c,
  nat_add : expr ← mk_const `nat.add,
  p : pattern    ← mk_pattern [] [a, b] (app_of_list nat_add [a, b]) [] [app_of_list nat_add [b, a], a, b],
  trace (pattern.moutput p),
  H ← get_local `H >>= infer_type,
  lhs_rhs ← match_eq H,
  r     ← match_pattern p (prod.fst lhs_rhs),
  trace r,
  constructor
