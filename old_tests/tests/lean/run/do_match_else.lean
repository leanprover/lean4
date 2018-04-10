open tactic

set_option pp.all true

meta def app2 (f a b : expr) :=
expr.app (expr.app f a) b

example (a b c x y : nat) (H : nat.add (nat.add x y) y = 0) : true :=
by do
  a ← get_local `a, b ← get_local `b, c ← get_local `c,
  H ← get_local `H >>= infer_type,
  (lhs, rhs) ← match_eq H,
  nat_add : expr ← mk_const `nat.add,
  p : pattern    ← mk_pattern [] [a, b] (app2 nat_add a b) [] [app2 nat_add b a, a, b],
  trace (pattern.moutput p),
  (_, [v₁, v₂, v₃]) ← match_pattern p lhs | failed,
  trace v₁, trace v₂, trace v₃,
  constructor
