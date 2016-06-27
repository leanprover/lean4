open tactic

set_option pp.all true

example (a b c x y : nat) (H : nat.add (nat.add x y) y = 0) : true :=
by do
  a ← get_local "a", b ← get_local "b", c ← get_local "c",
  nat_add : expr ← mk_const ("nat" <.> "add"),
  p : pattern    ← mk_pattern [] [a, b] (nat_add a b) [nat_add b a, a, b],
  trace (pattern.output p),
  H ← get_local "H" >>= infer_type,
  lhs_rhs ← match_eq H,
  [v₁, v₂, v₃] ← match_pattern p (prod.pr1 lhs_rhs) | failed,
  trace v₁,
  constructor
