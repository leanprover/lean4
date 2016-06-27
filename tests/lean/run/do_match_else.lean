open tactic

set_option pp.all true

example (a b c x y : nat) (H : nat.add (nat.add x y) y = 0) : true :=
by do
  a ← get_local "a", b ← get_local "b", c ← get_local "c",
  H ← get_local "H" >>= infer_type,
  (lhs, rhs) ← match_eq H,
  nat_add : expr ← mk_const ("nat" <.> "add"),
  p : pattern    ← mk_pattern [] [a, b] (nat_add a b) [nat_add b a, a, b],
  trace (pattern.output p),
  [v₁, v₂, v₃] ← match_pattern p lhs | failed,
  trace v₁, trace v₂, trace v₃,
  constructor

print "------------------"

example (f : nat → nat) (a b c x y : nat) (H : nat.add (nat.add (f (f x)) y) y = 0) : true :=
by do
  a ← get_local "a", b ← get_local "b", c ← get_local "c",
  H ← get_local "H" >>= infer_type,
  (lhs, rhs) ← match_eq H,
  nat_add : expr ← mk_const ("nat" <.> "add"),
  p : pattern    ← mk_pattern [] [a, b] (nat_add (nat_add a b) b) [nat_add (nat_add b b) (nat_add a a b), a, b],
  trace (pattern.output p),
  [v₁, v₂, v₃] ← match_pattern p lhs | failed,
  trace v₁, trace v₂, trace v₃,
  constructor
