open tactic

example (f : nat → nat) (a : nat) : f (f (a + 0)) = a → true :=
by do
  t ← target,
  s ← to_expr `(f a),
  b ← kdepends_on t s, guard ¬b,
  b ← kdepends_on t s semireducible, guard b,
  s ← to_expr `(f (a + 0)),
  b ← kdepends_on t s, guard b,
  intros, constructor
