open tactic

example (f : nat → nat → nat) (p : nat → Prop) (a b : nat) : f ((a + 1, b).1) b = f (a+1) (a, b).2 :=
by do
  t ← target,
  new_t ← dsimplify (λ e, failed) (λ e, do new_e ← whnf e, return (new_e, tt)) t,
  expected ← to_expr ```(f (nat.succ a) b = f (nat.succ a) b),
  guard (new_t = expected),
  reflexivity

example (f : nat → nat → nat) (p : nat → Prop) (a b : nat) : f ((a + 1, b).1) b = f (a+1) (a, b).2 :=
by do
  t ← target,
  new_t ← dsimplify (λ e, failed) (λ e, do new_e ← whnf_no_delta e, return (new_e, tt)) t,
  expected ← to_expr ```(f (a + 1) b = f (a + 1) b),
  guard (new_t = expected),
  reflexivity
