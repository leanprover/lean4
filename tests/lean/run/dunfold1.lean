open tactic

set_option pp.all true

example (a b : nat) (p : nat → Prop) (h : p (nat.succ (nat.succ a))) : p (a + 2) :=
by do
  t ← target,
  new_t ← dsimplify (λ e, failed) (λ e, do new_e ← dunfold_expr e, trace e, trace "===>", trace new_e, trace "-------", return (new_e, tt)) t,
  expected ← to_expr `(p (nat.succ (nat.succ a))),
  guard (new_t = expected),
  trace new_t,
  assumption
