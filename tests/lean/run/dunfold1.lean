open tactic

set_option pp.all true

def g : nat → nat := λ x, x + 5

example (a b : nat) (p : nat → Prop) (h : p (g (nat.succ (nat.succ a)))) : p (g (a + 2)) :=
by do
  t ← target,
  new_t ← dsimplify (λ e, failed)
     (λ e,
        do { new_e ← unfold_projection e, return (new_e, tt) }
        <|>
        do {
         guard ([`add, `nat.add, `one, `zero, `bit0, `bit1]^.any e^.is_app_of),
         new_e ← dunfold_expr e, trace e,
         trace "===>", trace new_e, trace "-------",
         return (new_e, tt) })
     t,
  expected ← to_expr `(p (g (nat.succ (nat.succ a)))),
  guard (new_t = expected),
  trace new_t,
  assumption
