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
         guard ([`add, `nat.add, `one, `zero]^.any e^.is_app_of),
         /- We are using transparency.none, so

            nat.add a (bit0 (nat.succ nat.zero))

            cannot be matched with

            nat.add ?a (nat.succ ?b)
         -/
         new_e ← dunfold_expr_core transparency.none e, trace e,
         trace "===>", trace new_e, trace "-------",
         return (new_e, tt) })
     t,
  trace new_t,
  expected ← to_expr ```(p (g (nat.add a (bit0 (nat.succ nat.zero))))),
  guard (new_t = expected),
  trace new_t,
  assumption


example (a b : nat) (p : nat → Prop) (h : p (g (nat.succ (nat.succ a)))) : p (g (a + nat.succ (nat.succ 0))) :=
by do
  t ← target,
  new_t ← dsimplify (λ e, failed)
     (λ e,
        do { new_e ← unfold_projection e, return (new_e, tt) }
        <|>
        do {
         guard ([`add, `nat.add, `one, `zero]^.any e^.is_app_of),
         new_e ← dunfold_expr_core transparency.none e, trace e,
         trace "===>", trace new_e, trace "-------",
         return (new_e, tt) })
     t,
  trace new_t,
  expected ← to_expr ```(p (g (nat.succ (nat.succ a)))),
  guard (new_t = expected),
  trace new_t,
  assumption
