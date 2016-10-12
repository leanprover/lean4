open tactic

def f : nat → nat := λ x, x + 10

@[simp] lemma f_lemma (x : nat) : f x = x + 10 :=
rfl

example (p : nat → Prop) (a : nat) (h : p (a + 10)) : p (f a) :=
by do
  t ← target,
  S ← simp_lemmas.mk_default,
  new_t ← dsimplify (λ e, failed) (λ e, do new_e ← S^.drewrite e, return (new_e, tt)) t,
  expected ← to_expr `(p (a + 10)),
  guard (new_t = expected),
  change new_t,
  assumption
