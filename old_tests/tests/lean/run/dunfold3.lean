open tactic

def g : nat → nat := λ x, x + 5

set_option pp.all true

example (a b : nat) (p : nat → Prop) (h : p (g (nat.succ (nat.succ a)))) : p (g (a + 2)) :=
begin
  unfold g at h,
  do { h ← get_local `h >>= infer_type, t ← to_expr ```(p (nat.succ (nat.succ a) + 5)), guard (h = t) },
  unfold has_add.add bit0 has_one.one nat.add,
  unfold g,
  do { t ← target, h ← get_local `h >>= infer_type, guard (t = h) },
  assumption
end

meta def check_expected (p : pexpr) : tactic unit :=
do t ← target, ex ← to_expr p, guard (t = ex)
