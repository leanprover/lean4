open tactic

def g : nat → nat := λ x, x + 5

example (a b : nat) (p : nat → Prop) (h : p (g (nat.succ (nat.succ a)))) : p (g (a + 2)) :=
begin
  unfold g at h,
  do { h ← get_local `h >>= infer_type, t ← to_expr `(p (nat.succ (nat.succ a) + 5)), guard (h = t) },
  unfold add has_add.add bit0 one nat.add,
  unfold g,
  do { t ← target, h ← get_local `h >>= infer_type, guard (t = h) },
  assumption
end

meta def check_expected (p : pexpr) : tactic unit :=
do t ← target, ex ← to_expr p, guard (t = ex)

example (a b c : nat) (f : nat → nat → nat) (h : false) : f (g a) (g b) = (g c) :=
begin
  unfold_occs g [2],
  check_expected `(f (g a) (b + 5) = g c),
  contradiction
end

example (a b c : nat) (f : nat → nat → nat) (h : false) : f (g a) (g b) = (g c) :=
begin
  unfold_occs g [1, 3],
  check_expected `(f (a + 5) (g b) = c + 5),
  contradiction
end
