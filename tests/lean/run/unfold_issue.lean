def f : nat → nat → nat
| 0     := λ x, x
| (n+1) := λ x, x + 1

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← tactic.to_expr p, guard (t = e)

example (n : nat): f (n+1) n = n + 1 :=
begin
  unfold f
end
