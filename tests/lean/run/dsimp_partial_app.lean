open tactic

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (expr.alpha_eqv t e)

meta def check_target (p : pexpr) : tactic unit :=
do t ← target, check_expr p t

example (a : list nat) : a = [1, 2] → a^.for nat.succ = [2, 3] :=
begin
  intros,
  dsimp [list.for, flip],
  check_target `(list.map nat.succ a = [2, 3]),
  subst a,
  dsimp [list.map],
  check_target `([nat.succ 1, nat.succ 2] = [2, 3]),
  reflexivity
end
