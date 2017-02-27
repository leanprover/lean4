open tactic

run_command do
 e ← to_expr `([5] : list ℕ),
 eval_expr ℕ e,
 return ()
