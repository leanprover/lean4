open tactic

run_cmd do
 e ← to_expr ``([5] : list ℕ),
 eval_expr ℕ e,
 return ()
