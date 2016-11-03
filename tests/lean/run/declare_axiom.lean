open tactic

run_command (do
  e ← to_expr `(false),
  add_decl $ declaration.ax `useful_assumption [] e)
