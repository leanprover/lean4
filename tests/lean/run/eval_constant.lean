open tactic

run_command do
   e  ← to_expr `(nat.add),
   fn ← eval_expr (nat → nat → nat) e,
   trace (fn 10 20)
