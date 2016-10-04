open tactic

meta def a : nat := 10

run_command eval_expr nat (expr.const `a [])
run_command eval_expr nat (expr.const `a []) >>= trace
