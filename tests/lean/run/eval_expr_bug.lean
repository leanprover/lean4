open tactic

meta def a : nat := 10

run_cmd eval_expr nat (expr.const `a [])
run_cmd eval_expr nat (expr.const `a []) >>= trace
