open tactic

run_cmd do
   e  ← to_expr ``(nat.add),
   fn ← eval_expr (nat → nat → nat) e,
   trace (fn 10 20)

run_cmd do
   e  ← to_expr ``(λ x y : nat, x + x + y),
   fn ← eval_expr (nat → nat → nat) e,
   trace (fn 10 20)
