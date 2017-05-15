meta def eval_list (α : Type) [reflected α] (e : expr) : tactic (list α) :=
tactic.eval_expr (list α) e

run_cmd eval_list ℕ ↑`([1, 2]) >>= tactic.trace
