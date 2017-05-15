import data.set

#check ({} : set nat)

open tactic expr

meta def is_assoc_bin_app : expr → tactic (expr × expr)
| (app (app op a1) a2) := do h ← to_expr ``(is_associative.assoc %%op), return (op, h)
| _                    := failed

run_cmd to_expr ``(({} : set nat) ∪ {}) >>= is_assoc_bin_app >>= λ p, trace p.2
