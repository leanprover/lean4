def half_baked : bool → ℕ
| tt := 42
| ff := sorry

vm_eval (half_baked tt)
vm_eval (half_baked ff)

meta def my_partial_fun : bool → ℕ
| tt := 42
| ff := undefined

vm_eval (my_partial_fun ff)

open expr tactic
run_command (do v ← to_expr `(half_baked ff) >>= whnf,
                trace $ to_string v^.is_sorry)

example : 0 = 1 := by admit
example : 0 = 1 := by mk_sorry >>= exact
example : 0 = 1 := by exact sorry
