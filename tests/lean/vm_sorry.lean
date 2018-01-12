def half_baked : bool → ℕ
| tt := 42
| ff := sorry

#eval (half_baked tt)
#eval (half_baked ff)

meta def my_partial_fun : bool → ℕ
| tt := 42
| ff := undefined

#eval (my_partial_fun ff)

open expr tactic
run_cmd (do v ← to_expr ``(half_baked ff) >>= whnf,
                trace $ to_string v^.is_sorry)

example : 0 = 1 := by admit
example : 0 = 1 := by mk_sorry >>= exact
example : 0 = 1 := by exact sorry
example : 0 = 1 := by sorry
