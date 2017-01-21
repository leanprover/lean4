def half_baked : bool → ℕ
| tt := 42
| ff := sorry

vm_eval (half_baked tt)
vm_eval (half_baked ff)

meta def my_partial_fun : bool → ℕ
| tt := 42
| ff := undefined

vm_eval (my_partial_fun ff)