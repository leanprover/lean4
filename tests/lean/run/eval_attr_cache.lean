open tactic
meta def list_name.to_expr (n : list name) : tactic expr := to_expr (quote n)
meta def my_attr : caching_user_attribute (name → bool) :=
{ name         := "my_attr",
  descr        := "my attr",
  mk_cache     := λ ls, do {
   els ← list_name.to_expr ls,
   c   ← to_expr `(λ n : name, (name.cases_on n ff (λ _ _, to_bool (n ∈ %%els)) (λ _ _, ff) : bool)),
   eval_expr (name → bool) c
  },
  dependencies := []
}

run_cmd attribute.register `my_attr

meta def my_tac : tactic unit :=
do f ← caching_user_attribute.get_cache my_attr,
   trace (f `foo),
   return ()

@[my_attr] def bla := 10
run_cmd my_tac
@[my_attr] def foo := 10 -- Cache was invalided

run_cmd my_tac  -- Add closure to the cache containing auxiliary function created by eval_expr
run_cmd my_tac  -- Cache should be flushed since the auxiliary function is gone
