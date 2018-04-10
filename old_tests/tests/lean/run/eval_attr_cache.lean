open tactic
@[user_attribute]
meta def my_attr : user_attribute (name → bool) :=
{ name         := "my_attr",
  descr        := "my attr",
  cache_cfg := {
    mk_cache   := λ ls, do {
      let c := `(λ n : name, (name.cases_on n ff (λ _ _, to_bool (n ∈ ls)) (λ _ _, ff) : bool)),
      eval_expr (name → bool) c
    },
    dependencies := []}
}

meta def my_tac : tactic unit :=
do f ← my_attr.get_cache,
   trace (f `foo),
   return ()

@[my_attr] def bla := 10
run_cmd my_tac
@[my_attr] def foo := 10 -- Cache was invalided

run_cmd my_tac  -- Add closure to the cache containing auxiliary function created by eval_expr
run_cmd my_tac  -- Cache should be flushed since the auxiliary function is gone
