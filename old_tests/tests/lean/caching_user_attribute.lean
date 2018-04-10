@[user_attribute]
meta def foo_attr : user_attribute string :=
{ name     := `foo, descr := "bar",
  cache_cfg := {
    mk_cache := λ ns, return $ string.join (list.map (λ n, to_string n ++ "\n") ns),
    dependencies := []} }

attribute [foo] eq.refl eq.mp

set_option trace.user_attributes_cache true

run_cmd do
  s : string ← foo_attr.get_cache,
  tactic.trace s,
  s : string ← foo_attr.get_cache,
  tactic.trace s,
  foo_attr.set `eq.mpr () tt,
  s : string ← foo_attr.get_cache,
  tactic.trace s,
  tactic.set_basic_attribute `reducible ``eq.mp, -- should not affect [foo] cache
  s : string ← foo_attr.get_cache,
  tactic.trace s
