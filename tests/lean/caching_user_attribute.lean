@[user_attribute]
meta def foo_attr : caching_user_attribute string :=
{ name     := `foo, descr := "bar",
  mk_cache := λ ns, return $ list.join ∘ list.map (list.append "\n" ∘ to_string) $ ns,
  dependencies := [] }

attribute [foo] eq.refl eq.mp

set_option trace.user_attributes_cache true

run_cmd do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s

run_cmd do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s

attribute [foo] eq.mpr
local attribute [-foo] eq.mp

run_cmd do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s

attribute [reducible] eq.mp -- should not affect [foo] cache

run_cmd do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s
