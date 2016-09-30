meta def foo_attr : caching_user_attribute :=
{ name := `foo, descr := "bar", Cache := string, cache := list.join ∘ list.map (list.append "\n" ∘ to_string ∘ declaration.to_name) }

run_command attribute.register `foo_attr

attribute [foo] eq.refl eq.mp

set_option trace.user_attributes_cache true

run_command do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s

run_command do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s

attribute [foo] eq.mpr
local attribute [-foo] eq.mp

run_command do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s

attribute [reducible] eq.mp -- should not affect [foo] cache

run_command do
  s : string ← caching_user_attribute.get_cache foo_attr,
  tactic.trace s
