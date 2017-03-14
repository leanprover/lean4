@[user_attribute]
definition foo_attr : user_attribute := { name := `foo, descr := "bar" }

attribute [foo] eq.refl

#print [foo]
#print eq.refl
run_cmd attribute.get_instances `foo >>= tactic.pp >>= tactic.trace
#print "---"

-- compound names
@[user_attribute]
definition foo_baz_attr : user_attribute := ⟨`foo.baz, "bar"⟩

attribute [foo.baz] eq.refl

#print [foo.baz]
#print eq.refl
run_cmd attribute.get_instances `foo.baz >>= tactic.pp >>= tactic.trace

-- can't redeclare attributes
@[user_attribute]
definition duplicate : user_attribute := ⟨`reducible, "bar"⟩


-- wrong type
@[user_attribute]
definition bar := "bar"

section
  variable x : string

  @[user_attribute]
  definition baz_attr : user_attribute := ⟨`baz, x⟩
end
