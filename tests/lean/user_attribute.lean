definition foo_attr : user_attribute := { name := `foo, descr := "bar" }
run_cmd attribute.register `foo_attr

attribute [foo] eq.refl

#print [foo]
#print eq.refl
run_cmd attribute.get_instances `foo >>= tactic.pp >>= tactic.trace
#print "---"

-- compound names
definition foo_baz_attr : user_attribute := ⟨`foo.baz, "bar"⟩

run_cmd attribute.register `foo_baz_attr

attribute [foo.baz] eq.refl

#print [foo.baz]
#print eq.refl
run_cmd attribute.get_instances `foo.baz >>= tactic.pp >>= tactic.trace

-- can't redeclare attributes
definition duplicate : user_attribute := ⟨`reducible, "bar"⟩
run_cmd attribute.register `duplicate


-- wrong type
definition bar := "bar"
run_cmd attribute.register `bar

section
  variable x : string

  definition baz_attr : user_attribute := ⟨`baz, x⟩
  run_cmd attribute.register `baz_attr
end
