definition foo_attr := ⦃user_attribute, name := `foo, descr := "bar"⦄
run_command attribute.register `foo_attr

attribute [foo] eq.refl

print [foo]
print eq.refl
run_command attribute.get_instances `foo >>= tactic.pp >>= tactic.trace
print "---"

-- compound names
definition foo_baz_attr := ⦃user_attribute, name := `foo.baz, descr := "bar"⦄

run_command attribute.register `foo_baz_attr

attribute [foo.baz] eq.refl

print [foo.baz]
print eq.refl
run_command attribute.get_instances `foo.baz >>= tactic.pp >>= tactic.trace

-- can't redeclare attributes
definition duplicate := ⦃user_attribute, name := `reducible, descr := "bar"⦄
run_command attribute.register `duplicate


-- wrong type
definition bar := "bar"
run_command attribute.register `bar

section
  variable x : string

  definition baz_attr := ⦃user_attribute, name := `baz, descr := x⦄
  run_command attribute.register `baz_attr
end
