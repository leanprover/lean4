definition foo := ⦃user_attribute, descr := "bar"⦄
run_command attribute.register `foo

attribute [foo] eq.refl

print [foo]
print eq.refl
run_command attribute.get_instances `foo >>= tactic.pp >>= tactic.trace
print "---"

-- compound names
definition foo.baz := ⦃user_attribute, descr := "bar"⦄

run_command attribute.register `foo.baz

attribute [foo.baz] eq.refl

print [foo.baz]
print eq.refl
run_command attribute.get_instances `foo.baz >>= tactic.pp >>= tactic.trace

-- can't redeclare attributes
definition reducible := ⦃user_attribute, descr := "bar"⦄
run_command attribute.register `reducible


-- wrong type
definition bar := "bar"
run_command attribute.register `bar

section
  variable x : string

  definition baz := ⦃user_attribute, descr := x⦄
  run_command attribute.register `baz
end
