@[user_attribute]
meta def foo_attr : user_attribute := { name := `foo, descr := "bar" }

attribute [foo] eq.refl

#print [foo]
#print eq.refl
run_cmd attribute.get_instances `foo >>= tactic.pp >>= tactic.trace
#print "---"

-- compound names
@[user_attribute]
meta def foo_baz_attr : user_attribute := { name := `foo.baz, descr := "bar" }

attribute [foo.baz] eq.refl

#print [foo.baz]
#print eq.refl
run_cmd attribute.get_instances `foo.baz >>= tactic.pp >>= tactic.trace

-- can't redeclare attributes
@[user_attribute]
meta def duplicate : user_attribute := { name := `reducible, descr := "bar" }


-- wrong type
@[user_attribute]
meta def bar := "bar"

section
  variable x : string

  @[user_attribute]
  meta def baz_attr : user_attribute := { name := `baz, descr := x }
end

-- parameterized attributes

@[user_attribute] meta def pattr : user_attribute unit name :=
{ name := `pattr, descr := "pattr", parser := lean.parser.ident }

@[pattr poing]
def foo := 1

run_cmd pattr.get_param `foo >>= tactic.trace
