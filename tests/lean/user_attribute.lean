attribute [user_attribute]
definition foo := ⦃user_attribute, descr := "bar"⦄

print attributes

attribute [foo] eq.refl

print [foo]
print eq.refl


-- compound names
attribute [user_attribute]
definition foo.baz := ⦃user_attribute, descr := "bar"⦄

print attributes

attribute [foo.baz] eq.refl

print [foo.baz]
print eq.refl


-- can't redeclare attributes
attribute [user_attribute]
definition reducible := ⦃user_attribute, descr := "bar"⦄


-- wrong type
attribute [user_attribute]
definition bar := "bar"

section
  variable x : string

  attribute [user_attribute]
  definition bar := ⦃user_attribute, descr := x⦄
end
