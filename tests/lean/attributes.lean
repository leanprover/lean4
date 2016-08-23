definition foo (A : Type) := A

attribute [-unfold] foo

attribute [unfold 1] foo

section
  local attribute [-unfold] foo
  print foo
end
print foo

attribute [-unfold] foo
print foo

attribute [-unfold] foo

attribute [unfold] foo
print foo

--

attribute [reducible] foo
attribute [-reducible] foo -- use [semireducible] instead
print foo

--

attribute [-instance] nat_has_one
