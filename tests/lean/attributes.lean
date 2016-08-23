definition foo (A : Type) := A

local attribute [-unfold] foo

local attribute [unfold 1] foo

attribute [-unfold]

section
  local attribute [-unfold] foo
  print foo
end
print foo

local attribute [-unfold] foo
print foo

local attribute [-unfold] foo

local attribute [unfold] foo
print foo

--

local attribute [reducible] foo
local attribute [-reducible] foo -- use [semireducible] instead

--

local attribute [-instance] nat_has_one
