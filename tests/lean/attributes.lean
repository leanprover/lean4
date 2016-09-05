definition foo (A : Type) := A

local attribute [reducible] foo
local attribute [-reducible] foo -- use [semireducible] instead

--

local attribute [-instance] nat_has_one
