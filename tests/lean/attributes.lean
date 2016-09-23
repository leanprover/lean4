universe variables u
definition foo (A : Type u) := A

local attribute [reducible] foo
local attribute [-reducible] foo -- use [semireducible] instead

--

local attribute [-instance] nat.has_one
