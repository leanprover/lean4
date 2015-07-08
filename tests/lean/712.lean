reserve infix `~~~`:50
reserve notation `[` a `][` b:10 `]`

section
local infix `~~~` := eq

print notation ~~~

local infix `~~~`:50 := eq

print notation ~~~

local infix `~~~`:100 := eq

infix `~~~`:100 := eq  -- FAIL

print notation ~~~

local notation `[` a `][`:10 b:20 `]` := a = b

print notation ][
end

notation `[` a `][`:10 b:20 `]` := a = b -- FAIL

notation `[` a `][` b `]` := a = b
infix `~~~` := eq

print notation ~~~
print notation ][
