local j1 = mk_assumption_justification(1)
local j2 = mk_assumption_justification(2)
assert(is_justification(j1))
assert(j1:depends_on(j1))
assert(not j1:depends_on(j2))
for c in j1:children() do
   assert(false)
end
assert(not j2:has_children())
print(j1)
assert(not j1:get_main_expr())
