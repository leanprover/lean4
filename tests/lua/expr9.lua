local env = environment()
local m   = mk_metavar("m", mk_arrow(Bool, Bool))
local a   = Local("a", Bool)
print(env:normalize(Fun(a, m)))
print(env:normalize(Fun(a, m(a))))
local m2   = mk_metavar("m2", mk_arrow(Bool, Bool, Bool))
print(env:normalize(Fun(a, (m2(a))(a))))
env:type_check(m)
env:type_check(Fun(a, m(a)))
env:type_check(Fun(a, (m2(a))(a)))
local m3   = mk_metavar("m3", mk_metavar("m4", mk_sort(mk_meta_univ("l"))))
env:type_check(m3)
-- The following call fails, because the type checker will try to
-- create a constraint, but constraint generation is not supported by
-- the type checker used to implement the method type_check
assert(not pcall(function()
                    env:type_check(m3(a))
                 end
))




