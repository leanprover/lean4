local a = Const("a")
local b = Const("b")
local f = Const("f")
local vec = Const("vec")
print(Pi({{a, Type}, {b, vec(a), true}}, vec(b)))
print(Pi({{a, Type, binder_info(true, true)}, {b, vec(a), true}}, vec(b)))
assert(not pcall(function()
                    print(Pi({{a, Type}, {f(b), vec(a), true}}, vec(b)))
                 end
))
assert(not pcall(function()
                    print(Pi({{a, Type, a}, {b, vec(a), true}}, vec(b)))
                 end
))

