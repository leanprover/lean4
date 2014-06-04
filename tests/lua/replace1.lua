local f = Const("f")
local a = Const("a")
local b = Const("b")
local t = f(a, f(a))
local new_t = t:replace(function(e)
                           if e == a then
                              return b
                           end
                        end)
print(new_t)
