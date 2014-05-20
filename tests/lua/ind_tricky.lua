local env = environment()

local tricky = Const("tricky")
local P      = Const("P")

env = add_inductive(env,
                    "tricky", Bool,
                    "C",      mk_arrow(Pi(P, Bool, mk_arrow(P, P)), tricky))

function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):check(t)))
end

env = env:add_global_level("u")
local tricky_rec = Const("tricky_rec", {0})

display_type(env, tricky_rec)
