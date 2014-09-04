local env = environment()

local tricky = Const("tricky")
local P      = Local("P", Prop)

env = add_inductive(env,
                    "tricky", Prop,
                    "C",      mk_arrow(Pi(P, mk_arrow(P, P)), tricky))

function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):check(t)))
end

env = env:add_universe("u")
local tricky_rec = Const({"tricky", "rec"}, {0})

display_type(env, tricky_rec)
