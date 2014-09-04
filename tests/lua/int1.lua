local env      = environment()
local nat      = Const("nat")
local int      = Const("int")

env = add_inductive(env,
                    "nat", Type,
                    "zero", nat,
                    "succ", mk_arrow(nat, nat))

env = add_inductive(env,
                    "int", Type,
                    "pos", mk_arrow(nat, int),
                    "neg", mk_arrow(nat, int))
function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):check(t)))
end

display_type(env, Const({"nat", "rec"}, {0}))
display_type(env, Const({"int", "rec"}, {0}))
