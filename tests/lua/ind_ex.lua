local env       = environment()
local l         = param_univ("l")
local U_l       = mk_sort(l)
local inhabited = Const("inhabited", {l})
local A         = Local("A", U_l)
local a         = Local("a", A)

env = add_inductive(env,
                    "inhabited", {l}, 1, mk_arrow(U_l, Prop),
                    "inhabited_intro", Pi(A, a, inhabited(A)))

function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):check(t)))
end

display_type(env, Const({"inhabited", "rec"}, {1}))
