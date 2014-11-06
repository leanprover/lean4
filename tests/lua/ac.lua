local env = environment()
local l   = param_univ("l")
local U_l = mk_sort(l)
local A   = Local("A", U_l)
local R   = Local("R", mk_arrow(A, A, Prop))
local Acc = Const("Acc", {l})
local x   = Local("x", A)
local y   = Local("y", A)
env = add_inductive(env,
                    "Acc", {l}, 2, Pi(A, R, x, Prop),
                    "Acc_intro", Pi(A, R, x, mk_arrow(Pi(y, mk_arrow(R(y, x), Acc(A, R, y))), Acc(A, R, x))))

function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):infer(t)))
end

display_type(env, Const({"Acc", "rec"}, {0, 1}))
