function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(env:normalize(env:type_check(t))))
end

local env = environment()

local l   = param_univ("l")
local U_l = mk_sort(l)
local A   = Local("A", U_l)
local R   = Local("R", mk_arrow(A, A, Prop))
local x   = Local("x", A)
local y   = Local("y", A)
local Acc = Const("Acc", {l})

env = add_inductive(env,
                    "Acc", {l}, 2, Pi(A, R, x, mk_sort(l+1)),
                    "Acc_intro", Pi(A, R, x, mk_arrow(Pi(y, mk_arrow(R(y, x), Acc(A, R, y))), Acc(A, R, x))))

env = env:add_universe("u")
env = env:add_universe("v")
local u = global_univ("u")
local v = global_univ("v")
display_type(env, Const({"Acc", "rec"}, {v, u}))

-- well_founded_induction_type :
-- Pi (A : Type)
--    (R : A -> A -> Prop)
--    (R_is_wf : Pi (a : A), (Acc A R a))
--    (P : A -> Type)
--    (H : Pi (x : A) (Hr : Pi (y : A) (a : R y x), (P y)), (P x))
--    (a : A),
-- (P a)
local l1          = param_univ("l1")
local l2          = param_univ("l2")
local Acc         = Const("Acc", {l1})
local Acc_intro   = Const("Acc_intro", {l1})
local Acc_rec     = Const({"Acc", "rec"}, {l2, l1})
local A           = Local("A", mk_sort(l1))
local R           = Local("R", mk_arrow(A, A, Prop))
local x           = Local("x", A)
local y           = Local("y", A)
local a           = Local("a", A)
local P           = Local("P", mk_arrow(A, mk_sort(l2)))
local Hr          = Local("Hr", Pi(y, mk_arrow(R(y, x), P(y))))
local H           = Local("H", Pi(x, Hr, P(x)))
local HR          = Local("HR", R(y, x))
local HRa         = Local("HRa", R(y, a))
local arg         = Local("arg", Pi(y, HR, Acc(A, R, y)))
local H_arg       = Local("H_arg", Pi(y, HR, P(y)))
local d           = Local("d", Acc(A, R, x))
local Hwf        = Local("R_is_wf", Pi(a, Acc(A, R, a)))
local wfi_th_type = Pi(A, R, Hwf, P, H, a, P(a))
print(wfi_th_type)
type_checker(env):check(wfi_th_type, {l1, l2})
local wfi_th_val  = Fun(A, R, Hwf, P, H, a, Acc_rec(A, R,
                                                    Fun(x, d, P(x)), -- C
                                                    Fun(x, arg, H_arg, H(x, H_arg)), -- e_1
                                                    a,
                                                    Acc_intro(A, R, a, Fun(y, HRa, Hwf(y)))
))
print(env:normalize(type_checker(env):check(wfi_th_val, {l1, l2})))
env = add_decl(env, mk_definition("well_founded_induction_type", {l1, l2}, wfi_th_type, wfi_th_val))
display_type(env, Const("well_founded_induction_type", {1,1}))
