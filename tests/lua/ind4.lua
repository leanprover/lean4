function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(env:normalize(env:type_check(t))))
end

local env      = environment()
local l        = param_univ("l")
local U_l      = mk_sort(l)
local U_l1     = mk_sort(max_univ(l, 1)) -- Make sure U_l1 is not Prop
local A        = Local("A", U_l)
local list_l   = Const("list", {l})

local env1 = add_inductive(env,
                           "list", {l}, 1, Pi(A, U_l1),
                           "nil", Pi(A, list_l(A)),
                           "cons", Pi(A, mk_arrow(A, list_l(A), list_l(A))))

display_type(env1, Const({"list", "rec"}, {1, 1}))

-- Slightly different definition where A : Type.{l} is an index
-- instead of a global parameter
local U_sl = mk_sort(succ_univ(l))
local env2 = add_inductive(env,
                           "list", {l}, 0, Pi(A, U_sl), -- The resultant type must live in the universe succ(l)
                           "nil", Pi(A, list_l(A)),
                           "cons", Pi(A, mk_arrow(A, list_l(A), list_l(A))))
display_type(env2, Const({"list", "rec"}, {1, 1}))
