local env = hott_environment()
assert(not env:impredicative())
assert(not env:prop_proof_irrel())

local l        = param_univ("l")
local U_l      = mk_sort(l)
local A        = Local("A", U_l)
local list_l   = Const("list", {l})

-- In HoTT environments, we don't need to use max(l, 1) trick
-- in the following definition
env = add_inductive(env,
                    "list", {l}, 1, Pi(A, U_l),
                    "nil", Pi(A, list_l(A)),
                    "cons", Pi(A, mk_arrow(A, list_l(A), list_l(A))))

local l1          = param_univ("l1")
local l2          = param_univ("l2")
local U_l1        = mk_sort(l1)
local U_l2        = mk_sort(l2)
local U_l1l2      = mk_sort(max_univ(l1, l2))
local A           = Local("A", U_l1)
local B           = Local("B", U_l2)
local a           = Local("a", A)
local b           = Local("b", B)
local sigma_l1l2  = Const("sigma", {l1, l2})

env = add_inductive(env,
                    "sigma", {l1, l2}, 2, Pi({A, B}, U_l1l2),
                    "pair", Pi({A, B, a, b}, sigma_l1l2(A, B)))

local coproduct_l1l2 = Const("coproduct", {l1, l2})

env = add_inductive(env,
                    "coproduct", {l1, l2}, 2, Pi({A, B}, U_l1l2),
                    "inl", Pi({A, B, a}, coproduct_l1l2(A, B)),
                    "inr", Pi({A, B, b}, coproduct_l1l2(A, B)))

env:for_each(function(d)
                print(tostring(d:name()) .. " : " .. tostring(d:type()))
             end
)
