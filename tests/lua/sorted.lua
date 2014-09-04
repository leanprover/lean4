local env = environment()
local l        = mk_param_univ("l")
local A        = Local("A", mk_sort(l))
local U_l      = mk_sort(l)
local U_l1     = mk_sort(max_univ(l, 1)) -- Make sure U_l1 is not Prop
local list_l   = Const("list", {l}) -- list.{l}

env = add_inductive(env,
                    "list", {l}, 1, Pi(A, U_l1),
                    "nil", Pi(A, list_l(A)),
                    "cons", Pi(A, mk_arrow(A, list_l(A), list_l(A))))

local cons_l = Const("cons", {l})
local nil_l  = Const("nil", {l})
local is_sorted_l = Const("is_sorted", {l})
local a           = Local("a", A)
local lt          = Local("lt", mk_arrow(A, A, Prop))
local a1          = Local("a1", A)
local a2          = Local("a2", A)
local t           = Local("t", list_l(A))
local Hlt         = Local("H", lt(a1, a2))
local Hs          = Local("Hs", is_sorted_l(A, lt, cons_l(A, a2, t)))

env = add_inductive(env,
                    "is_sorted", {l}, 2,   Pi(A, lt, mk_arrow(list_l(A), Prop)),
                    "is_sorted_nil",       Pi(A, lt, is_sorted_l(A, lt, nil_l(A))),
                    "is_sorted_cons_nil",  Pi(A, lt, a, is_sorted_l(A, lt, cons_l(A, a, nil_l(A)))),
                    "is_sorted_cons_cons", Pi(A, lt, a1, a2, t, Hlt, Hs, is_sorted_l(A, lt, cons_l(A, a1, cons_l(A, a2, t)))))

print(env:find({"is_sorted", "rec"}):type())
