local env    = empty_environment()
local l      = mk_param_univ("l")
local A      = Const("A")
local U_l    = mk_sort(l)
local U_l1   = mk_sort(mk_level_max(l, mk_level_one()))
local list_l = Const("list", {l})
local Nat    = Const("nat")
local vec_l  = Const("vec", {l})
local zero   = Const("zero")
local succ   = Const("succ")
local forest_l = Const("forest", {l})
local tree_l   = Const("tree",   {l})
local n      = Const("n")
env = add_inductive(env, "nat", Type, "zero", Nat, "succ", mk_arrow(Nat, Nat))
env = add_inductive(env,
                    "list", {l}, 1, mk_arrow(U_l, U_l1),
                    "nil", Pi({{A, U_l, true}}, list_l(A)),
                    "cons", Pi({{A, U_l, true}}, mk_arrow(A, list_l(A), list_l(A))))
env = add_inductive(env,
                    "vec", {l}, 1,
                    mk_arrow(U_l, Nat, U_l1),
                    "vnil",  Pi({{A, U_l, true}}, vec_l(A, zero)),
                    "vcons", Pi({{A, U_l, true}, {n, Nat, true}}, mk_arrow(A, vec_l(A, n), vec_l(A, succ(n)))))

local And = Const("and")
local Or  = Const("or")
local B   = Const("B")
env = add_inductive(env, "false", Bool)
env = add_inductive(env, "true", Bool, "trivial", Const("true"))
env = add_inductive(env,
                    "and", mk_arrow(Bool, Bool, Bool),
                    "and_intro", Pi({{A, Bool, true}, {B, Bool, true}}, mk_arrow(A, B, And(A, B))))
env = add_inductive(env,
                    "or", mk_arrow(Bool, Bool, Bool),
                    "or_intro_left",  Pi({{A, Bool, true}, {B, Bool, true}}, mk_arrow(A, Or(A, B))),
                    "or_intro_right", Pi({{A, Bool, true}, {B, Bool, true}}, mk_arrow(B, Or(A, B))))
local P = Const("P")
local a = Const("a")
local exists_l = Const("exists", {l})
env = add_inductive(env,
                    "exists", {l}, 2, Pi({{A, U_l}}, mk_arrow(mk_arrow(A, Bool), Bool)),
                    "exists_intro", Pi({{A, U_l, true}, {P, mk_arrow(A, Bool), true}, {a, A}}, mk_arrow(P(a), exists_l(A, P))))

env = add_inductive(env, {l}, 1,
                    {"tree", mk_arrow(U_l, U_l1),
                     "node", Pi({{A, U_l, true}}, mk_arrow(A, forest_l(A), tree_l(A)))
                    },
                    {"forest", mk_arrow(U_l, U_l1),
                     "emptyf", Pi({{A, U_l, true}}, forest_l(A)),
                     "consf",  Pi({{A, U_l, true}}, mk_arrow(tree_l(A), forest_l(A), forest_l(A)))})

local tc = type_checker(env)
print(tc:check(Const("forest", {mk_level_zero()})))
print(tc:check(Const("vcons", {mk_level_zero()})))
print(tc:check(Const("consf", {mk_level_zero()})))
local Even = Const("Even")
local Odd  = Const("Odd")
local b    = Const("b")
env = add_inductive(env, {},
                    {"Even", mk_arrow(Nat, Bool),
                     "zero_is_even", Even(zero),
                     "succ_odd",     Pi(b, Nat, mk_arrow(Odd(b), Even(succ(b))))},
                    {"Odd", mk_arrow(Nat, Bool),
                     "succ_even", Pi(b, Nat, mk_arrow(Even(b), Odd(succ(b))))})
