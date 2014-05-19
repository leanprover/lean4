local env      = empty_environment()
local l        = mk_param_univ("l")
local A        = Const("A")
local U_l      = mk_sort(l)
local U_l1     = mk_sort(max_univ(l, 1)) -- Make sure U_l1 is not Bool/Prop
local list_l   = Const("list", {l}) -- list.{l}
local Nat      = Const("nat")
local vec_l    = Const("vec", {l})  -- vec.{l}
local zero     = Const("zero")
local succ     = Const("succ")
local forest_l = Const("forest", {l})
local tree_l   = Const("tree",   {l})
local n        = Const("n")

env = env:add_global_level("u")
env = env:add_global_level("v")
local u        = global_univ("u")
local v        = global_univ("v")

function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):infer(t)))
end

env = add_inductive(env,
                    "nat", Type,
                    "zero", Nat,
                    "succ", mk_arrow(Nat, Nat))
-- In the following inductive datatype, {l} is the list of universe level parameters.
-- 1 is the number of parameters.
-- The Boolean true in {A, U_l, true} is marking that this argument is implicit.
env = add_inductive(env,
                    "list", {l}, 1, Pi(A, U_l, U_l1),
                    "nil", Pi({{A, U_l, true}}, list_l(A)),
                    "cons", Pi({{A, U_l, true}}, mk_arrow(A, list_l(A), list_l(A))))
env = add_inductive(env,
                    "vec", {l}, 1, Pi({{A, U_l}, {n, Nat}}, U_l1),
                    "vnil",  Pi({{A, U_l, true}}, vec_l(A, zero)),
                    "vcons", Pi({{A, U_l, true}, {n, Nat, true}}, mk_arrow(A, vec_l(A, n), vec_l(A, succ(n)))))

local And = Const("and")
local Or  = Const("or")
local B   = Const("B")
-- Datatype without introduction rules (aka constructors). It is a uninhabited type.
env = add_inductive(env, "false", Bool)
-- Datatype with a single constructor.
env = add_inductive(env, "true", Bool, "trivial", Const("true"))
env = add_inductive(env,
                    "and", 2, Pi({{A, Bool}, {B, Bool}}, Bool),
                    "and_intro", Pi({{A, Bool, true}, {B, Bool, true}}, mk_arrow(A, B, And(A, B))))
env = add_inductive(env,
                    "or", 2, Pi({{A, Bool}, {B, Bool}}, Bool),
                    "or_intro_left",  Pi({{A, Bool, true}, {B, Bool, true}}, mk_arrow(A, Or(A, B))),
                    "or_intro_right", Pi({{A, Bool, true}, {B, Bool, true}}, mk_arrow(B, Or(A, B))))
local P = Const("P")
local a = Const("a")
local exists_l = Const("exists", {l})
env = add_inductive(env,
                    "exists", {l}, 2, Pi({{A, U_l}, {P, mk_arrow(A, Bool)}}, Bool),
                    "exists_intro", Pi({{A, U_l, true}, {P, mk_arrow(A, Bool), true}, {a, A}}, mk_arrow(P(a), exists_l(A, P))))

env = add_inductive(env, {l}, 1,
                    {"tree", Pi(A, U_l, U_l1),
                     "node", Pi({{A, U_l, true}}, mk_arrow(A, forest_l(A), tree_l(A)))
                    },
                    {"forest", Pi(A, U_l, U_l1),
                     "emptyf", Pi({{A, U_l, true}}, forest_l(A)),
                     "consf",  Pi({{A, U_l, true}}, mk_arrow(tree_l(A), forest_l(A), forest_l(A)))})
local tc = type_checker(env)

display_type(env, Const("forest", {mk_level_zero()}))
display_type(env, Const("vcons", {mk_level_zero()}))
display_type(env, Const("consf", {mk_level_zero()}))
display_type(env, Const("forest_rec", {v, u}))
display_type(env, Const("nat_rec", {v}))
display_type(env, Const("or_rec"))

local Even = Const("Even")
local Odd  = Const("Odd")
local b    = Const("b")
env = add_inductive(env, {},
                    {"Even", mk_arrow(Nat, Bool),
                     "zero_is_even", Even(zero),
                     "succ_odd",     Pi(b, Nat, mk_arrow(Odd(b), Even(succ(b))))},
                    {"Odd", mk_arrow(Nat, Bool),
                     "succ_even", Pi(b, Nat, mk_arrow(Even(b), Odd(succ(b))))})

local flist_l = Const("flist", {l})
env = add_inductive(env,
                    "flist", {l}, 1, Pi(A, U_l, U_l1),
                    "fnil", Pi({{A, U_l, true}}, flist_l(A)),
                    "fcons", Pi({{A, U_l, true}}, mk_arrow(mk_arrow(Nat, A), mk_arrow(Nat, Bool, flist_l(A)), flist_l(A))))

local eq_l = Const("eq", {l})
env = add_inductive(env,
                    "eq", {l}, 2, Pi({{A, U_l}, {a, A}, {b, A}}, Bool),
                    "refl", Pi({{A, U_l}, {a, A}}, eq_l(A, a, a)))
display_type(env, Const("eq_rec", {v, u}))
display_type(env, Const("exists_rec", {v, u}))
display_type(env, Const("list_rec", {v, u}))
display_type(env, Const("Even_rec"))
display_type(env, Const("Odd_rec"))
display_type(env, Const("and_rec", {v}))
display_type(env, Const("vec_rec", {v, u}))
display_type(env, Const("flist_rec", {v, u}))
