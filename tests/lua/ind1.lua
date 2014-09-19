local env      = environment()
local l        = mk_param_univ("l")
local U_l      = mk_sort(l)
local A        = Local("A", U_l)
local U_l1     = mk_sort(max_univ(l, 1)) -- Make sure U_l1 is not Prop
local list_l   = Const("list", {l}) -- list.{l}
local Nat      = Const("nat")
local vec_l    = Const("vec", {l})  -- vec.{l}
local zero     = Const("zero")
local succ     = Const("succ")
local forest_l = Const("forest", {l})
local tree_l   = Const("tree",   {l})
local n        = Local("n", Nat)

env = env:add_universe("u")
env = env:add_universe("v")
local u        = global_univ("u")
local v        = global_univ("v")

function display_type(env, t)
   print(tostring(t) .. " : " .. tostring(type_checker(env):check(t)))
end

env = add_inductive(env,
                    "nat", Type,
                    "zero", Nat,
                    "succ", mk_arrow(Nat, Nat))
-- In the following inductive datatype, {l} is the list of universe level parameters.
-- 1 is the number of parameters.
-- The Propean true in {A, U_l, true} is marking that this argument is implicit.
env = add_inductive(env,
                    "list", {l}, 1, Pi(A, U_l1),
                    "nil", Pi(A, list_l(A)),
                    "cons", Pi(A, mk_arrow(A, list_l(A), list_l(A))))
env = add_inductive(env,
                    "vec", {l}, 1, Pi(A, n, U_l1),
                    "vnil",  Pi(A, vec_l(A, zero)),
                    "vcons", Pi(A, n, mk_arrow(A, vec_l(A, n), vec_l(A, succ(n)))))

local And = Const("and")
local Or  = Const("or")
-- Datatype without introduction rules (aka constructors). It is a uninhabited type.
env = add_inductive(env, "false", Prop)
-- Datatype with a single constructor.
env = add_inductive(env, "true", Prop, "trivial", Const("true"))
local A = Local("A", Prop)
local B = Local("B", Prop)
env = add_inductive(env,
                    "and", 2, Pi(A, B, Prop),
                    "and_intro", Pi(A, B, mk_arrow(A, B, And(A, B))))
env = add_inductive(env,
                    "or", 2, Pi(A, B, Prop),
                    "or_intro_left",  Pi(A, B, mk_arrow(A, Or(A, B))),
                    "or_intro_right", Pi(A, B, mk_arrow(B, Or(A, B))))
local A = Local("A", U_l)
local P = Local("P", mk_arrow(A, Prop))
local a = Local("a", A)
local exists_l = Const("exists", {l})
env = add_inductive(env,
                    "exists", {l}, 2, Pi(A, P, Prop),
                    "exists_intro", Pi(A, P, a, mk_arrow(P(a), exists_l(A, P))))

env = add_inductive(env, {l}, 1,
                    {"tree", Pi(A, U_l1),
                     "node", Pi(A, mk_arrow(A, forest_l(A), tree_l(A)))
                    },
                    {"forest", Pi(A, U_l1),
                     "emptyf", Pi(A, forest_l(A)),
                     "consf",  Pi(A, mk_arrow(tree_l(A), forest_l(A), forest_l(A)))})
local tc = type_checker(env)

display_type(env, Const("forest", {0}))
display_type(env, Const("vcons", {0}))
display_type(env, Const("consf", {0}))
display_type(env, Const({"forest", "rec"}, {v, u}))
display_type(env, Const({"nat", "rec"}, {v}))
display_type(env, Const({"or", "rec"}))

local Even = Const("Even")
local Odd  = Const("Odd")
local b    = Local("b", Nat)
env = add_inductive(env, {},
                    {"Even", mk_arrow(Nat, Prop),
                     "zero_is_even", Even(zero),
                     "succ_odd",     Pi(b, mk_arrow(Odd(b), Even(succ(b))))},
                    {"Odd", mk_arrow(Nat, Prop),
                     "succ_even", Pi(b, mk_arrow(Even(b), Odd(succ(b))))})

local flist_l = Const("flist", {l})
env = add_inductive(env,
                    "flist", {l}, 1, Pi(A, U_l1),
                    "fnil", Pi(A, flist_l(A)),
                    "fcons", Pi(A, mk_arrow(mk_arrow(Nat, A), mk_arrow(Nat, Prop, flist_l(A)), flist_l(A))))

local eq_l = Const("eq", {l})

local A = Local("A", U_l)
local a = Local("a", A)
local b = Local("b", A)
env = add_inductive(env,
                    "eq", {l}, 2, Pi(A, a, b, Prop),
                    "refl", Pi(A, a, eq_l(A, a, a)))
display_type(env, Const({"eq", "rec"}, {v, u}))
display_type(env, Const({"exists", "rec"}, {u}))
display_type(env, Const({"list", "rec"}, {v, u}))
display_type(env, Const({"Even", "rec"}))
display_type(env, Const({"Odd", "rec"}))
display_type(env, Const({"and", "rec"}, {v}))
display_type(env, Const({"vec", "rec"}, {v, u}))
display_type(env, Const({"flist", "rec"}, {v, u}))

local nat_rec1 = Const({"nat", "rec"}, {1})
local a        = Local("a", Nat)
local b        = Local("b", Nat)
local n        = Local("n", Nat)
local c        = Local("c", Nat)
local add      = Fun(a, b, nat_rec1(mk_lambda("_", Nat, Nat), b, Fun(n, c, succ(c)), a))
display_type(env, add)
local tc = type_checker(env)
assert(tc:is_def_eq(add(succ(succ(zero)), succ(zero)),
                    succ(succ(succ(zero)))))
assert(tc:is_def_eq(add(succ(succ(succ(zero))), succ(succ(zero))),
                    succ(succ(succ(succ(succ(zero)))))))

local list_nat      = Const("list", {1})(Nat)
local list_nat_rec1 = Const({"list", "rec"}, {1, 1})(Nat)
display_type(env, list_nat_rec1)
local h        = Local("h", Nat)
local t        = Local("t", list_nat)
local c        = Local("c", Nat)
local lst      = Local("lst", list_nat)
local length   = Fun(lst, list_nat_rec1(mk_lambda("_", list_nat, Nat), zero, Fun(h, t, c, succ(c)), lst))
local nil_nat  = Const("nil", {1})(Nat)
local cons_nat = Const("cons", {1})(Nat)
print(tc:whnf(length(nil_nat)))
assert(tc:is_def_eq(length(nil_nat), zero))
assert(tc:is_def_eq(length(cons_nat(zero, nil_nat)), succ(zero)))
assert(tc:is_def_eq(length(cons_nat(zero, cons_nat(zero, nil_nat))), succ(succ(zero))))

env:export("ind1_mod.olean")
local env2 = import_modules("ind1_mod")
local tc = type_checker(env2)
assert(tc:is_def_eq(length(nil_nat), zero))
assert(tc:is_def_eq(length(cons_nat(zero, nil_nat)), succ(zero)))
assert(tc:is_def_eq(length(cons_nat(zero, cons_nat(zero, nil_nat))), succ(succ(zero))))
