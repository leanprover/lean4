local env      = environment()

function bad_add_inductive(...)
   arg = {...}
   ok, msg = pcall(function() add_inductive(unpack(arg)) end)
   assert(not ok)
   print("\nExpected error: " .. msg:what())
end

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

bad_add_inductive(env,
                  "nat", Type,
                  "zero", Bool, -- Incorrect result type
                  "succ", mk_arrow(Nat, Nat))

bad_add_inductive(env, {l}, 1,
                  {"tree", mk_arrow(U_l, U_l1),
                   "node", Pi({{A, U_l, true}}, mk_arrow(A, forest_l(A), tree_l(A)))
                  },
                  {"forest", mk_arrow(U_l1, U_l1), -- Parameters of all inductive types must match
                   "emptyf", Pi({{A, U_l, true}}, forest_l(A)),
                   "consf",  Pi({{A, U_l, true}}, mk_arrow(tree_l(A), forest_l(A), forest_l(A)))})

bad_add_inductive(env, {l}, 1,
                  {"tree", mk_arrow(U_l, U_l), -- Result may be in universe zero (e.g., l is instantiated with zero)
                   "node", Pi({{A, U_l, true}}, mk_arrow(A, forest_l(A), tree_l(A)))
                  },
                  {"forest", mk_arrow(U_l, U_l1),
                   "emptyf", Pi({{A, U_l, true}}, forest_l(A)),
                   "consf",  Pi({{A, U_l, true}}, mk_arrow(tree_l(A), forest_l(A), forest_l(A)))})

bad_add_inductive(env,
                  "nat", 1, Type, -- mismatch in the number of arguments claimed
                  "zero", Nat,
                  "succ", mk_arrow(Nat, Nat))

env = add_inductive(env,
                    "nat", Type,
                    "zero", Nat,
                    "succ", mk_arrow(Nat, Nat))

local Even = Const("Even")
local Odd  = Const("Odd")
local b    = Const("b")
bad_add_inductive(env, {},
                  {"Even", mk_arrow(Nat, Type),
                   "zero_is_even", Even(zero),
                   "succ_odd",     Pi(b, Nat, mk_arrow(Odd(b), Even(succ(b))))},
                  {"Odd", mk_arrow(Nat, Bool), -- if one datatype lives in Bool/Prop, then all must live in Bool/Prop
                   "succ_even", Pi(b, Nat, mk_arrow(Even(b), Odd(succ(b))))})

bad_add_inductive(env,
                  "list", {l}, 1, mk_arrow(U_l, U_l1),
                  "nil", Pi({{A, U_l, true}}, mk_arrow(mk_arrow(list_l(A), Bool), list_l(A))), -- nonpositive occurrence of inductive datatype
                  "cons", Pi({{A, U_l, true}}, mk_arrow(A, list_l(A), list_l(A))))

bad_add_inductive(env,
                  "list", {l}, 1, mk_arrow(U_l, U_l1),
                  "nil", Pi({{A, U_l, true}}, list_l(mk_arrow(A, A))),
                  "cons", Pi({{A, U_l, true}}, mk_arrow(A, list_l(A), list_l(A))))

local list_1 = Const("list", {mk_level_one()})

bad_add_inductive(env,
                  "list", {l}, 1, mk_arrow(U_l, U_l1),
                  "nil", Pi({{A, U_l, true}}, list_l(A)),
                  "cons", Pi({{A, U_l, true}}, mk_arrow(A, list_1(Nat), list_l(A)))) -- all list occurrences must be of the form list_l(A)

bad_add_inductive(env,
                  "list", {l}, 1, mk_arrow(U_l, U_l1),
                  "nil", Pi({{A, U_l, true}}, list_l(A)),
                  "cons", Pi({{A, Type, true}}, mk_arrow(A, list_1(A), list_1(A))))

bad_add_inductive(env,
                  "list", {l}, 1, mk_arrow(U_l, U_l1),
                  "nil", Pi({{A, U_l, true}}, mk_arrow(U_l, list_l(A))),
                  "cons", Pi({{A, U_l, true}}, mk_arrow(A, list_l(A), list_l(A))))

bad_add_inductive(env,
                  "list", {l}, 1, mk_arrow(U_l, U_l1),
                  "nil", Pi({{A, U_l, true}}, list_l(A)),
                  "cons", Pi({{A, U_l, true}}, mk_arrow(list_l(A), A, list_l(A))))

env = add_decl(env, mk_var_decl("eq", Pi(A, Type, mk_arrow(A, A, Bool))))
local eq   = Const("eq")
local Nat2 = Const("nat2")
local a    = Const("a")
bad_add_inductive(env,
                  "nat2", Type,
                  "zero2", Nat2,
                  "succ2", Pi(a, Nat2, mk_arrow(eq(Nat2, a, a), Nat2)))

local env      = empty_environment()
bad_add_inductive(env, -- Environment does not support inductive datatypes
                  "nat", Type,
                  "zero", Nat,
                  "succ", mk_arrow(Nat, Nat))
