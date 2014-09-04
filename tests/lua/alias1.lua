local env = environment()

local env      = environment()
local l        = mk_param_univ("l")
local U_l      = mk_sort(l)
local U_l1     = mk_sort(max_univ(l, 1)) -- Make sure U_l1 is not Prop
local nat      = Const({"nat", "nat"})
local vec_l    = Const({"vec", "vec"}, {l})  -- vec.{l}
local zero     = Const({"nat", "zero"})
local succ     = Const({"nat", "succ"})
local one      = succ(zero)
local list_l   = Const({"list", "list"}, {l}) -- list.{l}

env = add_inductive(env,
                    name("nat", "nat"), Type,
                    name("nat", "zero"), nat,
                    name("nat", "succ"), mk_arrow(nat, nat))

env:for_each_decl(function(d) print(d:name()) end)
env = add_aliases(env, "nat", "natural")
assert(get_expr_aliases(env, {"natural", "zero"}):head() == name("nat", "zero"))
assert(get_expr_aliases(env, {"natural", "nat"}):head() == name("nat", "nat"))
assert(is_expr_aliased(env, {"nat", "nat"}) == name("natural", "nat"))

local A        = Local("A", U_l)

env = add_inductive(env,
                    name("list", "list"), {l}, 1, Pi(A, U_l1),
                    name("list", "nil"),  Pi(A, list_l(A)),
                    name("list", "cons"), Pi(A, mk_arrow(A, list_l(A), list_l(A))))

env = add_aliases(env, "list", "lst")
print(not get_expr_aliases(env, {"lst", "list", "rec"}):is_nil())
env = add_aliases(env, "list")
print(get_expr_aliases(env, {"list", "rec"}):head())
assert(not get_expr_aliases(env, {"list", "rec"}):is_nil())
assert(not get_expr_aliases(env, {"lst", "list", "rec"}):is_nil())

env = add_aliases(env, "list", "l")
print(get_expr_aliases(env, {"l", "list"}):head())
print(get_expr_aliases(env, {"l", "cons"}):head())

local A = Local("A", mk_sort(1))
local R = Local("R", mk_arrow(A, A, Prop))
local a = Local("a", A)
local b = Local("b", A)

env = add_expr_alias(env, "z", name("nat", "zero"))
assert(get_expr_aliases(env, "z"):head() == name("nat", "zero"))
assert(get_expr_aliases(env, "zz"):is_nil())
