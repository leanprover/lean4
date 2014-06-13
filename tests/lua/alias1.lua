local env = environment()

local env      = environment()
local l        = mk_param_univ("l")
local A        = Const("A")
local U_l      = mk_sort(l)
local U_l1     = mk_sort(max_univ(l, 1)) -- Make sure U_l1 is not Bool/Prop
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
assert(get_alias_exprs(env, {"natural", "zero"}):head() == zero)
assert(get_alias_exprs(env, {"natural", "nat"}):head() == nat)
assert(is_aliased(env, nat) == name("natural", "nat"))

env = add_inductive(env,
                    name("list", "list"), {l}, 1, Pi(A, U_l, U_l1),
                    name("list", "nil"),  Pi({{A, U_l, true}}, list_l(A)),
                    name("list", "cons"), Pi({{A, U_l, true}}, mk_arrow(A, list_l(A), list_l(A))))

env = add_aliases(env, "list", "lst")
print(not get_alias_exprs(env, {"lst", "list_rec"}):is_nil())
env = add_aliases(env, "list")
print(get_alias_exprs(env, "list_rec"):head())
assert(not get_alias_exprs(env, "list_rec"):is_nil())
assert(not get_alias_exprs(env, {"lst", "list_rec"}):is_nil())

env = add_aliases(env, "list", "l")
print(get_alias_exprs(env, {"l", "list"}):head())
print(get_alias_exprs(env, {"l", "cons"}):head())

local A = Local("A", mk_sort(1))
local R = Local("R", mk_arrow(A, A, Bool))
local a = Local("a", A)
local b = Local("b", A)

env = add_alias(env, "z", zero)
assert(get_alias_exprs(env, "z"):head() == zero)
assert(get_alias_exprs(env, "zz"):is_nil())
