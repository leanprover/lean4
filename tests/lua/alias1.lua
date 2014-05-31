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

env:for_each(function(d) print(d:name()) end)
env = add_aliases(env, "nat", "natural")
assert(get_alias(env, {"natural", "zero"}) == zero)
assert(get_alias(env, {"natural", "nat"}) == nat)
assert(is_aliased(env, nat) == name("natural", "nat"))

env = add_inductive(env,
                    name("list", "list"), {l}, 1, Pi(A, U_l, U_l1),
                    name("list", "nil"),  Pi({{A, U_l, true}}, list_l(A)),
                    name("list", "cons"), Pi({{A, U_l, true}}, mk_arrow(A, list_l(A), list_l(A))))

env = add_aliases(env, "list", "lst")
print(get_alias(env, {"lst", "list_rec"}))
env = add_aliases(env, "list")
print(get_alias(env, "list_rec"))
assert(get_alias(env, "list_rec"))
assert(get_alias(env, {"lst", "list_rec"}))

env = add_aliases(env, "list", "lnat", {{"A", nat}})
print(get_alias(env, {"lnat", "list"}))
print(get_alias(env, {"lnat", "cons"}))
assert(get_alias(env, {"lnat", "cons"}) == Const({"list", "cons"}, { mk_level_placeholder() })(nat))

local A = Local("A", mk_sort(1))
local R = Local("R", mk_arrow(A, A, Bool))
local a = Local("a", A)
local b = Local("b", A)

env = add_decl(env, mk_var_decl({"foo", "pred"}, Pi({A, R, a, b}, Bool)))
env = add_aliases(env, "foo", nil, {{"A", nat}, {"a", zero}})
local Rn = Local("R", mk_arrow(nat, nat, Bool))
local bn = Local("b", nat)
local a1 = get_alias(env, "pred")
local a2 = Fun({Rn, bn}, Const({"foo", "pred"})(nat, Rn, zero, bn))
print(a1)
print(a2)
assert(a1 == a2)
env = add_aliases(env, "foo", nil, {{"A", nat}, {"a", zero}, {"b", one}})
print(get_alias(env, "pred"))
env = add_alias(env, "z", zero)
assert(get_alias(env, "z") == zero)
assert(not get_alias(env, "zz"))
