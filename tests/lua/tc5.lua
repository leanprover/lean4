local env = bare_environment()
env = add_decl(env, mk_constant_assumption("A", Prop))
env = add_decl(env, mk_constant_assumption("T", Type))
env = add_decl(env, mk_definition("B2", Type, Prop, {opaque=false}))
env = add_decl(env, mk_constant_assumption("C", Const("B2")))
env = add_decl(env, mk_definition("BB", Type, mk_arrow(Prop, Prop), {opaque=false}))
local tc = type_checker(env)
assert(tc:is_prop(Const("A")))
assert(tc:is_prop(Const("C")))
assert(not tc:is_prop(Const("T")))
assert(not tc:is_prop(Const("B2")))
print(tc:check(mk_lambda("x", mk_metavar("m", mk_metavar("t", mk_sort(mk_meta_univ("l")))), Var(0))))
print(tc:ensure_sort(Const("B2")))
assert(not pcall(function()
                    print(tc:ensure_sort(Const("A")))
                 end
))
print(tc:ensure_pi(Const("BB")))
assert(not pcall(function()
                    print(tc:ensure_pi(Const("A")))
                 end
))
assert(not pcall(function()
                    env = add_decl(env, mk_constant_assumption("A", mk_local("l1", Prop)))
                 end
))
assert(not pcall(function()
                    print(tc:check(Let("x", Type, Const("A"), Var(0))))
                 end
))
assert(not pcall(function()
                    print(tc:check(mk_lambda("x", Prop, Var(0))(Type)))
                 end
))
assert(not pcall(function()
                    print(tc:check(Var(0)))
                 end
))

assert(tc:check(mk_pi("x", Prop, Var(0))) == Prop)

local env = bare_environment({impredicative=false})
local tc = type_checker(env)
assert(tc:check(mk_pi("x", Prop, Var(0))) == Type)
