function init(env)
   env = add_decl(env, mk_constant_assumption("A", Prop))
   env = add_decl(env, mk_constant_assumption("And", mk_arrow(Prop, mk_arrow(Prop, Prop))))
   env = add_decl(env, mk_axiom("p", Const("A")))
   env = add_decl(env, mk_axiom("q", Const("A")))
   return env
end
local And = Const("And")
local p   = Const("p")
local q   = Const("q")

local env = init(bare_environment())
local t   = type_checker(env)
assert(t:is_def_eq(p, q))
assert(t:is_def_eq(And(p, q), And(q, p)))

env = init(bare_environment({prop_proof_irrel=false}))
t   = type_checker(env)
assert(not t:is_def_eq(p, q))
assert(not t:is_def_eq(And(p, q), And(q, p)))
