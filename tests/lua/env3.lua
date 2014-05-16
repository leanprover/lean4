function init(env)
   env = add_decl(env, mk_var_decl("A", Bool))
   env = add_decl(env, mk_var_decl("And", mk_arrow(Bool, mk_arrow(Bool, Bool))))
   env = add_decl(env, mk_axiom("p", Const("A")))
   env = add_decl(env, mk_axiom("q", Const("A")))
   return env
end
local And = Const("And")
local p   = Const("p")
local q   = Const("q")

local env = init(empty_environment())
local t   = type_checker(env)
assert(t:is_def_eq(p, q))
assert(t:is_def_eq(And(p, q), And(q, p)))

env = init(empty_environment({prop_proof_irrel=false}))
t   = type_checker(env)
assert(not t:is_def_eq(p, q))
assert(not t:is_def_eq(And(p, q), And(q, p)))

