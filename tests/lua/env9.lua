local env = bare_environment()
-- Trust level is set to 0 by default. Then, we must type check a
-- definition, before adding it to the environment
assert(not pcall(function() env:add(mk_var_decl("A", Bool)) end))
-- The function check produces a "certified declaration".
env:add(check(env, mk_var_decl("A", Bool)))

local env = bare_environment({trust_level = 10000000})
-- Now, env has trust_level > LEAN_BELIEVER_TRUST_LEVEL, then we can
-- add declarations without type checking them.
env:add(mk_var_decl("A", Bool))

