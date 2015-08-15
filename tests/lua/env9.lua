local env = bare_environment()
-- Trust level is set to 0 by default. Then, we must type check a
-- definition, before adding it to the environment
assert(not pcall(function() env:add(mk_constant_assumption("A", Prop)) end))
-- The function check produces a "certified declaration".
env:add(check(env, mk_constant_assumption("A", Prop)))
