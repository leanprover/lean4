local env = environment()
env = env:add_universe("u")
env = env:add_universe("v")
assert(env:is_universe("u"))

env:export("glvl1_mod.olean")
local env2 = import_modules("glvl1_mod")
assert(env2:is_universe("u"))
assert(env2:is_universe("v"))
