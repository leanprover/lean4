local env = environment()
env = env:add_global_level("u")
env = env:add_global_level("v")
assert(env:is_global_level("u"))

env:export("glvl1_mod.olean")
local env2 = import_modules("glvl1_mod")
assert(env2:is_global_level("u"))
assert(env2:is_global_level("v"))
