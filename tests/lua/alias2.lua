local env = environment()

local env      = environment()
local l        = mk_param_univ("l")
local u        = mk_global_univ("u")
env = add_level_alias(env, "m", "l")
env = add_level_alias(env, "l1", "l")
assert(is_level_aliased(env, "l") == name("l1"))
