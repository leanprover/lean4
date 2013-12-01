local env = environment()
assert(is_hidden(env, "and"))
assert(is_hidden(env, "or"))
assert(is_hidden(env, {"Int", "lt"}))
parse_lean_cmds([[
  Definition a : Bool := true
]], env)
assert(not is_hidden(env, "a"))
set_hidden_flag(env, "a")
assert(is_hidden(env, "a"))
set_hidden_flag(env, "a", false)
assert(not is_hidden(env, "a"))
assert(not is_hidden(env, "b"))
assert(not pcall(function () set_hidden_flag(env, "b") end))
