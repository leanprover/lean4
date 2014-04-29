import("util.lua")
local env = environment()
env:import("Int")
print(get_options())
parse_lean_cmds([[
variable f : Int -> Int -> Int
variable g : Bool -> Bool -> Bool
variables a b : Int
variables i j : Int
variables p q : Bool
notation 100 _ ++ _ : f
notation 100 _ ++ _ : g
set_option pp::colors true
set_option pp::width  300
]], env)
print(get_options())
assert(get_options():get{"pp", "colors"})
assert(get_options():get{"pp", "width"} == 300)
parse_lean_cmds([[
  print i ++ j
  print f i j
]], env)

local env2 = environment()
env2:import("Int")
parse_lean_cmds([[
variable f : Int -> Int -> Int
variables a b : Int
print f a b
notation 100 _ -+ _ : f
]], env2)

local f, a, b = Consts("f, a, b")
assert(tostring(f(a, b)) == "f a b")
set_formatter(lean_formatter(env))
assert(tostring(f(a, b)) == "a ++ b")
set_formatter(lean_formatter(env2))
assert(tostring(f(a, b)) == "a -+ b")

local fmt = lean_formatter(env)
-- We can parse commands with respect to environment env2,
-- but using a formatter based on env.
parse_lean_cmds([[
print f a b
]], env2, options(), fmt)

set_formatter(fmt)
env  = nil
env2 = nil
fmt  = nil
collectgarbage()
-- The references to env, env2 and fmt were removed, but The global
-- formatter (set with set_formatter) still has a reference to its
-- environment.
assert(tostring(f(a, b)) == "a ++ b")
