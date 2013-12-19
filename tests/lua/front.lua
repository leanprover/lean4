local env = environment()
print(get_options())
parse_lean_cmds([[
Variable f : Int -> Int -> Int
Variable g : Bool -> Bool -> Bool
Variables a b : Int
Variables i j : Int
Variables p q : Bool
Notation 100 _ ++ _ : f
Notation 100 _ ++ _ : g
SetOption pp::colors true
SetOption pp::width  300
]], env)
print(get_options())
assert(get_options():get{"pp", "colors"})
assert(get_options():get{"pp", "width"} == 300)
parse_lean_cmds([[
  Show i ++ j
  Show f i j
]], env)

local env2 = environment()
parse_lean_cmds([[
Variable f : Int -> Int -> Int
Variables a b : Int
Show f a b
Notation 100 _ -- _ : f
]], env2)

local f, a, b = Consts("f, a, b")
assert(tostring(f(a, b)) == "f a b")
set_formatter(lean_formatter(env))
assert(tostring(f(a, b)) == "a ++ b")
set_formatter(lean_formatter(env2))
assert(tostring(f(a, b)) == "a -- b")

local fmt = lean_formatter(env)
-- We can parse commands with respect to environment env2,
-- but using a formatter based on env.
parse_lean_cmds([[
Show f a b
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
