import("util.lua")
local env = environment()
parse_lean_cmds([[
   variable N : Type
   variables x y : N
   variable f : N -> N -> N
   set_option pp::colors false
]], env)
local f, x, y = Consts("f, x, y")
print(env:type_check(f(x, y)))
assert(env:type_check(f(x, y)) == Const("N"))
assert(not get_options():get{"pp", "colors"})
parse_lean_cmds([[
   set_option pp::colors true
]], env)
assert(get_options():get{"pp", "colors"})
local o = get_options()
o:update({"lean", "pp", "notation"}, false)
assert(not o:get{"lean", "pp", "notation"})
o = parse_lean_cmds([[
   check fun x : N, y
   set_option pp::notation true
   check fun x : N, y
]], env, o)
print(o)
assert(o:get{"lean", "pp", "notation"})
assert(parse_lean("f x y", env) == f(x, y))
