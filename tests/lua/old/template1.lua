import("util.lua")
import("template.lua")
local env = environment()
env:import("Int")
parse_lean_cmds([[
   variables a b c : Int
   variables f : Int -> Int
]], env)
local a, b, c = Consts("a, b, c")
print(parse_template("%1 + f %2 + %1 + %1", {a, b}, env))
assert(tostring(parse_template("%1 + f %2 + %1 + %1", {a, b}, env)) == "Int::add (Int::add (Int::add a (f b)) a) a")
assert(not pcall(function() print(parse_template("%1 + f %2 + %1 + %1", {a}, env)) end))
print(parse_template("%1 + f %2 + %3 + f (f %1)", {a, b, c}, env))
print(parse_template("%1 + f %2 + 10 + f (f %1)", {a, b, c}, env))
assert(tostring(parse_template("%1 + f %2 + 10 + f (f %1)", {a, b, c}, env)) == "Int::add (Int::add (Int::add a (f b)) (nat_to_int 10)) (f (f a))")
set_formatter(lean_formatter(env))
print(parse_template("%1 + f %2 + %3 + f (f %1)", {a, b, c}, env))
assert(tostring(parse_template("%1 + f %2 + %3 + f (f %1)", {a, b, c}, env)) == "a + f b + c + f (f a)")
