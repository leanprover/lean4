local env = environment()
env:import("Int")
parse_lean_cmds([[
  variable f : Int -> Int -> Int
  notation 20 _ +++ _ : f
  print f 10 20
  notation 20 _ -+- _ : f
  print f 10 20
]], env)

local F = parse_lean('f 10 20', env)
print(lean_formatter(env)(F))
assert(tostring(lean_formatter(env)(F)) == "10 -+- 20")

local child = env:mk_child()

parse_lean_cmds([[
  print f 10 20
]], child)

assert(tostring(lean_formatter(env)(F)) == "10 -+- 20")
print(lean_formatter(child)(F))
assert(tostring(lean_formatter(child)(F)) == "10 -+- 20")
