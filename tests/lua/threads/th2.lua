S1 = State()
S2 = State()
code = [[
  function f(env, prefix, num, type)
      local r = list_certified_declaration()
      for i = 1, num do
          r = list_certified_declaration(type_check(env, mk_var_decl(prefix .. "_" .. i, type)), r)
      end
      return r
  end
]]
S1:dostring(code)
S2:dostring(code)
local e = empty_environment()
e = add_decl(e, mk_var_decl("N", Type))
code2 = [[
  e, prefix = ...
  return f(e, prefix, 1000, Const("N"))
]]
T1 = thread(S1, code2, e, "x")
T2 = thread(S2, code2, e, "y")
local r1 = T1:wait()
local r2 = T2:wait()
while not r1:is_nil() do
   e = e:add(r1:car())
   r1 = r1:cdr()
end
while not r2:is_nil() do
   e = e:add(r2:car())
   r2 = r2:cdr()
end
assert(e:find("x_" .. 10))
assert(e:find("y_" .. 100))
