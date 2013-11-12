S1 = State()
S2 = State()
code = [[
  function f(env, prefix, num, type)
      for i = 1, num do
          env:add_var(prefix .. "_" .. i, type)
      end
  end
]]
S1:dostring(code)
S2:dostring(code)
e = environment()
e:add_var("N", Type())
code2 = [[
  e, prefix = ...
  f(e, prefix, 1000, Const("N"))
]]
T1 = thread(S1, code2, e, "x")
T2 = thread(S2, code2, e, "y")
T1:wait()
T2:wait()
print(e)
