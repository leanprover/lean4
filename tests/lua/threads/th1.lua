f = Const("f")
a = Const("a")

S = State()
T = thread(S, [[
   t = ...
   g = Const("g")
   return g(t)
]], f(a))

r = T:wait()
print(r)
