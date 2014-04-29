f = Const("f")
a = Const("a")
t = f(a)
s = State()
s:dostring("x = 10")

t1, t2, t3 =
s:dostring([[
a, b = ...
print("x = " .. tostring(x))
print("a = " .. tostring(a))
print("b = " .. tostring(b))
g = Const("g")
return g(b), g(g(b)), g(b, b)
]], 10, t)
print("t1: " .. tostring(t1))
print("t2: " .. tostring(t2))
print("t3: " .. tostring(t3))
print(x)
print(a)
s:dostring([[ print(b) ]])
