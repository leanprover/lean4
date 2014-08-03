function tst_match(p, t)
   local r   = match(p, t)
   assert(r)
   print("--------------")
   for i = 1, #r do
      print("  #" .. i .. " := " .. tostring(r[i]))
   end
end

local env = environment()
local N   = Const("N")
local f   = Const("f")
local a   = Const("a")
local b   = Const("b")
local x   = Local("x", N)
local y   = Local("y", N)
tst_match(f(Var(0), Var(0)), f(a, a))
tst_match(f(Var(0), Var(1)), f(a, b))
tst_match(Var(0)(x, y), f(x, f(x, y)))
assert(not match(Var(0)(x, x), f(x, f(x, y))))
assert(not match(Var(0)(x), f(x, y)))
tst_match(Pi(x, y, Var(2)(x)), Pi(x, y, f(f(x))))
tst_match(Fun(x, y, Var(2)(x)), Fun(x, y, f(f(x))))
assert(match(Pi(x, Var(2)(x)), Pi(x, y, f(f(x)))))
