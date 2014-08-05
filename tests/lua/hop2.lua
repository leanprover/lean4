function tst_match(p, t)
   local r1, r2   = match(p, t)
   assert(r1)
   print("--------------")
   for i = 1, #r1 do
      print("  expr:#" .. i .. " := " .. tostring(r1[i]))
   end
   for i = 1, #r2 do
      print("  lvl:#" .. i .. "  := " .. tostring(r2[i]))
   end
end

local env = environment()
local N   = Const("N")
local a   = Const("a")
local b   = Const("b")
local x   = Local("x", N)
local y   = Local("y", N)
local u1  = mk_global_univ("u1")
local u2  = mk_global_univ("u2")
local z   = level()
local f   = Const("f", {u1, z})
local f2  = Const("f", {u1, u1+1})
local fp  = Const("f", {mk_idx_meta_univ(0), mk_idx_meta_univ(1)})
tst_match(fp(Var(0), Var(0)), f(a, a))
tst_match(fp(Var(0), Var(1)), f2(a, b))
tst_match(Var(0)(x, y), f(x, f(x, y)))
assert(not match(Var(0)(x, x), f(x, f(x, y))))
assert(not match(Var(0)(x), f(x, y)))
