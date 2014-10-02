function test_unify(env, lhs, rhs, num_s)
   print(tostring(lhs) .. " =?= " .. tostring(rhs) .. ", expected: " .. tostring(num_s))
   local ss = unify(env, lhs, rhs, name_generator(), true, substitution(), options())
   local n  = 0
   for s in ss do
      print("solution: ")
      s:for_each_expr(function(n, v, j)
                         print("  " .. tostring(n) .. " := " .. tostring(v))
      end)
      s:for_each_level(function(n, v, j)
                          print("  " .. tostring(n) .. " := " .. tostring(v))
      end)
      n = n + 1
   end
   if num_s ~= n then print("n: " .. n) end
   assert(num_s == n)
end

local env = environment()
env = add_decl(env, mk_constant_assumption("N", Type))
local N = Const("N")
env = add_decl(env, mk_constant_assumption("f", mk_arrow(N, N, N)))
env = add_decl(env, mk_constant_assumption("a", N))
local f  = Const("f")
local a  = Const("a")
local l1 = mk_local("l1", "x", N)
local l2 = mk_local("l2", "y", N)
local l3 = mk_local("l3", "z", N)
local m  = mk_metavar("m", mk_arrow(N, N, N))
test_unify(env, m(l1, l2), f(f(a, l1), l1), 1)
test_unify(env, f(m(l1, l2), l1), f(f(a, l1), l1), 1)
test_unify(env, f(m(l1, l2), a), f(f(a, l1), l1), 0)
