import logic
namespace experiment
inductive nat : Type :=
| zero : nat
| succ : nat → nat

check @nat.rec

(*
local env     = get_env()
local nat_rec = Const({"nat", "rec"}, {1})
local nat     = Const("nat")
local n       = Local("n", nat)
local C       = Fun(n, Prop)
local p       = Local("p", Prop)
local ff      = Const("false")
local tt      = Const("true")
local t       = nat_rec(C, ff, Fun(n, p, tt))
local zero    = Const("zero")
local succ    = Const("succ")
local one     = succ(zero)
local tc      = type_checker(env)
print(env:whnf(t(one)))
print(env:whnf(t(zero)))
local m       = mk_metavar("m", nat)
print(env:whnf(t(m)))

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

test_unify(env, t(m), tt, 1)
test_unify(env, t(m), ff, 1)
*)
end experiment
