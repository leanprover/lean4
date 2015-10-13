import logic

definition proj1 (x : num) (y : num) := x
definition One : num := 1

(*
local num   = Const("num")
local m     = mk_metavar("m", num)
local proj1 = Const("proj1")
local zero  = Const({"num", "zero"})
local one   = Const("One")
local t1    = proj1(m, one)
local t2    = proj1(m, zero)

function test_unify(env, m, cs, num_s)
   local ss = unify(env, cs, name_generator())
   local n  = 0
   for s in ss do
      print("solution: " .. tostring(s:instantiate(m)))
      n = n + 1
   end
   if num_s ~= n then print("n: " .. n) end
   assert(num_s == n)
end

local env = get_env()

print("===============")
test_unify(env, m, { mk_eq_cnstr(proj1(m, one), proj1(zero, zero)) }, 1)
print("===============")
test_unify(env, m, { mk_eq_cnstr(proj1(m, one), proj1(zero, m)) }, 1)
*)
