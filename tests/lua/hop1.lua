import("util.lua")
local env = get_environment()
parse_lean_cmds([[
  axiom Ax1 {A : TypeU} (P Q : A -> Bool) : (forall x : A, P x /\ Q x) = ((forall x : A, P x) /\ (forall x : A, Q x))
  variable f : Nat -> Nat -> Nat
  variable p : Nat -> Bool
]], env)
local Ax1 = env:find_object("Ax1"):get_type()
function body(e)
   while (e:is_pi()) do
      local _, _, r = e:fields()
      e = r
   end
   return e
end
local p = body(Ax1):arg(2)
local t = parse_lean([[
    forall x : Nat, p (f x 0) /\ f (f x x) 1 >= 0
]], env)
r = hop_match(p, t)
assert(r)
assert(#r == 3)
local p, f, x, Nat = Consts("p, f, x, Nat")
assert(r[1] == Nat)
assert(r[2] == fun(x, Nat, p(f(x, nVal(0)))))
assert(r[3] == fun(x, Nat, Const({"Nat", "ge"})(f(f(x, x), nVal(1)), nVal(0))))
for i = 1, #r do
   print("#" .. tostring(i) .. " <--- " .. tostring(r[i]))
end
