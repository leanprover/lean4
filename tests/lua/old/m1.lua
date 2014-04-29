function body(e)
   while (e:is_pi()) do
      e = e:abst_body()
   end
   return e
end
function show_subst(r)
   for i = 1, #r do
      if r[i] then
         print("#" .. tostring(i) .. " <--- " .. tostring(r[i]))
      end
   end
end
local env = get_environment()
parse_lean_cmds([[
  variable f : Nat -> Nat -> Nat
  variable g : Nat -> Nat
  variable p : Nat -> Bool
  variables a b c : Nat
]])
local t = parse_lean([[fun x, (f (g a)) x]])
print(t)
local eta     = env:find_object("eta"):get_type()
local eta_lhs = body(eta):arg(2)
print(eta_lhs)
r = hop_match(eta_lhs, t)
print("r: " .. #r)
show_subst(r)
assert(r[3])
print(eta)
local r3_type = env:infer_type(r[3])
print(r3_type)
local eta3_type = eta:abst_body():abst_body():abst_domain()
print(eta3_type)
r2 = hop_match(eta3_type, r3_type)
show_subst(r2)
