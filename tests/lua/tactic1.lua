local ps   = proof_state()
local env  = environment()
local Bool = Const("Bool")
env:add_var("p", Bool)
env:add_var("q", Bool)
local p, q = Consts("p, q")
local ctx  = context()
ctx = ctx:extend("H1", p)
ctx = ctx:extend("H2", q)
ps  = to_proof_state(env, ctx, p)
local ios = io_state()
print(ps)
local ltac = tactic(function(env, ios, s)
                       print("FIRST tactic in Lua, current state: " .. tostring(s));
                       return s
end)
local t = (trace_tactic("hello") .. trace_tactic("world")) + (trace_tactic("again") .. ltac .. assumption_tactic())
for s in t(env, ios, ps) do
   if s:is_proof_final_state() then
      local m = proof_map()
      local a = assignment(s:get_menv())
      print(s:proof_builder()(m, a))
   else
      print(s)
   end
end
print("-------------------")
print(t:solve(env, ios, ps))
print(t:solve(env, ios, ctx, p))
assert(t:solve(env, ios, ps) == Var(1))
assert(t:solve(env, ios, ctx, q) == Var(0))
local t2 = id_tactic() + id_tactic() + id_tactic()
local r  = t2:solve(env, ios, ps)
assert(#r == 3)
for i, out_state in ipairs(r) do
   print(i, out_state)
end
