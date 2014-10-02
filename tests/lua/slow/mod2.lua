function mk_env(prefix, sz)
   prefix    = name(prefix)
   local env = environment()
   local A   = Local("A", mk_sort(0))
   local x   = Local("x", A)
   env = add_decl(env, mk_definition(name(prefix, "id"), Pi(A, mk_arrow(A, A)), Fun(A, x, x), {opaque=false}))
   env = add_decl(env, mk_constant_assumption(name(prefix, "P"), Prop))
   local P   = Const(name(prefix, "P"))
   local id  = Const(name(prefix, "id"))
   env = add_decl(env, mk_axiom(name(prefix, "Ax"), P))
   local Ax  = Const(name(prefix, "Ax"))
   for i = 1, sz do
      local pr = id(P, Ax)
      for j = 1, i do
         pr = id(P, pr)
      end
      local pr2 = id(P, pr)
      env = add_decl(env, mk_theorem(name(prefix, "T", i), P, pr))
   end
   return env
end

local mod_names = {}

function export_env(i, sz)
   local prefix = "mod" .. tostring(i)
   local mname  = "mod2_" .. prefix
   mod_names[#mod_names + 1] = mname
   mk_env(prefix, sz):export(mname .. ".olean")
end

local NumMods=40
local NumThs=150
for i = 1, NumMods do
   export_env(i, NumThs)
end

print("importing...")
local initt = os.clock()
local env2  = import_modules(mod_names, {num_threads=4, keep_proofs=true})
print(string.format("elapsed time: %.2f\n", os.clock() - initt))
for i = 1, NumMods do
   for j = 1, NumThs do
      assert(env2:get({"mod" .. tostring(i), "T", j}):is_theorem())
   end
end
