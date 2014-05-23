local NumThreads=4

function mod_name(midx)
   return tostring("mod5_mod" .. tostring(midx))
end

function const_name(midx)
   return "mod" .. tostring(midx) .. "C"
end

function mk_module(midx, imports)
   local imp_names = {}
   for i = 1, #imports do
      imp_names[#imp_names + 1] = mod_name(imports[i])
   end
   local env   = import_modules(imp_names, NumThreads)
   if #imports == 0 then
      env = add_decl(env, mk_var_decl(const_name(midx), Bool))
      env = add_decl(env, mk_var_decl("and", mk_arrow(Bool, Bool, Bool)))
   elseif #imports == 1 then
      env = add_decl(env, mk_definition(const_name(midx), Bool, Const(const_name(imports[1]))))
   else
      local And = Const("and")
      env = add_decl(env, mk_definition(const_name(midx), Bool, And(Const(const_name(imports[1])), Const(const_name(imports[2])))))
   end
   env:export(tostring(mod_name(midx)) .. ".olean")
end

local NumMods = 100

function mk_modules()
   mk_module(0, {})
   local i = 1
   local j = 1
   while i <= NumMods do
      if j % 2 == 0 then
         mk_module(i, {i-1, i-2})
         i = i + 1
      else
         mk_module(i,   {i-1})
         mk_module(i+1, {i-i})
         i = i + 2
      end
      j = j + 1
   end
end

mk_modules()
local env = import_modules(mod_name(NumMods))
env:for_each(function(d)
                print(d:name())
             end
)
for i = 1, NumMods do
   assert(env:get(const_name(i)):is_definition())
end
