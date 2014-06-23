local env     = environment()
local group   = Const("group")
local carrier = Const("carrier")
local real    = Const("real")
local nat     = Const("nat")
env = add_decl(env, mk_var_decl("group", mk_sort(2)))
env = add_decl(env, mk_var_decl("carrier", mk_arrow(group, Type)))
env = add_decl(env, mk_var_decl("real", Type))
env = add_decl(env, mk_var_decl("nat",  Type))
env = add_decl(env, mk_var_decl("real_group", group))
env = add_decl(env, mk_var_decl("nat_group", group))
local real_group = Const("real_group")
local nat_group  = Const("nat_group")
local m = mk_metavar("m", mk_metavar("m_ty", mk_sort(mk_meta_univ("u"))))
local cs  = {}
local tc  = type_checker(env, name_generator("foo"), function (c) print(c); cs[#cs+1] = c end)
assert(tc:is_def_eq(carrier(m), real))
local o   = options({"unifier", "use_exceptions"}, false)
print(o)
assert(not unify(env, cs, o)())

function hint(c, ngen)
   local lhs = c:lhs()
   local rhs = c:rhs()
   local j   = c:justification()
   if lhs:is_app() and lhs:fn() == carrier and lhs:arg():is_meta() then
      return
         {{ mk_eq_cnstr(lhs:arg(), nat_group, j) }, -- first possible solution
          { mk_eq_cnstr(lhs:arg(), real_group, j) }}
   else
      return nil
   end
end

function display_solutions(ss)
   local n = 0
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
end

display_solutions(unify(env, cs, hint, o))
