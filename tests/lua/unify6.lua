local env = environment()
local m1  = mk_meta_univ("m1")
local m2  = mk_meta_univ("m2")
local m3  = mk_meta_univ("m3")
local l1  = mk_param_univ("l1")

function display_solutions(m, ss)
   local n = 0
   for s in ss do
      print("solution: " .. tostring(s:instantiate(m):normalize()))
      s:for_each_expr(function(n, v, j)
                         print("  " .. tostring(n) .. " := " .. tostring(v))
      end)
      s:for_each_level(function(n, v, j)
                          print("  " .. tostring(n) .. " := " .. tostring(v))
      end)
      n = n + 1
   end
end

cs = { mk_level_eq_cnstr(m1, max_univ(m2, max_univ(m2, l1, 1))),
       mk_level_eq_cnstr(m2, level()+1),
       mk_level_eq_cnstr(m3+1, m2+1)
     }

display_solutions(m1, unify(env, cs, name_generator()))
