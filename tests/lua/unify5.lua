local env = environment()
env = add_decl(env, mk_constant_assumption("N", Type))
local N = Const("N")
env = add_decl(env, mk_constant_assumption("f", mk_arrow(N, N, N)))
env = add_decl(env, mk_constant_assumption("a", N))
env = add_decl(env, mk_constant_assumption("b", N))
local f  = Const("f")
local a  = Const("a")
local b  = Const("b")
local m1 = mk_metavar("m1", N)
local m2 = mk_metavar("m2", N)
local m3 = mk_metavar("m3", N)
local m4 = mk_metavar("m4", N)

function display_solutions(m, ss)
   local n = 0
   for s in ss do
      print("solution: " .. tostring(s:instantiate(m)))
      s:for_each_expr(function(n, v, j)
                         print("  " .. tostring(n) .. " := " .. tostring(v))
      end)
      s:for_each_level(function(n, v, j)
                          print("  " .. tostring(n) .. " := " .. tostring(v))
      end)
      n = n + 1
   end
end

cs = { mk_eq_cnstr(m1, f(m2, f(m3, m4))),
       mk_choice_cnstr(m2, function(m, e, s, ngen) return {{mk_eq_cnstr(m, a)}, {mk_eq_cnstr(m, f(a, a))}} end),
       mk_choice_cnstr(m3, function(m, e, s, ngen) return {mk_eq_cnstr(m, b), mk_eq_cnstr(m, f(b, b))} end),
       mk_choice_cnstr(m4, function(m, e, s, ngen) return {a, b} end)
     }

display_solutions(m1, unify(env, cs, name_generator()))
