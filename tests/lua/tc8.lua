local env = environment()
local N   = Const("N")
env = add_decl(env, mk_constant_assumption("N", Type))
env = add_decl(env, mk_constant_assumption("f", mk_arrow(N, N)))
env = add_decl(env, mk_constant_assumption("a", N))
local f = Const("f")
local a = Const("a")
local m1   = mk_metavar("m1", mk_metavar("m2", mk_sort(mk_meta_univ("l"))))
local ngen = name_generator("tst")
local tc   = type_checker(env, ngen)

function test_check(e)
   t, cs = tc:check(e)
   print(tostring(e) .. " : " .. tostring(t))
   cs = cs:linearize()
   for i = 1, #cs do
      print(" >> " .. tostring(cs[i]))
   end
end

test_check(f(m1))
test_check(f(f(m1)))
test_check(f(m1))
