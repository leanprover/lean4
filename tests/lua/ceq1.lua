local env  = get_environment()

function is_ceq(e)
   while e:is_pi() do
      _, _, e = e:fields()
   end
   return e:is_eq() or e:is_heq()
end

function show_ceqs(ceqs)
   for i = 1, #ceqs do
      print(ceqs[i][1], ceqs[i][2])
      env:type_check(ceqs[i][2])
      assert(is_ceq(ceqs[i][1]))
   end
end

function test_ceq(name, expected)
   local obj = env:find_object(name)
   local r   = to_ceqs(env, obj:get_type(), Const(name))
   show_ceqs(r)
   assert(#r == expected)
end

parse_lean_cmds([[
   import if_then_else
   variable f : Nat -> Nat
   axiom Ax1 : forall x : Nat, x > 0 -> f x < 0 /\ not (f x = 1)
   axiom Ax2 : forall x : Nat, x < 0 -> f (f x) = x
   variable g : Nat -> Nat -> Nat
   axiom Ax3 : forall x : Nat, not (x = 1) -> if (x < 0) then (g x x = 0) else (g x x < 0 /\ g x 0 = 1 /\ g 0 x = 2)
]])

test_ceq("Ax1", 2)
test_ceq("Ax2", 1)
test_ceq("Ax3", 4)

