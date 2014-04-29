local env  = get_environment()
assert(env:find_object("neq_elim"))

function show_ceqs(ceqs)
   for i = 1, #ceqs do
      print(ceqs[i][1], ceqs[i][2], is_permutation_ceq(ceqs[i][1]))
      env:type_check(ceqs[i][2])
      assert(is_ceq(env, nil, ceqs[i][1]))
   end
end

function test_ceq(name, expected, is_perm)
   local obj = env:find_object(name)
   local r   = to_ceqs(env, nil, obj:get_type(), Const(name))
   show_ceqs(r)
   assert(#r == expected)
   if is_perm ~= nil then
      for i = 1, #r do
         assert(is_permutation_ceq(r[i][1]) == is_perm)
      end
   end
end

parse_lean_cmds([[
   variable f : Nat -> Nat
   axiom Ax1 : forall x : Nat, x > 0 -> f x < 0 /\ not (f x = 1)
   axiom Ax2 : forall x : Nat, x < 0 -> f (f x) = x
   variable g : Nat -> Nat -> Nat
   axiom Ax3 : forall x : Nat, not (x = 1) -> if (x < 0) then (g x x = 0) else (g x x < 0 /\ g x 0 = 1 /\ g 0 x = 2)
   axiom Ax4 : forall x y : Nat, f x = x
   axiom Ax5 : forall x y : Nat, f x = y /\ g x y = x
   axiom Ax6 : forall x : Nat, f x ≠ 0
]])

test_ceq("Ax1", 2)
test_ceq("Ax2", 1)
test_ceq("Ax3", 4)
test_ceq("Ax4", 0)
test_ceq("Ax5", 1)
test_ceq("Ax6", 1)
test_ceq("eta", 1)
test_ceq("not_not_eq", 1,    false)
test_ceq("or_comm", 1,       true)
test_ceq("or_assoc", 1,      false)
test_ceq("or_id", 1,         false)
test_ceq("or_falsel", 1,     false)
test_ceq("or_falser", 1,     false)
test_ceq("or_truel", 1,      false)
test_ceq("or_truer", 1,      false)
test_ceq("or_tauto", 1,      false)
test_ceq("and_comm", 1,      true)
test_ceq("and_assoc", 1,     false)
test_ceq("and_id", 1,        false)
test_ceq("and_falsel", 1,    false)
test_ceq("and_falser", 1,    false)
test_ceq("and_truel", 1,     false)
test_ceq("and_truer", 1,     false)
test_ceq("and_absurd", 1,    false)
test_ceq("imp_truer", 1,     false)
test_ceq("imp_truel", 1,     false)
test_ceq("imp_falser", 1,    false)
test_ceq("imp_falsel", 1,    false)
test_ceq("not_and", 1,       false)
test_ceq("not_or", 1,        false)
test_ceq("not_iff", 1,       false)
test_ceq("not_implies", 1,   false)
test_ceq("or_left_comm", 1,  true)
test_ceq("and_left_comm", 1, true)
test_ceq("forall_or_distributer", 1,  false)
test_ceq("forall_or_distributel", 1,  false)
test_ceq("forall_and_distribute", 1,  false)
test_ceq("exists_and_distributer", 1, false)
test_ceq("exists_and_distributel", 1, false)
test_ceq("exists_or_distribute", 1,   false)
test_ceq({"Nat", "add_zeror"}, 1,     false)
test_ceq({"Nat", "add_zerol"}, 1,     false)
test_ceq({"Nat", "add_comm"}, 1 ,     true)
test_ceq({"Nat", "add_assoc"}, 1,     false)
test_ceq({"Nat", "mul_zerol"}, 1,     false)
test_ceq({"Nat", "mul_zeror"}, 1,     false)
test_ceq({"Nat", "mul_onel"}, 1,      false)
test_ceq({"Nat", "mul_oner"}, 1,      false)
test_ceq({"Nat", "mul_comm"}, 1,      true)
test_ceq({"Nat", "mul_assoc"}, 1,     false)
test_ceq({"Nat", "add_comm"}, 1,      true)
test_ceq({"Nat", "add_assoc"}, 1,     false)
test_ceq({"Nat", "distributer"}, 1,   false)
test_ceq({"Nat", "distributel"}, 1,   false)
test_ceq({"Nat", "le_refl"}, 1,       false)
test_ceq({"Nat", "le_zero"}, 1,       false)
test_ceq({"Nat", "not_lt_0"}, 1,      false)
test_ceq({"Nat", "lt_nrefl"}, 1,      false)
