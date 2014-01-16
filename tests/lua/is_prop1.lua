local env = get_environment()
assert(env:is_proposition(Const("true")))
assert(env:is_proposition(Const("false")))
assert(not env:is_proposition(nVal(0)))
assert(env:is_proposition(parse_lean([[forall x : Nat, x > 0]])))
parse_lean_cmds([[
   variable f : Nat -> Nat -> Nat
   variable p : Nat -> Bool
   variables a b c : Nat
   definition B := Bool
   variable q : B
]])
assert(env:is_proposition(parse_lean([[p (f a 0)]])))
assert(env:is_proposition(parse_lean([[p (f a 0) /\ a > 0]])))
assert(not env:is_proposition(parse_lean([[fun x, p (f x 0) /\ a > 0]])))
assert(env:is_proposition(parse_lean([[forall x : Bool, x]])))
assert(not env:is_proposition(parse_lean([[forall x : Nat, Nat]])))
assert(not env:is_proposition(parse_lean([[forall T : Type, T]])))
assert(env:is_proposition(parse_lean([[forall x y z, x /\ z /\ y]])))
assert(env:is_proposition(parse_lean([[true -> false]])))
assert(env:is_proposition(parse_lean([[Nat -> false]])))
assert(not env:is_proposition(parse_lean([[true -> Nat]])))
assert(not env:is_proposition(parse_lean([[Type]])))
assert(env:is_proposition(parse_lean([[0 = 1]])))
assert(env:is_proposition(parse_lean([[q]])))


