add_rewrite_rules({"Nat", "add_zerol"})
add_rewrite_rules({"Nat", "add_zeror"})
parse_lean_cmds([[
  variable f : Nat -> Nat -> Nat
  variable g : Nat -> Nat
  variable b : Nat
  definition a := 1
  theorem a_eq_1 : a = 1
  := refl a
  definition c := 1
  set_opaque a true

  axiom f_id (x : Nat) : f x 1 = 2*x

  axiom g_g_x (x : Nat) : (not (x = 0)) -> g (g x) = 0
]])
add_rewrite_rules("a_eq_1")
add_rewrite_rules("f_id")
add_rewrite_rules("eq_id")

-- set_option({"lean", "pp", "implicit"}, true)
e, pr = simplify(parse_lean('fun x, f (f x (0 + a)) (g (b + 0))'))
print(e)
print(pr)
local env = get_environment()
print(env:type_check(pr))

e, pr = simplify(parse_lean('forall x, let d := a + 1 in f x a >= d'))
print(e)
print(pr)
local env = get_environment()
print(env:type_check(pr))

e, pr = simplify(parse_lean('(fun x, f (f x (0 + a)) (g (b + 0))) b'))
print(e)
print(pr)
local env = get_environment()
print(env:type_check(pr))

e, pr = simplify(parse_lean('(fun x y, f x y) = f'))
print(e)
print(pr)
local env = get_environment()
print(env:type_check(pr))
