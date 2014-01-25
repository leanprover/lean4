rewrite_set simple
add_rewrite eq_id imp_truel imp_truer Nat::add_zeror : simple
variables a b : Nat
variable  f : (Nat → Nat) → Nat
variable  g : Nat → Nat

(*
local t = parse_lean('λ x x2, (∀ y, g y = x) → g (a + x + b) > x2 + g x')
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
get_environment():type_check(pr)
*)
