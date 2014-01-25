rewrite_set simple
add_rewrite eq_id imp_truel imp_truer Nat::add_zeror : simple
variables a b : Nat
variable  f : (Nat → Nat) → Nat
(*
local t = parse_lean('λ x, a + 0 = 1 → x > f (λ y, y + a)')
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
get_environment():type_check(pr)
*)

(*
local t = parse_lean('λ x, a + 0 = 1 → x = 2 → x > f (λ y, y + a + x)')
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
get_environment():type_check(pr)
*)
