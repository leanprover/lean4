rewrite_set simple
add_rewrite eq_id imp_truel imp_truer Nat::add_zeror : simple
(* add_congr_theorem("simple", "and_congrr") *)
variables a b : Nat
variables f : (Nat → Nat → Bool) → Bool

(*
local t = parse_lean('λ x, x = 1 ∧ f (λ y z, y + z > x)')
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
get_environment():type_check(pr)
*)
