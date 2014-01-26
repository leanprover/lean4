rewrite_set simple
add_rewrite eq_id imp_truel imp_truer Nat::add_zeror : simple
variables a b : Nat
variable  f {A : Type} : A → Bool
axiom fNat (a : Nat) : f a = (a > 0)
add_rewrite fNat : simple

(*
local t = parse_lean('(∀ x : Nat, f x) ∧ (∀ x : Bool, f x)')
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
get_environment():type_check(pr)
*)
