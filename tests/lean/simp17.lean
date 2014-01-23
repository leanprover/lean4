rewrite_set simple
add_rewrite and_truer and_truel and_falser and_falsel or_falsel Nat::add_zeror : simple
(*
  add_congr_theorem("simple", "and_congrr")
*)

variables a b c : Nat

(*
local t = parse_lean([[c + 0 ≠ b + 1 ∧ b = 0 ∧ c = 1]])
local s, pr = simplify(t, "simple")
print(s)
print(pr)
print(get_environment():type_check(pr))
*)