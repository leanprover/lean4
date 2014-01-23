rewrite_set simple
add_rewrite and_truer and_truel and_falser and_falsel or_falsel : simple
(*
  add_congr_theorem("simple", "and_congr")
  add_congr_theorem("simple", "or_congr")
*)

variables a b c : Nat

(*
local t = parse_lean([[a = 1 ∧ ((¬ b = 0 ∨ c ≠ b) ∨ b + c > a)]])
local s, pr = simplify(t, "simple")
print(s)
print(pr)
print(get_environment():type_check(pr))
*)