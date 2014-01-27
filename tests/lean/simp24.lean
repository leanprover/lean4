rewrite_set simple
add_rewrite eq_id imp_truel imp_truer Nat::add_zeror : simple
variables a b : Nat
(*
local opts = options({"simplifier", "contextual"}, false)
local t = parse_lean('λ x, a = a → x = a')
local t2, pr = simplify(t, "simple", opts)
print(t2)
print(pr)
get_environment():type_check(pr)
*)

(*
local opts = options({"simplifier", "contextual"}, false)
local t = parse_lean('λ x, x = a → x = x')
local t2, pr = simplify(t, "simple", opts)
print(t2)
print(pr)
get_environment():type_check(pr)
*)

(*
local opts = options({"simplifier", "contextual"}, false)
local t = parse_lean('λ x, x = a + 0 → a = a')
local t2, pr = simplify(t, "simple", opts)
print(t2)
print(pr)
*)

(*
local t = parse_lean('λ x, a + 0 = 1 → x > a')
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
get_environment():type_check(pr)
*)
