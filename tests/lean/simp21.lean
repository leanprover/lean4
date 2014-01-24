variable vec    : Nat → Type
rewrite_set simple
add_rewrite Nat::add_assoc Nat::add_zeror eq_id : simple
variable n : Nat
(*
local t = parse_lean([[ vec n = vec (n + 0) ]])
print(t)
print("===>")
local t2, pr = simplify(t, "simple")
print(t2)
print(pr)
*)