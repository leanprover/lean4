variables a b c d e f p: Bool
rewrite_set simple
add_rewrite and_assoc and_comm and_left_comm : simple
(*
local t  = parse_lean("((f ∨ p) ∧ (e ∨ p)) ∧ ((p ∨ d) ∧ c) ∧ (b ∧ a)")
local t2 = simplify(t, "simple")
print(t)
print("====>")
print(t2)
*)
