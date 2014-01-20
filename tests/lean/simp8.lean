variables a b c d e f : Nat
rewrite_set simple
add_rewrite Nat::add_assoc Nat::add_comm Nat::add_left_comm Nat::distributer Nat::distributel : simple
(*
local t  = parse_lean("f + (c + f + d) + (e * (a + c) + (d + a))")
local t2, pr = simplify(t, "simple")
print(t)
print("====>")
print(t2)
*)
