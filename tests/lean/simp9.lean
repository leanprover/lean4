variables a b c d e f : Nat
rewrite_set simple
add_rewrite Nat::mul_assoc Nat::mul_comm Nat::mul_left_comm Nat::add_assoc Nat::add_comm Nat::add_left_comm
            Nat::distributer Nat::distributel : simple
(*
local t      = parse_lean("(a + b) * (c + d) * (e + f) * (a + b) * (c + d) * (e + f)")
local t2, pr = simplify(t, "simple")
print(t)
*)
