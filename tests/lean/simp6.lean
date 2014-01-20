variables a b : Nat
rewrite_set simple
add_rewrite Nat::add_comm eq_id : simple

(*
local t = parse_lean("a + b = b + a")
print(simplify(t, 'simple'))
*)