variable f : Nat → Nat
variable g : Nat → Nat
variable a : Nat
axiom fid (x : Nat) : g x ≠ 0 → f x = x
add_rewrite fid
axiom gcnst (x : Nat) : g x = 1
add_rewrite gcnst

theorem one_neq_0 : 1 ≠ 0
:= Nat::succ_nz 0

add_rewrite one_neq_0

(*
local t = parse_lean("f a")
local r, pr = simplify(t)
print(r)
print(pr)
get_environment():type_check(pr)
*)