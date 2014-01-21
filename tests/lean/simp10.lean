variable f : Nat → Nat
variable g : Nat → Nat
variable a : Nat
axiom fid (x : Nat) : g x ≠ 0 → f x = x
add_rewrite fid
axiom gcnst (x : Nat) : g x = 1
add_rewrite gcnst

(*
local t = parse_lean("f a")
local r, pr = simplify(t)
print(r)
print(pr)
get_environment():type_check(pr)
*)