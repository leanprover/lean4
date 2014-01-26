import cast
variable vec    : Nat → Type
variable concat {n m : Nat} (v : vec n) (w : vec m) : vec (n + m)
infixl   65 ; : concat
axiom    concat_assoc {n1 n2 n3 : Nat} (v1 : vec n1) (v2 : vec n2) (v3 : vec n3) :
             (v1 ; v2) ; v3 = cast (congr2 vec (symm (Nat::add_assoc n1 n2 n3)))
                              (v1 ; (v2 ; v3))
variable empty : vec 0
axiom    concat_empty {n : Nat} (v : vec n) :
             v ; empty = cast (congr2 vec (symm (Nat::add_zeror n)))
                         v

rewrite_set simple
add_rewrite Nat::add_assoc Nat::add_zeror eq_id : simple
add_rewrite concat_assoc concat_empty Nat::add_assoc Nat::add_zeror : simple

(*
local t = parse_lean('∀ (n : Nat) (v : vec (n + 0)) (w : vec n), v = w ; empty')
print(t)
local t2, pr = simplify(t, "simple")
print("====>")
print(t2)
get_environment():type_check(pr)
*)

print ""

(*
local t = parse_lean('λ n : Nat, ∃ (v : vec (n + 0)) (w : vec n), v ≠ w ; empty')
print(t)
local t2, pr = simplify(t, "simple")
print("====>")
print(t2)
get_environment():type_check(pr)
*)
