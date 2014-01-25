import   cast
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
add_rewrite concat_assoc concat_empty Nat::add_assoc Nat::add_zeror and_truer eq_id : simple

variable n : Nat
variable v : vec n
variable w : vec n
variable f {A : TypeM} : A → A
variable p {A : TypeM} : A → Bool
axiom fax {n m : Nat} (v : vec n) (w : vec m) : f (v; (w; v)) = v; (w; v)
add_rewrite fax : simple

(*
local t = parse_lean([[ p (f ((v ; w) ; empty ; (v ; empty))) ∧ v = cast (congr2 vec (Nat::add_zeror n)) (v ; empty) ]])
print(t)
print("===>")
local t2, pr = simplify(t, "simple")
print(t2)
print("checking proof")
print (get_environment():type_check(pr))
*)
