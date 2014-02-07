variable vec    : Nat → Type
variable concat {n m : Nat} (v : vec n) (w : vec m) : vec (n + m)
infixl   65 ; : concat
axiom    concat_assoc {n1 n2 n3 : Nat} (v1 : vec n1) (v2 : vec n2) (v3 : vec n3) :
             (v1 ; v2) ; v3 = cast (to_heq (congr2 vec (symm (Nat::add_assoc n1 n2 n3))))
                              (v1 ; (v2 ; v3))
variable empty : vec 0
axiom    concat_empty {n : Nat} (v : vec n) :
             v ; empty = cast (to_heq (congr2 vec (symm (Nat::add_zeror n))))
                         v

rewrite_set simple
add_rewrite Nat::add_assoc Nat::add_zeror eq_id : simple
add_rewrite concat_assoc concat_empty Nat::add_assoc Nat::add_zeror : simple

(*
local opts = options({"simplifier", "heq"}, true)
local t = parse_lean('λ n : Nat, λ v : vec n, v ; empty')
local t2, pr = simplify(t, "simple", opts)
print(t2)
-- print(pr)
get_environment():type_check(pr)
*)

variable f {A : Type} : A → A

(*
local opts = options({"simplifier", "heq"}, true)
local t = parse_lean('λ n : Nat, λ v : vec (n + 0), (f v) ; empty')
local t2, pr = simplify(t, "simple", opts)
print(t2)
-- print(pr)
get_environment():type_check(pr)
*)

print ""

universe M >= 1
definition TypeM := (Type M)

variable lheq {A B : TypeM} : A → B → Bool
infixl 50 === : lheq
(*
local opts = options({"simplifier", "heq"}, true)
local t = parse_lean('λ val : Nat, (λ n : Nat, λ v : vec (n + 0), (f v) ; empty) val === (λ n : Nat, λ v : vec (n + 0), v) val')
print(t)
print("=====>")
local t2, pr = simplify(t, "simple", opts)
print(t2)
-- print(pr)
get_environment():type_check(pr)
*)
