import heq
import tactic
add_rewrite Nat::add_assoc Nat::add_zeror

variable vec    : Nat → Type
variable concat {n m : Nat} (v : vec n) (w : vec m) : vec (n + m)
infixl   65 ; : concat
axiom    concat_assoc {n1 n2 n3 : Nat} (v1 : vec n1) (v2 : vec n2) (v3 : vec n3) :
             (v1 ; v2) ; v3 = cast (by simp)  (v1 ; (v2 ; v3))
variable empty : vec 0
axiom    concat_empty {n : Nat} (v : vec n) :
             v ; empty = cast (by simp) v

add_rewrite concat_assoc concat_empty

(*
local t = parse_lean('∀ (n : Nat) (v : vec (n + 0)) (w : vec n), v = w ; empty')
print(t)
local t2, pr = simplify(t)
print("====>")
print(t2)
get_environment():type_check(pr)
*)

print ""

(*
local t = parse_lean('λ n : Nat, ∃ (v : vec (n + 0)) (w : vec n), v ≠ w ; empty')
print(t)
local t2, pr = simplify(t)
print("====>")
print(t2)
get_environment():type_check(pr)
*)
