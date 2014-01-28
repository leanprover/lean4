rewrite_set NNF
add_rewrite not_not_eq not_true not_false not_neq not_and not_or not_iff not_implies not_forall
            not_exists forall_and_distribute exists_and_distributer exists_and_distributel : NNF

variable p : Nat → Nat → Bool
variable f : Nat → Nat
variable g : Nat → Nat → Nat

(*
local t1     = parse_lean('¬ ∀ x, (∃ y, p x y ∨ p (f x) (f y)) ∨ f 0 = 1')
local t2, pr = simplify(t1, "NNF")
print(t1)
print("====>")
print(t2)
get_environment():type_check(pr)
*)
